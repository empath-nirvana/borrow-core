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

## 0. Summary

- **What is lost, and where** (§1). The frontend decides each construct's shape and then emits a
  kernel term chosen for the proofs: a `ν` machine per div body, a handler site with a captured
  `κ` per `for` over a generator, a state-passing closure per stateful handler, a copy per site.
  The checker checks that term, the erasure drops its types, and the backend compiles the erasure.
  Of the 31 places in §1.2 where a later stage reconstructs or never gets what an earlier one
  knew, four groups matter:
  - **choices of the elaborator, recovered by searching user code** (A1–A11): the clause kind
    (`tailClause?`), the clauses at a site (`clausesAt`), loops (the §14 machine, then #540's
    partial evaluator), the consumer of a loop, copies of one body, the handler's state;
  - **checked facts the erasure drops** (B1–B6): rows, types, the qualifier tags (`Convert`
    discards them), the effect context (it reaches `Driver` and is never read);
  - **recognisers of fixed schemes** (C1–C7), which are exact and stay;
  - **re-derivations inside the frontend** (D1–D7), among them the string templates that build
    the schemes.
- **The principle** (§1.4). Recognising a fixed scheme, whose shape does not depend on the
  program, is exact. Recognising a property of user code is a search. Such a property should come
  from where it was decided.
- **Routes** (§2). G where the fact is a typing fact with a law: keep the qualifier, pass the
  checked effect context on, classify clause forms where they are checked, and #216's clause
  multiplicity as its own grade. M where the fact is about shape or about the elaboration's
  choices: one typed structured IR computes them, and a table carries them beside the checked term.
  Recovery is kept for fixed schemes and for input with no frontend (kernel programs). Three of
  the issue's four G candidates fail *laws first* as kernel grades (§2.2): tail position is not a
  count; totality is already a type; a reification mode as a kernel former would be a value-type
  former with borrow consequences and no new program.
- **The recommended pipeline** (§3).
  - The compiled code still comes from the checked term.
  - A typed structured IR (typed-elaboration's TIR moved to the surface, with U1's loop node and
    the effects pass's sites) produces both the kernel term and a **fact table**.
  - The erasure keeps static names (as now), the qualifier tags, a span per node and the checked
    effect context.
  - The backend **verifies** each table entry by re-deriving its scheme and comparing it with the
    erasure. A mismatch is an internal error. Then it lowers by the entry.
  - State machines are built at the lowering, and only at a reified loop value or a stored `κ`.
    Under OQ-15's decided reading of divergence (codata), the meaning of a div body is still a
    machine.
- **No new kernel former or grade** in the recommended path, and no change to FP, adequacy or
  `total_every_run` (§4). #216 is a grade with its own law and its own unit.
- **The larger option** (§4.4): divergence written in direct style, a loop effect whose only
  reification is explicit. It would delete the frontend's machine and put loops under
  effect-lowering's classification. It revises a recorded decision (OQ-15 (a), decision 35), so
  it is the user's to reopen. It is reported, not recommended.
- **Units** (§3.6). #541's units 1, 3–8 and loops U1–U4 are kept. Effect-lowering unit 9 (the
  site table) is promoted to the channel and moves before unit 3. #540's narrowing and `poison`
  padding are kept. Its recovery of loops is replaced by construction from loop entries (§3.5).
  Four new units, N1–N4.
- **No algebra hard stop** in the recommended path (§9). Three defects (§9.2): the qualifier
  dropped at conversion; elaboration schemes that are strings, about which the planned units
  cannot state their laws; the frontend's lowering report, which is not the lowering.

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
| B3 | the qualifier `lin`/`aff`/`unr` | discarded at conversion (`Convert.lean:737–739`); `κ`'s cancel arm built for every qualifier (`kapBody`, `Capture.lean:259–266`) | the term: `hnd (n, (qs, H))` | — |
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
  continuation (affine) as the rest`, at elaboration, before any backend pass.

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

- **G (typed and checked).** The fact is a typing fact: a type, or a form the checker checks,
  with a law it must satisfy. It is carried because the checker has it. A new grade is admitted
  only when its equational theory is stated first.
- **M (structured IR and table).** The fact is about the program's shape, or about which scheme
  the elaborator chose. It is computed once, on a typed structured IR, carried in a table beside
  the checked term, and verified against that term.
- **R (recovery kept).** The fact is a fixed scheme (§1.4), or a whole-program analysis with no
  better source, or the input has no frontend (the kernel programs of `Backend/Kernel.lean`, and
  hand-written core).

### 2.2 The G candidates of #552, judged

| candidate | the law it would have to satisfy | verdict |
|---|---|---|
| **The qualifier, refined: "exactly once on every path, in tail"** | `tail_resumes` (`Core/Handlers.lean`): a clause whose every path ends in one resume equals its resume-removed body followed by one resume | **Not a grade.** A grade counts uses and composes under sequencing. Tail position does not: `M; k y` is tail and `k y; M` is not, with the same count. The precise typing statement is parametricity in the answer type (a clause natural in `R` must call `κ` once, last). The kernel has no type `∀` (decision 8). **Carried as a clause form** instead: the elaborator emits the tail clause in one fixed scheme; the checker or the backend classifies it exactly (§3.4). |
| **"0" for abortive branches** | `catch_abort`, `abort_absorbs` | **Already in the kernel.** An abortive operation's answer is `0` at a qualifier with weakening, and its clause gets no `κ` (SPEC §19 `[raise]`). The erasure keeps it (`raise` against `perform`, B4). |
| **#216: clause multiplicity** | a clause of an abortive operation runs at most once per handler instance, since the first abort ends the handled computation (`catch_abort`; `hnd` is consumed); a clause of a resuming operation runs once per `perform`, any number of times | **A real grade, admitted.** It is a function of what `[handle]` already has (each operation's qualifier and answer type), so the erasure needs nothing new. It changes what types (`default(d)` with an owned `d`), not what the backend recovers. Its own unit, §4.1. |
| **Totality, or div, as a grade on loops and calls** | `total_every_run` | **Already a type.** A total function is `U(A ⊸ F B)`, a div one `U(A ⊸ F(U(Loop B R)))` (SPEC §14). A counted loop's step is `!(I32 ⊗ S ⇒ S ⊕ E)`, so a loop classified total that is not cannot pass the checker. The per-form split (D1) is the inference being syntactic. Loops U2's class pass on the typed tree is the inference. A separate grade would state the same fact twice. A *row entry* for div is §4.4's option. |
| **Static handler sites in the row** | static per-site names (law 3) | **Kept already** (#521): the name is a literal in `perform` and `hnd` (B5). What is lost is the per-site *handler* facts (A1–A6), which travel with the effect context and the table (§3.3). No former. |
| **A suspension or "may reify" mode** | complete-drive: a loop value observed only by its enclosing machine, up to a root the runtime drives to the end, has no observable turn boundaries (SPEC §14 *The outermost handler*; `docs/effect-lowering.md` §2.7) | **As a kernel mode: rejected.** It would be a second-class thunk, as System C's unboxed blocks: a value-type former (about 100 match arms, CLAUDE.md *Growth discipline*), with rules for what may capture it, which is a borrow-calculus change, and no program it newly types. Justified by the lowering alone, it fails *laws first*. **As a fact of the structured IR: accepted (M).** The frontend already decides it by the expected type (direct-style call against loop as value; `for` over `g(e)` against stored generator; BOXED-κ's `boxK`). |
| (added) **Types to the backend** | none: they are read off the derivation | **G, later (H3 of effect-lowering §3.1).** It removes B1, B2 and the retry. It is the largest change of all, so it comes after the table (§3.3, option C3). |

### 2.3 The routes, per fact

| fact (§1.2) | route | why |
|---|---|---|
| A1, A2 clause kind (tail, resume or cancel) | **G**: one fixed scheme per kind, classified exactly | a checkable form with a law: `tail_resumes`; `kappa_cancel_steps` for resume or cancel |
| A3 stored `κ` | **G**, the same classification | `Capture` builds the machine, as now |
| A4 the clause code at a site | **M**: the table names the clause's code (a closed `!` value, emitted as a definition of its own) | which code is shape, not type. With the name, a direct call needs no flow |
| "names the clause performs are unhandled in `K`" (effect-lowering §2.3, condition 2) | **M**, a static check over names and the call graph | not local to `[handle]`: a re-entered site can be inside `K` and still typed. Static names make it decidable |
| A5 handler state | **G**: the state's type, in the effect context | the declared parameter type; its law (state-passing equals a cell) is unit 3's |
| A6 copies of one body, A7 drained by one `for` | **M** | facts about the elaboration and about instances |
| A8 the codata scheme | **R** | a fixed scheme |
| A9 loops, A10 their consumer | **M**: a loop entry per body machine, a mode per call | under OQ-15 (a) the meaning stays a machine. The mode is decided by expected types, a typed-elaboration fact |
| A11 lets at several rows | **R** now, **G** with types (C3) | works, at a second conversion |
| B1 rows, B2 types | **R** now, **G** with C3 | the least solution is sound and cheap. C3 removes it and the retry |
| B3 the qualifier | **G**: keep `qs` through `Convert` | already in the checked term |
| B6 the effect context | **G**: hand `Checked.sigs` to the backend, and extend it per name with clause kinds and the state's type | the checker built it |
| C1–C7 | **R** | fixed schemes |
| D1, D7 a body loops | **G** via loops U2's class pass | an inference on types, validated by the checker |
| D2 a body's operations | **M**: read from the effects pass's rows | — |
| D3 `return`'s type | **M** (loops U3) | — |
| D4 types of the program | the TIR on the surface, as `docs/typed-elaboration.md` §1.1 planned | it is the structured IR (§3.2) |
| D5 the report | rendered from the table | one source for the report and the lowering |
| D6 string templates | typed schemes, Lean functions that build core (N1) | the laws the units owe must be stated over them |

## 3. The resulting pipeline

### 3.1 The stages

    parse
    effects             sites, instances, copies (Effects.lean, as now)
    structured IR       the typed surface tree (§3.2): loops (U1's node), sites with
                        clause kinds, calls with their mode, types and rows
      ├─ kernel terms   typed schemes (N1): today's elaboration, unchanged output
      └─ fact table     per site name: kinds, clause code, state type, copy group;
                        per loop node: its scheme's parameters, its points, its mode
    check               Checked: e, sigs (+ kinds per name), pins
    erasure             e, plus a span per node (C2); qs kept
    backend
      verify            each entry: re-derive the scheme, compare with the erasure
      convert, poly     qs kept through Convert
      classify          sites from the table (no search); table-less input by today's recovery
      lower, no κ       direct calls (named clause code), native handler state,
                        resume or cancel in place (units 3, 4)
      loops             body machines with a complete root as native loops (N4)
      capture           state machines: reified loop values and stored κ only
      unwind, collapse, types, flow, flat (+ #540's narrowing, poison padding)

### 3.2 The structured IR

It is not a new language. It is the surface tree after the effects pass, typed, which is
`docs/typed-elaboration.md` §1.1's TIR placed where that design put it ("one node per surface
construct", "the summaries lowering needs: the node's effect"), and which `Pipeline.lean:9–13`
still lists as the plan. Its nodes:

- **`loop ℓ (src) { M } else D; N`**: U1's node (#548, in progress), with the class of loops U2 and
  the live variables per edge of U3;
- **a site**: `forSite`/`pullSite`/`with`, its static name, and per operation the clause's kind,
  decided where the clause is written:
  - *tail*: every path of the clause ends in its resume. A `for` body with no `break` or `return`
    is one;
  - *resume or cancel*: each path resumes or cancels;
  - *stored*: the clause keeps `κ`;
  - *abortive*: no `κ`;
- **a call**: *direct-style* (its loop is observed by the enclosing machine) or *value* (the loop
  escapes), by the expected type (SPEC §14);
- types and rows on every node, from the typed elaboration's own inference (`TCx.tyV`,
  `Instances.table`).

Push stages (effect-lowering unit 7) are rewrites on this IR: the adapter's instance and its
argument are both nodes there.

### 3.3 The channel: what the erasure keeps

| option | how | for | against |
|---|---|---|---|
| C1: marks in the checked term | a dead binding of a literal, `let _ = (i64 magic, i32 id)`, at each scheme's root; typed by existing rules, a β-step of meaning | survives `polyLets`' duplication; no change to the erasure | magic numbers in checked core; one machine step per mark in the source interpreter |
| **C2: a span per node** (recommended) | the erasure returns `Expr` and an array of each node's core span; `prepare`'s rewrites carry it; entries are keyed by span and by static name | no change to the checked term; the same array gives the native target its source locations (#532's debug info) | `prepare`'s five rewrites each carry the array; generated code shares its sugar's span, so an entry names its scheme's head shape too |
| C3: a typed erasure | the checker emits each node's type with it | removes B1, B2, A11 and the retry | every backend pass carries types; the largest change |

**Recommendation: C2 now, C3 later on the same array.** Keep `qs` through `Convert` (B3) and pass
`Checked.sigs` to the backend (B6) in the same unit.

### 3.4 Verify, then lower

- **Every entry is checked against the term it describes.** The entry names a scheme and its
  parameters. The backend applies the scheme function (N1) to the parameters, erases the result,
  and compares it with the erased subterm at the entry's key. This is structural equality, not a
  search. It is the method of `Frontend/Check/CrossCheck.lean`, which compares erasures.
- **A mismatch is an internal error**, and the gate fails. There is no silent fallback to a
  generic path: a silent fallback is how chain-yield's machine went unnoticed.
- **Clause kinds** can be classified by the checker itself. `[handle]`'s builder sees each
  clause value, and the scheme is fixed, so the classification is exact. It goes in
  `Checked`, beside `pins` (option K1, §8). The other entries are whole-program facts (copies,
  condition 2, a loop's root) and are verified in the backend (K2).
- **Input with no table** (kernel programs, hand-written core in the corpus) takes the generic
  path, whose recognisers (A1, A4) then produce the same table. Their counts are pinned
  (`corpus/kernel-counts.expected`: `tick-native 0 0 0`), so those recognisers stay, as the
  table's second producer and no longer as the decision for elaborated programs.

### 3.5 Where state machines are built

- **The meaning.** Under OQ-15's decided reading (`docs/effects-state/05a-open-questions-1-34.md`,
  OQ-15: codata, (a)), a div body's kernel term is a `ν` machine. The kernel has no other loop for
  a computation that may not end. So "late" means at the lowering.
- **The lowering.** From each root the runtime drives to the end (`main`), the backend follows
  direct-style calls through their loop entries. Each body machine reached that way is lowered
  natively:
  - each point is a block, and each skip to a point a jump;
  - a point holding a callee's loop is a call of the callee's native loop;
  - a finish is a return.

  It needs no budget and no search: the entry lists the points.
- **A machine is kept** only at a reified loop value (an argument of `div_fuel`, an annotated
  loop binding, a stored generator), at a stored `κ` (stored generator sites, BOXED-κ, task
  queues), and at what forwards through them. `Capture` builds those, after the direct
  lowerings, as effect-lowering §3 orders.
- **Under `div_fuel`** the count of observations is the meaning, so a loop reached from a
  reified value keeps its machine (effect-lowering §2.8). A function called both from `main` and
  under `div_fuel` gets two lowerings. Code size is not a goal.
- The law that makes this the meaning's lowering is §4.2's *complete drive*.

### 3.6 Units, kept, collapsed or replaced

| unit | verdict | how |
|---|---|---|
| effect-lowering 1 (#544, merged) | kept | `tailClause?` stays as the table's producer for table-less input, and becomes the exact check of the tail scheme |
| 2 (#540, running) | narrowing, `poison` padding and dead-word removal **kept**; loop recovery **replaced** | the padding and narrowing serve every real machine and sum. Specialising `drive` back into loops is replaced by N4's construction. A pass bounded by budgets is an optimiser (effect-lowering §3.4); N4 has no bound. Let #540 finish its brief and land on its acceptance. Its loop recovery is then interim |
| 3 classify, then lower before `Capture`; native handler state | kept | classifies from the table and `Checked`, not by search; the state's type from the effect context |
| 4 resume or cancel in place | kept | the kind comes from the table; the split point is the scheme's |
| 5 one code per codata value; copies merged | kept | copy groups and the non-nesting verdict come from the table |
| 6 specialisation S1 | kept | backend |
| 7 push stages | kept, **moved** onto the structured IR | the equation is stated over the scheme |
| 8 abortive pass-through, loop exit | kept | backend; with C3 the re-injection is the identity by type |
| 9 H1 site table | **promoted**: it becomes N3, before 3 | it is the channel |
| loops U1 (#548, running) | kept | its loop node is the structured IR's |
| U2 (#549) | kept | the class pass is the IR's fact. Its counted machine loops are machines of the meaning, lowered natively by N4 |
| U3 (#550), U4 (#551) | kept | edges, join points and labels are IR facts; U4's moves between machine points become jumps in N4 |
| U5 (#58) | independent | — |

New units, N1 to N4:

| # | unit | needs | acceptance |
|---|---|---|---|
| N1 | **Typed schemes.** The string templates of the schemes later units prove laws over (§14's machine, `forData`, `forYield`, `pullView`) as Lean functions that build core | — | `bcc desugar` byte-identical on every corpus and `experiments/` program |
| N2 | **The channel.** C2's span array through `prepare`; `qs` kept through `Convert`; `Checked.sigs` to the backend | — | every WAT and `.ll` byte-identical |
| N3 | **The site table** (unit 9 promoted). Per name: kinds, the clause's code, the state's type, the copy group, condition 2; verified (§3.4); `bcc check`'s `lowering` lines rendered from it | N1, N2 | `tailResumptive`'s decisions identical on the corpus, now from the table; `for-yield-branch`'s three sites reported as tail, tail, resume or cancel |
| N4 | **Loops by construction.** Loop entries and call modes; native lowering from complete roots (§3.5); `bcc-counts --sites` counts the machines still driven at a complete consumer | N2, U2 | that count 0 on the corpus and `bench/`; sieve ≤ 1.4×; with unit 1, chain-yield ≤ 1.2× |

**Order.** U1 (running) → N1 and N2 (independent of each other) → N3 → effect-lowering units 3,
4 and 5 → U2 → N4 → U3, U4 → unit 7. #540 lands when it meets its own acceptance. N1 touches the
schemes U2–U4 edit: §8 choice 5.

## 4. Laws and proofs

### 4.1 G

- **Keeping `qs`, passing the effect context on.** No law and no proof: both are in the checked
  artifact already.
- **Clause kinds.** Each kind's lowering rests on a law the kernel already has:
  - tail: `tail_resumes`, `op_tail`;
  - abortive: `catch_abort`, `abort_absorbs`, `then_fin`, `unwind_prefix`;
  - resume or cancel: `kappa_resume_steps`, `kappa_cancel_steps`, `cancel_prefix`;
  - stored: H-op with `κ` as a value.

  Classifying a fixed scheme adds no typing rule. The state-passing equation (A5) and resume or
  cancel in place are units 3 and 4's hypotheses (effect-lowering §2.3–§2.4), stated over N1's
  schemes.
- **#216, clause multiplicity.**
  - *Grades*: `{1, ω}` per clause, from the operation's qualifier and answer type: an abortive
    operation's clause is graded 1, a resuming one's ω. A linear grade has no clause shape yet
    (#216's table).
  - *Typing*: `[handle]`'s premise "`H` over a part of the context whose live slots are
    persistent" (SPEC §19, *As built*) becomes "whose live slots are persistent where the clause
    is graded ω, and drop where it is graded 1".
  - *Law*: a clause graded 1 runs at most once per instance of its handler. By `catch_abort`, and
    since the handled computation is gone after it.
  - *Proofs*: `handle_compatC`'s abortive case with an affine environment for the clause. The
    clauses' environment that does not run is dropped by the handler's return path, which needs
    `[then]`'s drop glue at the site. FP and adequacy keep their statements, and so does
    `total_every_run`.
  - *Borrows*: a captured borrow must outlive the site, as any capture. No borrow-calculus change.
  - *Lowering*: a move in a branch (#216).

  Its own unit, after N3. It does not touch recovery.

### 4.2 M: the agreement check

- **Per node, on every compile** (§3.4): the scheme re-derived from the entry equals the erased
  term. This is exact, and it covers every program, not only the corpus.
- **Per scheme, once, in Lean**: the special lowering of a scheme has the generic lowering's
  observations under the entry's condition. Each is a law some planned unit already owes:

  | scheme | law | status |
  |---|---|---|
  | tail clause | `tail_resumes` | proved (#547) |
  | native handler state | state-passing equals threading a cell, at `lin`/`aff` | unit 3, hypothesis |
  | resume or cancel in place | the cancel unwinds `K` innermost first with `⊥`'s semantics | unit 4, hypothesis |
  | push stage | pull and push agree when the drain is driven to the end | unit 7, hypothesis |
  | counted fold and machine | agree when the machine is driven to the end | loops U2, hypothesis |
  | exits across levels | the first `up e` is the answer | loops U4, hypothesis |
  | **complete drive** (new, N4) | a body machine driven to the end by a complete driver performs the same steps, in order, as its native lowering. The observation boundaries are skips of no effect | hypothesis, by induction on the run of the step, from `unfold`'s β (`nu_out (nu_in t) = t`) |

  Each law is stated over N1's scheme function, so the scheme the check compares and the scheme
  the law is about are one definition. Today's string templates do not allow that (§9.2).
- **Differential, on the corpus**: the stages' interpreters against the goldens, as today.
- **Strength.** For borrow guarantees this is today's strength. The compiled code is a function
  of the checked term, and the entry only selects among lowerings whose agreement is a law. The
  rejected alternative, compiling from the structured IR directly (Lean's `partial` and
  `implemented_by`, §5), would compile code the checker never saw. Every program's borrow
  guarantee would then rest on the per-scheme laws alone.

### 4.3 What the existing proofs need

In the recommended path: nothing. No `CDerives` rule, relation clause, machine step or type
former is added. FP, adequacy and `total_every_run` keep their statements. #216 changes one
premise and one compatibility case (§4.1).

### 4.4 The option not recommended: divergence in direct style

**What.** A library effect, say `Div` with one linear operation `tick() -> Next` (`Next` is
`next` or `close`), is performed at each point where today's machine skips. A `while` becomes a
kernel loop at the row `Div`: one primitive, with a machine step like `count_try`'s. A loop value
is `reify` of a computation at that row, built where a value is expected. Then:

- the frontend's machine (`mWalk`, `mAssemble`, `divMachine`, `Sugar.lean:957–1527`),
  `div_bind` and `div_defer` are deleted;
- totality is the row without `Div`;
- §14's specialisation at a callback's computation type becomes row polymorphism, which the
  kernel has (decision 62);
- every loop falls under effect-lowering's classification:
  - the runtime's handler of `tick` resumes in tail: a direct call, so a native loop;
  - `div_fuel` resumes `n` times, then closes: resume or close in place;
  - a stored generator keeps `κ`: a state machine.

It is #552's "totality as an effect" and "may reify" in one mechanism.

**Unknowns** (unknowns first: a spike before any build):
1. *The relation.* `ewpTS` is a least fixed point (SPEC §19 *Divergence*), so a computation that
   ticks forever is not in it. The candidate is a greatest fixed point over segments, with `tick`
   as the guard: `cwp M Q = gfp W. ewpTS M Π_W Q`, where `Π_W` gives `tick`'s continuation the
   obligation `W` (`ewp_mono` makes the functional monotone). It needs no step-indexing if each
   segment is finite. Hypothesis. Every rule's compatibility at rows with `Div` must be re-proved
   segment by segment. The borrow frames are unaffected while `tick` cannot cross a borrow (T1):
   a borrow callback's row is unwind-only, so `LoopLend` stays.
2. *The residual.* A loop closed early hands back what has no destructor (SPEC §14). An affine
   cancel answers `()`. A cancel that answered the residual would change "the canceller sees `()`"
   (algebra, *Cancel*): a hard stop. The candidate that avoids it: `tick`'s continuation is
   *linear*. Closing is a resume with `close`, and the code after each tick returns the residual
   by name, as today's per-state `close` does. Hypothesis.
3. *`div_fuel`'s counts.* Ticks must stand exactly where today's machine skips: every move at the
   empty row, back edges only at a row (SPEC §14 *Moves*). Any corpus program whose `div_fuel`
   output changes is hard-stop item 2.

**Conflict.** OQ-15 records the kernel reading of divergence as decided: codata, `U(Loop B R)`
(a), with div as a row entry (b) not taken. Decision 35 says "a div function returns a loop". The
effects state register quotes "Div is not an algebraic effect; it stays codata/delay, and nobody
should pretend it is handled" (`docs/effects-state/04-decisions.md` §3 D1). This option keeps
codata as the model, since `cwp` is coinductive and `reify` gives `Loop` values. But it makes div
a handled operation. Only the user can reopen that.

**Cost if reopened.** On the effect side only, while `tick` obeys T1:
- one primitive, the loop;
- one relation clause, `cwp` at rows with `Div`;
- the handlers of `Div` (`reify`, `div_fuel`) with a coinductive `[op]` case;
- FP and adequacy restated at those rows;
- `total_every_run` unchanged, since its row is empty.

No value-type former. The trade-off against the recommended path: it removes A9, A10, D1 and
§14's machine, at the price of the relation. The recommended path keeps the machine as the
meaning and removes only its cost.

### 4.5 Borrow interactions

| change | borrow effect |
|---|---|
| keeping `qs`, the effect context, spans | none: data beside the checked term |
| clause kinds by scheme | none: the same terms are checked |
| native loops from complete roots (N4) | the meaning lends per observation (§14, `LoopLend`). The native loop runs the same lends in the same order, one per turn: a lend ends inside its turn. A frame slot is used only where no resumption point crosses the scope (`crossedScopes`, `Capture.lean:1046`), as now. PinLaw's R1 lends cross only real suspensions, which keep their machine |
| a reified loop's machine | as today |
| #216 | a captured borrow outlives the site, as every capture |

## 5. Prior art, compared on fit

| system | what it carries, and how | fit |
|---|---|---|
| Granule (Orchard, Liepelt, Eades, *Quantitative program reasoning with graded modal types*, ICFP 2019) | graded modalities over a semiring: how many times a value is used; graded effects | #216's clause multiplicity is such a grade. Tail position is not: grades compose by counting |
| QTT (McBride, *I Got Plenty o' Nuttin'*, 2016; Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018; Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021) | the 0 grade decides what erasure removes | the converse here: facts with no runtime meaning (kinds, spans, entries) that erasure must *keep* for the compiler. QTT's discipline applies: they must not change the meaning, which is why they sit beside the checked term |
| Koka (Leijen, *Type Directed Compilation of Row-Typed Algebraic Effects*, POPL 2017; Xie et al., *Effect Handlers, Evidently*, ICFP 2020; Xie and Leijen, *Generalized Evidence Passing for Effect Handlers*, ICFP 2021) | clause kinds are written in the handler (`fun`, `val`, `ctl`, `final ctl`); a `fun` runs in place; `div` is an effect in the row, and total means no effect | the clause kind as a declared, checked form is §2.3's route for A1. Koka's `div` row is §4.4's option, without a mechanised codata model. Its evidence is run-time, which #541 forbids |
| Effekt (Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*, OOPSLA 2020; Schuster, Brachthäuser, Ostermann, *Compiling Effect Handlers in Capability-Passing Style*, ICFP 2020; Brachthäuser, Schuster, Lee, Boruch-Gruszecki, *Effects, Capabilities, and Boxes*, OOPSLA 2022) | lifts are inserted by a type-directed translation, so the compiler knows them; blocks are second-class unless boxed | the closest fit. The translation's output carries what the types decided, as the table does. System C's box is the reification point. Here it is a mode of the structured IR (§2.2), because as a kernel former it would cost a value type and change the borrow rules |
| Lean 4 (Ullrich and de Moura, *`do` Unchained*, ICFP 2022; `partial`, `implemented_by`) | `do` elaborated to `forIn` with join points and a threaded tuple; the compiler compiles `partial` definitions from code the kernel sees as an opaque constant | the `do` translation is loops U3/U4's. `partial` is the M-direct design: compiled code the kernel never checked, trusted. §4.2 rejects it for borrow guarantees |
| MLIR (Lattner et al., *MLIR: Scaling Compiler Infrastructure for Domain Specific Computation*, CGO 2021) | `scf.for`/`scf.while` with loop-carried values, lowered to the unstructured `cf` dialect by a later conversion; progressive lowering | the loop node with live variables per edge (U3) is `scf`'s `iter_args`. Progressive lowering is §3.1's order: structure kept until the lowering that needs to lose it |
| Rust MIR (rustc's MIR building, NLL borrow checking, drop elaboration, `rustc_mir_transform/src/coroutine.rs`) | one IR is borrow-checked and compiled; the coroutine transform runs on MIR after borrow checking | the property kept here: the compiled code comes from the checked IR, and the state machine is made after checking. The difference is that MIR's shape is a good compilation IR, while our checked term's is a proof encoding, hence the table |
| CPS, ANF, join points (Appel, *Compiling with Continuations*, 1992; Flanagan, Sabry, Duba, Felleisen, *The Essence of Compiling with Continuations*, PLDI 1993; Kennedy, *Compiling with Continuations, Continued*, ICFP 2007; Fluet and Weeks, *Contification Using Dominators*, ICFP 2001; Maurer, Downen, Ariola, Peyton Jones, *Compiling without Continuations*, PLDI 2017) | CPS reifies every continuation, then contification recovers the second-class ones. Kennedy separates local continuations from first-class ones. GHC's join points are a typed form of Core that Core Lint checks and the optimiser preserves | our kernel term is the reify-everything end: a `κ` per operation, a `ν` per div body. A1, A9 and #540 are contification. GHC's lesson is §2.3's: make the non-reified case a checked form, so that it is kept, not recovered. SSA (Kelsey 1995; Appel, *SSA is Functional Programming*, 1998) is ANF with join points: N4's native lowering of a machine |

## 6. The test before building

### 6.1 What disappears, what appears

- **No longer the decision for elaborated programs**:
  - `tailClause?` and `tailResumptive` (A1);
  - `clausesAt`'s one-closed-clause test (A4);
  - #540's specialisation of `drive` into loops (A9);
  - `loopsAt` and `LoopLend`'s `fin` (D1, by U2);
  - `opsC` (D2).

  `tailClause?` and `clausesAt` stay as the table's producer for table-less input (§3.4).
- **Deleted**: the frontend's lowering report as separate text (D5); the string templates of
  N1's schemes (D6).
- **Unchanged**: C1–C7, B1 and B2 (until C3), `Capture` for reified values and stored `κ`.
- **New kernel forms**: none. #216 changes one premise.

### 6.2 Predicted effect on #537's rows

Ratios over Rust on `make bench`'s machine. The targets are effect-lowering's and loops'. What
changes is that they are reached by construction, with no budget to exceed.

| row | now | predicted | units | why |
|---|---|---|---|---|
| sieve | 5.63× | ≤ 1.4× (sieve-for 1.30×) | N4 | its machine is all §14's; native from `main`'s root |
| chain-yield | 2.10× | ≤ 1.2× (chain-for 0.99×) | N4 | `yield` is already direct (#547); `range`'s `while` native |
| chain-gen | 21.5× | ≤ 1.3× | N4, 7 | push stages on the IR; without 7, two pull machines per element stay |
| gen-tree | 1.72× | ≤ 1.4× | 8 | unchanged by this design |
| async-tree | 0.84×, indirect 201 | ≤ 0.84×, indirect 0 | N3, 5 | copy groups from the table |
| raise-small | 1.30× | ≤ 1.1× | 8 | unchanged by this design |
| handlers-di, raise-large | 0.98×, 1.03× | unchanged | — | — |

`corpus/for-yield-branch.bc`'s site 3 becomes resume or cancel in place (unit 4, kind from N3),
and its `machines 17 suspending 9` falls. I do not predict to what. Every `allocs`, `indirect`
and `copies` value may only drop. The new count of machines driven at a complete consumer is 0
on the corpus and `bench/` after N4.

### 6.3 Kill criteria

Any one shows the design wrong where it applies:

1. **The table is incomplete.** After N3 and N4, an elaborated corpus or bench program still
   needs a search recogniser or a budgeted pass to decide its lowering. Then the IR lacks the fact.
   If the fact cannot be computed there, M is the wrong route for it.
2. **Verification is not exact.** A scheme's erasure is not a function of its entry, because a
   later frontend pass (`Respan`, `Hygiene`, `RenameLife`) changes it. Then that entry is
   recovered instead, and the design names which.
3. **Meaning.** Any of N1–N4 changes a desugar output, a golden, an exit status, `live 0`, a
   falsifier mode or a `div_fuel` count. That is a hard stop.
4. **Construction.** After N4, a machine is still driven at a complete consumer in the corpus or
   `bench/`. Then the modes are wrong.
5. **Cost is elsewhere.** After N4 and unit 1, sieve is above 1.6× or chain-yield above 1.5×.
   Then the native lowering is not where §1.3 puts the cost.
6. **(§4.4, only if the user reopens OQ-15.)** The spike cannot prove the compatibility of the
   loop, bind and `reify` at `Div` rows without step-indexing, or one corpus program's `div_fuel`
   answer changes. Then §4.4 is dropped.

## 7. Build plan

As §3.6's order: N1 and N2, then N3 (with effect-lowering 3–5 after it), U2, N4, U3–U4, unit 7.
Each unit lands with its spec text, its acceptance programs, `counts.expected` and the desugar
diff, and keeps every golden. N2, N3 and N4 touch `Backend/`, so `make gate-full` applies.

## 8. Open choices for the user

1. **The channel**: C1, **C2 (recommended)**, or C3 now (§3.3).
2. **Who classifies clause kinds**: **K1, the checker, in `Checked` (recommended for kinds)**,
   or K2, the backend's verifier for everything (§3.4).
3. **Loops**: **N4, construction from entries (recommended)**, or #540's specialiser as the
   mechanism (effect-lowering L1). #540 runs to its acceptance either way.
4. **Divergence in direct style** (§4.4): reopen OQ-15 and spike it, or not. Not recommended
   unless reopened. If it is, the spike comes before N4, since it would replace N4.
5. **Typed schemes**: N1 as one unit before U2 (recommended, conflicts with nothing running), or
   each loop unit converting the templates it edits.
6. **#216**: as its own unit after N3 (recommended), or later.

## 9. Hard stops and defects

### 9.1 The algebra hard stop

The recommended path changes no equation or semantic choice, no program's observable behaviour,
adds no runtime rule and rejects nothing. Two candidates would have:

| candidate | what it would change | where it stands |
|---|---|---|
| closing a reified direct-style loop by a cancel that answers its residual (§4.4, unknown 2) | "the canceller sees `()`" (algebra, *Cancel*) | not proposed; the linear-`tick` alternative avoids it, as a hypothesis |
| ticks placed other than at today's skips (§4.4, unknown 3) | `div_fuel`'s counts, hard-stop item 2 | a requirement of the option |

§4.4 as a whole revises a recorded decision (OQ-15 (a), decision 35), not an algebra equation.
It is reported for the user.

### 9.2 Defects

1. **The checked qualifier is discarded at conversion** (`Convert.lean:737–739`). The backend
   then builds a cancel arm for every `κ` (`Capture.lean:259–266`), including a linear `κ`'s,
   which has no cancel (SPEC §19, `kappaC_cancel_lin`). Root fix: keep `qs` (N2).
2. **The elaboration schemes are strings** (`Sugar.lean:253`, `:570`, `:1057`; 18 call sites). Loops
   U2's acceptance says "The fold/machine agreement (§2.6) is proved over the template"
   (#549). Effect-lowering units 3 and 7 ask for equations "over elaborated terms". A Lean lemma
   can be stated over a Core shape, as #547's `tail_resumes` is. It cannot be stated over the
   string the frontend parses. So the link between the scheme the frontend emits and the shape
   the law is about is unproved, and only the desugar diff tests it. Root fix: N1.
3. **The frontend's lowering report is not the lowering** (D5). `for-yield-branch.bc`'s three
   sites have one report text, and the backend made two direct calls and one machine. The
   bench README's earlier claim that chain-yield's `yield` was a direct call
   (`docs/effect-lowering.md` §1.5) is the same gap: nothing ties a description of the lowering
   to the lowering. Root fix: N3 renders the report from the
   table the backend verifies.

**Unspent, untranscribed and unverified.**
- #540's branch was read as committed WIP (`bcd0eb3`) plus uncommitted changes. Its final
  form may differ.
- U1's node was read from its uncommitted worktree (`LoopSrc`, `Comp.loop`).
- The complete-drive law (§4.2), §4.4's three unknowns and every row of §6.2 are hypotheses.
- I have not checked that `prepare`'s five rewrites can carry C2's array without losing a node.
  Kill criterion 2 tests it.

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
