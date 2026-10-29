# Loops: one loop model for every nest (#545)

**Status (2026-10-21).** U1 (#548) is built, and U2's class with B2 (#644, SPEC §62): a counted
loop whose body loops is at the row `div`, `bounded_fix` over the count
(`docs/pipeline-architecture.md` §3.2), with `break e` and `else`; counted machine loops over a
cursor are not built. Over a lend (`&a`, `&mut a`) its borrow is held across the body's ticks, and
the kernel refuses it (AW, AL, AG; SPEC §14, *Borrow scopes over loops*). The per-observation lend
(`LoopLend`'s rewrite, S13 below) is retired. The rest is the design as written.

A design for the surface's loops: `for`, `while`, `loop`, their exits (`break`, `break e`,
`continue`, `return`, and exits to an enclosing loop by name), and how a nest of loops of any
kinds is elaborated. It changes no code. Each claim is marked:

- **measured**: a run of `bcc run` or `bcc check` (`.lake/build/bin/bcc`) on `main` at `7a6d275`,
  reproducible by the programs in §7;
- **by inspection**: read off the code or SPEC, with no run behind it;
- **hypothesis**: argued here, not checked.

The hard requirements are #545's: a counted loop over finite data stays total, and a nest is div
only when something in it is div; every borrow guarantee holds (T1, close on every exit); an exit
is a branch and a loop stays a loop in the IR; every decided law holds
(`research/effects/src/decisions.md`, *The decided algebra*); sugar never special-cases the
kernel.

## 0. Summary

- **The defect.** Each loop's lowering is chosen from its own syntax and source type, before the
  nest around it and the loops inside it are known (§1.1). The choice is one of three: a total
  fold, a handler site, or a point of the body's state machine. A fold's step is a value, so a
  machine loop cannot be put inside one. The "spine" rules exist to keep it from being tried, and
  most refusals in §1.3 come from them.
- **The model** (§2). Every loop is one node of the surface tree, with a label, a source, a body,
  an `else` and its exits. After typing, a bottom-up pass gives each loop a **class**:
  - *total*: its source is sized, and nothing in its subtree is div;
  - *machine*: its source is unbounded, or something in its subtree is div.

  Machine is closed upward: a loop around a machine loop is a machine loop. A total loop is
  lowered as today: `count_try`, `bounded_fix` at a resuming row, or a handler site. A machine
  loop is a point of §14's machine; a counted machine loop walks its source's cursor, as
  `forDataDiv` does today. An exit is an edge to a join point. The edge carries the variables
  live at its target. Between total loops it leaves by the fold's `inr`, one branch per level;
  between machine points it is a move.
- **Totality** is a fact about the typed subtree, not one loop's syntax. A nest is div exactly
  when one of its loops or calls is.
- **Predicted** (§5):
  - the 24 matrix cells other than AA run and print 241;
  - AA, `*xp * *xp` and the one-arm case run once #58 lands (§3);
  - `return` at any depth runs in every cell;
  - labelled exits run;
  - #491, #501, #502, #503, #527 (item 1) and #150 are fixed; #493 is fixed by the threading
    unit; #492 and #527 (item 2) are independent; #134 does not reproduce on `main`.
- **No algebra hard stop** in the recommended path (§2.7). Two reports under hard-stop item 2
  need the user's confirmation, because they change existing `corpus/reject/` programs:
  - `corpus/reject/for-data-gen-loop.bc` is accepted by the model. It is the shape #545 requires.
  - `corpus/reject/double-use-in-callee.bc` would be accepted by one option of §3 (views copied
    implicitly). That option is not recommended without a decision.

  One option, not recommended (§2.6, G2), may change programs' observable behaviour; it is
  reported there.
- **Backend.** No unit touches the backend. The new machine-shaped nests run through `drive`
  until #540 lands (§6).

## 1. Inventory

### 1.1 The loop forms

`while c { M }` and `loop { M }` are parsed as a `for` with a marker source
(`Parser.lean:1506`, `:1516`: `.for_ sp io_while (.sugar .while_ c) M N`). So the surface
has one constructor, `.for_`, and the forms below are chosen when it is elaborated.

| form | written | elaborated by | becomes | decided from | when |
|---|---|---|---|---|---|
| counted `for` | `for x in a..b`, a view, `&a`, `&mut a`, an owned array, a sized iterator | `forData` (`Sugar.lean:4118`) | `count_try` (§16 K0′): one pure step per element, exits in the step's `inr` | the source's type (`dataSrcOf`, `:2371`), and the body's row (`opsC`) | at `surfC`, before the div pass, without looking inside the body for loops |
| counted, abortive body | the same, the body raising | `forData` | `count_try` whose step handles the operations of their sites and leaves by `inr`; re-raised after the loop | `opsC` finds only abortive operations | the same |
| counted, resuming body at a `with`'s site | the same | `forData`, `rowLoop` | `bounded_fix` over the count at the row (§30, *proposed*) | a resuming operation of a site not in `perTurn` | the same |
| counted, resuming body at a per-turn site | a `yield` in the body | `forDataDiv` (`:4439`) | a `while` over the source's cursor, a machine loop; no `break e`, no `else`; `&a` rejected | the operation's site is in `St.perTurn` | the same |
| `for` over a generator call | `for x in g(e)` | `forYield` (`:4544`) | a handler site; the body is the clause. Total when `g` does not loop. When `g` loops, a direct-style call of the loop handling each observation (`io_hwf`) | `g`'s result type (`loopRowOf`) | at `surfC` |
| `for` over a generator, body not a clause | the same, the body performing a control operation or looping | `Effects` (`pullSite`), then `mLoop` | a drain of `g`'s stored generator | the body's shape (§15, *A body that performs…*) | at effect elaboration |
| drain | `for` over a stored generator, an iterator, the input | `mLoop` (`:1320`) | a point of the body's machine (§14) | the source's type is not sized | in the div pass, after `surfC` |
| `while`, `loop` | `while c { M }`, `loop { M }` | `mLoop` | a point of the machine | the parser's marker | in the div pass |
| `count_fold` | library call | none | K0 | — | — |
| a block that loops | `{ S }` | `surfV` | `div_defer` of the machine | `loopsAt` on the block | at `surfC` |

By inspection. So the choice among fold, handler site and machine point is made one loop at a
time, from the loop's own source and the operations its body performs. Only one fact about the
body is used: `forYield` refuses a looping generator under a `.total` exit
(`:4614`). Nothing asks whether the body contains a machine loop.

### 1.2 What each refusal comes from

A counted loop's body is placed inside `count_try`'s step, `!{ (i, s) -> … }`, a value (the
template at `:4365`). The div pass then meets the inner `while`'s `.for_` inside a value, and
`Comp.elab` refuses it (`:150`). A looping generator is refused earlier, by `forYield`, under the
`.total` entry that the counted loop pushed on `DivSt.exits` (`:4427`).

`return` from a counted loop takes its type from the head of `DivSt.exits`: `.total Rt` under
another counted loop, or `exp`. Inside a machine body the head is `.drain` and `exp` is unknown,
so the type is "not determined" (`:4167`, `:4568`). By inspection. This is the cause of the
`return` failures of §1.3.

`LoopLend` decides whether a borrow block's body loops from `loopsOnSpine`
(`LoopLend.lean:123`). That reads a `for` as total from its source alone (`fin V M N`), in a
context of the parameters only, and does not look inside its body. By inspection.

### 1.3 Every spine rule and refusal

Each row was measured with the matrix of #545 (§7.1), its `return` variant (§7.2) and the cases of
§7.3.

| # | where | message (start) | cells and programs | cause |
|---|---|---|---|---|
| S1 | `Comp.elab` `.for_` (`Sugar.lean:150`) | "`for` may appear only on the spine of a function's body…" | RW, RL, AW, AL; `while` in an `if` that is the head of `;` (§7.3 `s1`); a `while` inside a counted loop with `return` (`s6`) | a machine loop inside a fold's step or a bind's head. For W and L the message names a `for`, which the program does not have |
| S2 | `forYield` (`:4614`) | "`gen` loops, so a `for` over it is div, and it is inside the body of a loop that is one total step…" | RG, AG; `corpus/reject/for-data-gen-loop.bc` | the same, caught earlier |
| S3 | `forData` (`:4185`) | "`a` is lent to this loop, so its body does not use it" | AA; `for xp in &a { … for yp in &a … }` | the body names the lent place. Independent of the split (§3) |
| S4 | `forData`, `forYield` (`:4167`, `:4568`) | "the type of the function's result, which a `return` in this loop returns, is not determined here" | §7.2: GA, GG, LA, LG, LR, WA, WG, WR; `s5` | the return target is found per form (§1.2) |
| S5 | `forDataDiv` (`:4446`) | "…so the loop is div…, and it has no value: `break e` and `else` are not provided there" | a counted loop with `yield` in its body, and `break e` | not built in `forDataDiv` |
| S6 | `exitOffSpine` (`:732`), `normExits` (`:742`) | "`break`, `continue` and `return` may appear only on the spine of a loop's body…" | an exit in a value or a call's argument, or in a head whose binders the rest uses | exits are moved by duplicating the rest into each arm |
| S7 | the checker, on elaborated core | "type mismatch: expected `i32`, but this has type `U (delay i32)`" | a div call in a counted body (`s4`, #503 item 1); in an `if` that is the head of `;` (`s2`, #503 item 2) | the div call is in a value position the div pass does not reach |
| S8 | the checker, on elaborated core | "`a` is used twice here…" | §7.2's RR with `for _ in a {}` before `return` (`rRR`) | every exit carries the whole threaded tuple (`exitV`, `tupleVal wsN`, `:4400`), including a variable this path consumed |
| S9 | `loopsAt` (`:454`) | "`spin` is declared `total`, but it has a `for` over an unbounded source (a drain)" | #527 item 1, a `while` | `while` is a `.for_` |
| S10 | `forYield` | "the loop's value has type `i32`, and `gen` returns `1`" | `let r : i32 = for i in gen(10) { … break v … }` (§7.3 `i134d`) | a `for` over a generator has no `else`, so its value must be the generator's result |
| S11 | parser | "expected a value, found `loop`" | `let r = loop { … break v }` (`i134b`) | `loop` and `while` are not expressions |
| S12 | `forData`, `forDataDiv` (kept) | "…performs an operation that resumes, and its source `&a` lends `a` around the whole loop…" | `corpus/reject/for-lend-resumes.bc` | T1, #172. Kept |
| S13 | `LoopLend` | "`count` loops, so it is called in direct style one step at a time…"; "the iterator of this `for` holds the borrow of `v`" | #491, #501 | §1.2: decided before the source has a type |

**The matrix** (measured): 19 of 25 print 241. The 6 refused are RW, RL, RG, AW, AL, AG (S1, S2).
AA is S3. This agrees with #545. **The `return` variant** (§7.2): 10 of 25 run (AR, GL, GR, GW,
LL, LW, RA, RR, WL, WW). The others are S1/S2 (6), S3 (AA) and S4 (8).

### 1.4 The issues

| issue | measured on `main` | symptom of the split? |
|---|---|---|
| #491 | as filed | **yes**: `LoopLend` decides "loops" before the source is typed, so a typed view is read as a drain (S13). Reproduction 2's `spinePattern` failure is a second cause: the parameter tuple is not matched. Deciding from the typed subtree removes both, since neither pattern is needed |
| #492 | as filed (§7.3 `i492`); without the loop it runs (`i492b`: `i32[5]`) | **independent**. `bcc desugar` shows the generated `case fx_self { inl -> abort[1.0] () \| inr -> …(a, …) }` of §20's budget inside the `handle_with` that `count_try`'s step installs for abortive operations, with no drop of `a` in the `abort` arm. It concerns drop placement in that generated code, not where the loop may stand. Not predicted fixed here |
| #493 | as filed | **independent in mechanism, fixed by U3**: the threaded variables are chosen by name (`mentionsC y M`) without the body's own binders. Live variables computed with scope (U3) choose the binding, not the name |
| #501 | as filed | **yes**: as #491 |
| #502 | as filed | **yes**: a loop that threads `a` inside an `if` that is the head of `;` rebinds `a` in the arm, and the rebinding does not reach the rest. A join point for the rest (U3) passes it |
| #503 | items 1–2 reproduced (`s4`, `s2`) | **yes**: S7. The model accepts them, so the diagnostic is replaced by a run (item 3 likewise, by inspection) |
| #527 | item 1 yes (S9); item 2 is a borrow block's message | item 1 **yes** (`while` is a `.for_`); item 2 **independent** (a message) |
| #150 | with the needed ascriptions (`i150`), refused: "`rest` is consumed in the `inr` arm but not in the `inl` arm" | **yes, hypothesis**: S8's cause, the `return` path carrying the threaded `rest` after `match rest` consumed it. The ascriptions it needs (`(inl f : text 'a + 1)`) are an independent inference gap |
| #134 | **not reproduced**: `break 0 - 1 - i` runs over a count and over a stored generator (`i134`, `i134f`) | its generator form hits S10, a different rule. A corpus program covering it is enough to close |
| #58 | `*r * *r` refused in a plain function (`e6`) | **independent**. See §3 |

## 2. One loop model

### 2.1 The node

The surface tree gets one loop constructor, carried through typing and the class pass:

    loop ℓ (src) { M } else { D }; N

- `ℓ`: a label, written or fresh.
- `src`: what the loop walks:
  - `count a b`;
  - `data V` (a view, `&a`, `&mut a`, an owned array, a sized iterator);
  - `gen g(e)`: a call of a function that performs an iteration effect;
  - `drain V`: a stored generator, an iterator, the input;
  - `while c`;
  - `forever`.
- `M`: the body.
- `D`: the value when the source ends. A source that cannot end has none.
- `N`: what follows.

Exits are terminals of the body, each naming its target: `break ℓ e`, `continue ℓ`, `return e`.
An unlabelled `break` or `continue` names the innermost loop.

`while` and `loop` stop being `for`s with a marker. That fixes S9's message, and makes
`let r = loop { … break v }` and `while c { … } else { d }` expressible (S11).

### 2.2 Where totality is decided

After typing, so every source and every call has its type, one bottom-up pass gives each loop a
class:

    machine(L) ⇔ src(L) is drain, while or forever
               ∨ src(L) = gen g(e) with g's body looping
               ∨ M performs an operation of a per-turn site (St.perTurn)
               ∨ M calls a div function in direct style, at any depth
               ∨ some loop in M is machine
    total(L)   ⇔ ¬machine(L)

- **Machine is upward-closed.** A loop around a machine loop runs across observations, so it
  cannot be one step.
- **A function is div** when a loop on its body, or a direct-style call, is machine. This
  replaces `loopsAt`'s syntactic test (S9) and `LoopLend`'s `fin` (S13). Both read the class.
- **Totality from data.** A loop is total only by its source's type (`dataSrcOf`, `sizedOf`) or
  its generator's result type. Nothing reads a name. A nest is div exactly when one of its parts
  is, and that shows in the function's type, `U(Loop B R)`.

| option | rule | for | against |
|---|---|---|---|
| **T1: the subtree's class** (recommended) | as above | a total loop inside a div body stays a fold (R under W, as today); totality is exact | one more pass over the typed tree |
| T2: the function's class | every loop of a div body is a machine point | simplest | R under W stops being `count_try`. Its turns become observations, which changes what `div_fuel` counts for existing programs. Hard-stop item 2, so excluded |

### 2.3 Where each lowering is chosen

| class | source | lowering | today's form it is |
|---|---|---|---|
| total | `count`, `data`; pure body | `count_try` | `forData` |
| total | `count`, `data`; abortive body | `count_try`, step handling the operation (option A1) | `forData` |
| total | `count`, `data`; resuming at a `with` site | `bounded_fix` over the count at the row | `forData` `rowLoop` (§30) |
| total | `gen g(e)`, `g` not looping | handler site; the body is the clause | `forYield` |
| machine | `count`, `data` | a point at the loop's head over the source's cursor (index, rest, sized state), one turn per observation | `forDataDiv`, generalized |
| machine | `gen g(e)`, `g` looping, body a clause | direct-style call of the handled loop (`io_hwf`) | `forYield` |
| machine | `gen g(e)`, body not a clause | drain of the stored generator | `pullSite` + `mLoop` |
| machine | `drain`, `while`, `forever` | a point of the machine | `mLoop` |

The information is the class (§2.2), the source's type, and the row (`opsC`, `perTurn`), all known
after typing. Every row is an elaboration that exists. The model changes **when** the choice is
made (after the class pass) and **what it may contain**, not the set of lowerings. A counted
machine loop is the one generalized form: `forDataDiv`'s cursor sources, moved into `mLoop`, with
`break e`, `else` and a join (S5).

**Borrows of a counted machine loop's source.** In a machine nest the loop is codata, so its lend
is the per-observation lend of §14:

- an owned array or `&a` is lent one turn at a time: the index in the state, the element borrowed
  inside the stretch that uses it;
- what the body keeps across a point (an element borrow live after an inner `while`) is refused,
  with §14's message ("a stretch before the loop that hands on something with `'x` in its type").
  That is the spanning lend, K1 (#172), which no unit here adds;
- a resuming operation under a lend stays refused (S12, T1).

So AW and AL run (`let i = *ip` copies before the inner loop). A variant that reads `*ip` after
the inner loop is refused by the existing rule, by design. `LoopLend` must read the class in the
same unit (U2). Otherwise a borrow block around R-over-W would be kept open across observations.
The core checker would refuse the result as a borrow that does not outlive its block, so this is
a confusing message, not unsoundness (by inspection of §14's outlives rule).

### 2.4 Exits: edges to join points

An exit is an edge from its terminal to a **join point**:

- `continue ℓ` goes to `ℓ`'s next turn;
- `break ℓ e` goes to `ℓ`'s rest `N`, with `e`;
- the end of the source goes to `N`, with `D`;
- `return e` goes to the function's terminal.

A join point is a `!` function of the variables live at it. Decision 42 already makes a machine
loop's join such a function, not a summand. The edge carries exactly those variables. It does not
carry the loop's whole threaded tuple. This fixes S8 (#150) and, computed with scope, #493.

How an edge is lowered depends on the classes it crosses:

- **Within one total loop**: the step's `inl s` (next turn) or `inr (live, e)` (leave), as today.
- **Out of nested total loops**: the inner fold answers `inr (live, up e)`, where `up` is a sum
  over the exits that leave it. The join after it is a `case`: `here` continues after the inner
  loop, and each `up` re-issues the exit one level out. This is how `return` leaves counted loops
  today (`LoopExit.total`), extended to `break ℓ` and `continue ℓ`. One tag test per level left.
  It runs only on the leaving path, and nothing is dispatched.
- **Out of a total loop inside a machine loop**: the fold's `inr` reaches the machine's code, and
  the `case` there is a move (`mGoto`) to `ℓ`'s join or head, or the finish for `return`. S4
  disappears because the return type is the function's result. The class pass knows it, so it is
  not looked for on `DivSt.exits`.
- **Between machine points**: a move, as `mBreak` and `return` are today, generalized from the
  innermost loop to `ℓ`.
- **A machine loop inside a total loop**: excluded by upward closure.

**In heads.** A loop, an assignment or a div call inside a head (`if c { while … } else { () };
N`) currently needs the spine. Under the model the head's terminals jump to a join point for `N`,
of the variables `N` reads, including the ones the head rebinds. This fixes `s1`, `s2` and #502.
`normExits` duplicates `N` into each arm instead (a commuting conversion). That is exponential in
nested heads, a degenerate blowup:

| option | how | for | against |
|---|---|---|---|
| J1: keep duplication where it applies today; join points only for heads it refuses | narrowest | every accepted program desugars as before | two mechanisms |
| **J2: join points everywhere** (recommended, after U3 measures it) | one mechanism | no duplication | changes the core of every program with an exit in a head. Counts may only drop, and each change is explained |

Recommendation: J1 inside U3, so U3's invariant is "desugar unchanged". Then J2 as a separate,
measured step.

### 2.5 The loop's value

One rule for every loop that can end: the value is `break e`'s, or `D` when the source ends.
A source that finishes with `B ≠ 1` (a drain, a generator) gives `D` its result. The spelling is
provisional: `else r -> d`. Without `else`, the value is the source's result, as today. A source
that cannot end has no `else`, and its value is `break`'s (type `0` without one). Today's rules
are each a case of this (§16 *The loop's value*). The rule also admits `else` on a generator's
`for` (S10) and a value on `while` and `loop` (S11). No accepted program changes. Hypothesis, to
be checked by U4's desugar diff.

### 2.6 Laws the model must satisfy

**Close on every exit.** An edge that leaves loops `L₁ … L_k`, innermost first, runs
`close(L₁); …; close(L_k)` before its join. `close` depends on the loop:

- a drain's `close` (§7);
- a generator site's cancel `(force k).2`, which runs the generator's finalisers (§19, laws 5–6);
- a lend's end (the borrow block's).

Then the variables not passed are dropped (§12). Machine loops do this today for `return` and
`break` (`held`'s `closeSrc`). Total loops do it lexically: the borrow block ends with the fold,
and the clause cancels `κ` (`leave`). For labelled exits the order is the nesting order, which
`unwind_prefix` and the finally law already fix for raises: innermost first. This is Rust's drop
elaboration on an exit edge. **To state and test in U4**:

- a `break ℓ` out of a `for` over a generator inside a `for` over a stored generator cancels the
  first, then closes the second;
- `corpus/gen-close.bc`'s order is unchanged.

**Exit propagation (fold fusion with exits).** For total loops,

    count_try(λ(i,s). case count_try(f, …, s) { inl t → g(i, t) | inr (l, here b) → h(i, l, b)
                                                | inr (l, up e) → inr (l, e) }, n, i₀, s₀)

answers the first `up e` the inner loop gives, with the outer loop's later steps not run. This is
`countTry_exit` (the first `inr` is the answer) applied at both levels
(`Support/Dynamics/Completeness.lean`). U4 states it as one lemma over the elaborated template.
Hypothesis until then.

**The fold and the machine agree.** A total loop elaborated as `count_try` and the same loop
elaborated as a machine loop over its cursor:

- give the same answer and perform the same effects in the same order when the machine is driven
  to the end;
- differ only in the number of observations, which only `div_fuel` sees.

The model never chooses the machine for a total loop, so no program depends on this. It is the
statement that a loop's lowering does not change its meaning. Proved by `countTryLoop_wp`'s
induction on `len − i`. Hypothesis until U2.

**Decided laws used, not changed**:

- deep handler laws and cancel, for `break` out of a generator site;
- algebraicity at abort, for option A2 below;
- static names, for labelled exits as handlers, option X2.

**Abortive operations in a total body.**

| option | how | for | against |
|---|---|---|---|
| **A1: as today** (recommended) | the step handles the operation and leaves by `inr`, re-raised after the loop | no change to existing core | `raise-small`'s cost. Effect-lowering unit 8 (#542 §2.2) fixes it in the backend |
| A2: perform in place | `bounded_fix` at the row, as `rowLoop` | no reification | changes the core of every counted loop that raises; the order of drops could move across a `close`, which hard-stop item 2 would have to clear program by program; duplicates unit 8 |

**Generators over finite data.** `fn gen(n) -> 1 with Yield[i32] = for k in 0..n { yield(k) }` is
div today (measured: `main : F U (delay i32)` for GR, and "`for` is div: `gen` loops"), because
`forDataDiv` turns its counted loop into a `while`.

| option | how | for | against |
|---|---|---|---|
| **G1: keep it div** (recommended) | as today; the model makes GR and AG run as machine nests | no existing program changes | a generator over a count is div, so `total` refuses its consumers |
| G2: total | the per-turn case becomes `bounded_fix` at the row, like a `with` site, so `gen` is total and its `for` is one handled call | totality from data reaches generators | **may hit hard-stop item 2**: a stored generator over such a body no longer skips a turn that yields nothing, so a consumer that observes skips (`first_two` in `corpus/for-data-div.bc` treats a skip as the end) can see different elements, and `div_fuel` counts change. I have not checked which corpus programs change. Not proposed without a decision and that check |

### 2.7 Exits as abortive operations: the candidate

#545 asks this to be evaluated: each loop installs a handler with abortive operations `brk(v)` and
`cont()`, and an exit is a raise to it. A named exit is a named handler instance, `with ℓ = h`
(#521), lowered as a branch, as abort is (`Unwind`).

- **For.**
  - Exits from inside a block or a callback (a `|>` stage, §32's blocks) come for free. Kotlin's
    non-local returns and Effekt's `loop { l => … l.break() }` do this.
  - Static names give labels with no accidental handling (law 3).
  - Unwinding runs finalisers in the finally law's order.
- **Against.**
  - **Decision 47** records "Exits live in the step's result, not in handlers". Adopting this
    revises a user decision. That is not an algebra stop, but it needs the user.
  - `count_try`'s step is pure, so a handler for the exit inside it is caught at the step and
    reified into `inr`, which is X1's encoding. To raise across steps, the loop must become
    `bounded_fix` at a row holding the exit effect, a different kernel term with a different
    lowering (A2's costs).
  - In a machine body an exit is a move between points, and a handler around a div computation is
    "not provided" (§20). So the candidate does not cover machine loops, and two mechanisms
    remain.
  - The `let mut` variables live after the loop still travel in the raise's payload. The payload
    is the same set as a join point's parameters.
  - At a generator site the clause holds an affine `κ`, which has no destructor. It must cancel
    `κ` before raising, as `leave` does today, so nothing is saved there.

| option | exits | covers | decision needed |
|---|---|---|---|
| **X1: edges to join points** (recommended) | values in the step's result between total loops, moves between machine points | every nest in §1.3 | none: decision 47 as written |
| X2: abortive operations | raises to a loop's handler | total loops, and exits from blocks and callbacks | revises decision 47; machine loops still need X1 |

**Recommendation: X1 now.** X2 is the extension for exits that cross a block or callback
boundary, where a handler is the only static carrier. It would come as its own unit after
§33/§32's blocks are settled. It would be lowered as abort (a branch per call) and would apply
only where X1 cannot reach.

**Hard stop.** None of X1, J1/J2, T1 or A1 changes a decided law or adds a runtime rule. G2 is
the one option that may change observable behaviour, and it is not recommended (above). Two
existing reject programs change; §5.2 lists them.

### 2.8 Labels

Syntax is provisional. `break name` collides with `break e` when `name` is a variable, so a label
needs a sigil:

- Rust's `'outer: for … { break 'outer v }` shares the tick with lifetimes, in a separate
  namespace;
- Zig's `outer: for … { break :outer v }` has no collision.

Either fits the node. The choice is a one-way door only in the sense that labels appear in user
code. U1 parses Rust's form, `'outer: for …`, the spelling §7.4 is written in; it stays
provisional. A label is a static name, so the edge's target is found lexically, as handler sites are
(§19 *Names*).

## 3. Element borrows in loops

| case | measured | cause | loop's threading? |
|---|---|---|---|
| `s = s + *xp * *xp` | refused in a loop (`b1`) and in a plain function, `fn f<'l>(r: imm 'l i32) -> i32 = *r * *r` (`e6`): "`r` is used twice" | `*` is `withload` on the borrow, which consumes it (`Sugar.lean:3325`); an `imm` borrow is not copied implicitly | no |
| a `break` in one arm (`if *yp > i { break } else { let y = *yp; … }`) | refused under every outer loop (`dR`…`dW`), with no `break` (`e2`), and in a plain function (`e3`): "`r` is consumed in the `inl` arm but not in the `inr` arm" | the condition's `*yp` consumed `yp`; the message names the second use's arm | no |
| AA, `for x in &a { for y in &a … }` | S3 | the body names the lent place | no |
| nested loops over two copies of a view (`e7`) | "`w` is used twice", generated by the counted loop | the inner loop consumes the view `w` each outer turn | no |

So all four are #58, implicit copies of `imm`, and not the loop's threading. For views and for a
place an enclosing loop lends, they are #58's natural extension. The threading defect is S8,
which these cases do not reach.

| option | scope | changes |
|---|---|---|
| **E1** | #58 as filed: an `imm` borrow used more than once is copied (`copy`, free) | fixes `b1`, `e2`/`e3`, the one-arm case. Spec entry and checker per #58 |
| E2 | E1, and `array_imm` views (`array_copy`) | also `e7`. **Changes `corpus/reject/double-use-in-callee.bc`** (a view used twice is its expected error; #145, #167), so hard-stop item 2 applies and needs a decision |
| E3 | E2, and `&a` of a place an enclosing loop lends `imm` is a copy of that loop's view (as §14 lets a block's borrow stand for the lent place) | also AA |

**Scope:** separate from this unit. #58 is its own spec entry (U5), and the loop units do not
depend on it. The matrix's AA cell, and §7.3's `b1`, `dA`–`dW`, `e7`, are its acceptance
programs. Recommendation: E1 with #58. E2 and E3 follow after the user decides on
`double-use-in-callee`.

## 4. Prior art, compared on fit

| system | loops and exits | how exits are lowered | fit |
|---|---|---|---|
| Rust MIR (rustc's HIR→MIR lowering of `loop`/`while`/`for`, labelled `break 'l v`/`continue 'l`) | one `loop` form; `while` and `for` desugar to it (`for` over `IntoIterator::next`); only `loop` has a value | a CFG: each exit is a `goto` to the labelled scope's exit block, with drop elaboration inserting the drops of every scope left on that edge | the model's edges and close-on-exit are this. Rust has no total/div distinction, so every loop is a CFG loop; here a total loop is a fold, because totality is a theorem (§14) |
| Zig (labelled blocks `blk: { break :blk v }`, `while (c) : (step) { } else { }`, `for … else`, `continue :outer`) | every loop an expression; `else` when the condition fails or the source ends | lowered to branches | §2.5's value rule is Zig's, extended to a source's result; the `:label` spelling avoids S11's ambiguity |
| Koka (`final ctl` effects; loops as library functions over closures) | no built-in `break`. A program declares an effect with a `final ctl` operation and handles it around the loop | evidence passing; `final ctl` does not resume | X2. Koka's exits work through callbacks because they are effects; its handler is found at run time, ours would be static |
| Effekt (*Effects as Capabilities*, OOPSLA 2020; the standard library's loops with a control capability) | `break`/`continue` as operations of a capability the loop passes to its body block | lexical capability passing; the staging work removes the overhead when handlers are known | X2's closest fit: a label as a capability, second-class blocks as §32's. Fits exits across blocks, the case X1 does not reach |
| Lean 4's `do` (Ullrich and de Moura, *`do` unchained*, ICFP 2022) | `for`/`while`/`repeat`, `break`, `continue`, `return`, `let mut`; no labels | translation into `forIn` with a step answering `ForInStep` (`done b` or `yield b`), mutable variables as a threaded tuple, join points for the rest of a `do` block, and `return` inside a loop as a wrapped result propagated out of each loop. The paper states the translation as rules (from the paper; not re-checked here) | X1 is this design: `count_try`'s `S ⊕ E` is `ForInStep`, `return`'s propagation is `LoopExit.total`, and its join points are §2.4's. Lean's `while` needs `partial` or a monad with non-termination, which is our div class. It decides that per definition, not per loop; T1 is finer |

## 5. The test before building

### 5.1 Programs, all expected to run

| set | programs | expected |
|---|---|---|
| the matrix (§7.1) | 25 cells | 241 each. AA needs E3 (§3), and all others need U2 |
| the `return` matrix (§7.2) | 25 cells, `return s` at depth 2 | 298 each. AA needs E3; S4's cells need U3; S1/S2's need U2 |
| labelled exits (§7.4) | 25 cells, `break 'outer` and `continue 'outer` from the inner loop | the value computed by hand per cell; needs U4 |
| loop values | `i134`, `i134b` (`loop` as value), `i134d` with `else` (U4); a `break e` in a counted body with `yield` (S5, U2) | `i32[4294967292]` (−4, as `i134` prints today) each; the generator's `break` value |
| heads | `s1` (a `while` in a head `if`), `s2` (#503 item 2), `s4` (#503 item 1), `s5`, `s6`, #502's | `s1`: 60; `s2`: 10; `s4`: 0; `s5`: 0; `s6`: 0; #502: `i32[3]` |
| borrows | `b1`, `dA`–`dW`, `e2`, `e3`, `e6` (E1); `e7` (E2); AA, `b5` (E3); AW, AL with `*ip` read after the inner loop (refused, §14's message) | as computed by hand |
| issues | #491, #501, #493 (three cases), #150's `fields.bc` with `for`/`return` (same output and counts as today's `fields.bc`) | their stated answers |
| kept refusals | `for-lend-resumes.bc` (T1); a `total fn` with a `while` (now naming the `while`); `for-free-bound.bc` | refused, messages naming the program's construct |

Expected values for §5.1's `s` programs are by hand, from the programs in §7.3.

### 5.2 The corpus

- **Units U1–U2**: every accepted corpus program and every `experiments/` program elaborates to
  the same core. Check with `bcc desugar` and `bcc check` before and after, as #521 did. Outputs,
  goldens, `counts.expected` and `kernel-counts.expected` are unchanged. A program's class equals
  the form it already has, by §2.3's last column.
- **U3** (live variables per edge): threaded tuples may shrink, so core may change. Every change
  is listed. `allocs`, `indirect` and `copies` may only drop. Loads and stores may change, and
  each rise is explained.
- **Reject programs that change (hard-stop item 2, for confirmation):**
  - `corpus/reject/for-data-gen-loop.bc` is accepted by U2. #545 asks for exactly this shape (RG).
    It moves to the corpus with its answer, 30.
  - `corpus/reject/double-use-in-callee.bc` changes only under E2.
  - No other reject changes. Measured over the 93 rejects' messages: none hits S1, and the one
    that hits S9's message, `total-loops.bc`, is a `for` over the input, whose message stays.

### 5.3 The issues, predicted

| issue | predicted | unit |
|---|---|---|
| #491, #501 | fixed | U2 |
| #502 | fixed | U3 |
| #503 | fixed: its programs run | U2, U3 |
| #527 | item 1 fixed (U1); item 2 not addressed | U1 |
| #150 | fixed (hypothesis: S8 is its cause) | U3 |
| #493 | fixed | U3 |
| #492 | **not** fixed by the model (independent) | — |
| #134 | already runs; close with a corpus program | U4 |
| #58 | its own unit | U5 |

### 5.4 Kill criteria

Any one shows the design wrong where it applies:

1. **Class is not enough.** A matrix cell can only be made to run by a rule that looks at a loop's
   form or name instead of its subtree's class.
2. **Not instances.** After U2, an accepted corpus program's `bcc desugar` output differs. Then
   today's forms are not the model's instances, and §2.3's table is wrong.
3. **Totality lost.** A loop over finite data whose subtree has no div construct is classified
   machine, or a `total` program of the corpus is refused.
4. **Exits not branches.** A labelled exit or a `return` from a total inner loop raises
   `indirect` or `allocs` above the same nest without the exit.
5. **Upward closure fails.** Some program needs a total loop around a machine loop: a borrow block
   or a `with` site that must stay one computation around a loop that is div. Then the boundary
   between the classes is in the wrong place.
6. **Loops not loops.** After #540, a new machine nest (RW, s1) still has loops driven by `drive`
   at a complete consumer (effect-lowering kill criterion 6, applied to the new programs). Or it
   runs above 1.5× the same program with its inner loop moved into a function.

## 6. Build plan

Units in dependency order. Each lands with its spec text (§14, §15, §16 amended where the spine
and per-form rules are stated), its acceptance programs, `counts.expected`, and the desugar diff of
§5.2. None touches `Backend/`.

| # | unit | needs | acceptance |
|---|---|---|---|
| U1 | **One loop node.** `while`/`loop` become loops with a source kind, not `for`s with a marker; labels parsed and carried (exits still to the innermost loop); messages name the construct written | — | desugar unchanged on the corpus; #527 item 1's message names the `while`; S1's message for W/L names `while`/`loop` |
| U2 | **Class pass and counted machine loops.** The bottom-up class (§2.2) on the typed tree; `forData` and `forYield` used only for total loops; a counted machine loop as an `mLoop` point over its cursor (`forDataDiv` moved there, with `break e`, `else`, a join); `loopsAt`, `total` and `LoopLend` read the class | U1 | the matrix's 24 non-AA cells: 241; `for-data-gen-loop` moved to the corpus; #491, #501, #503's programs; desugar unchanged otherwise; the fold/machine agreement (§2.6) proved over the template |
| U3 | **Edges with live variables; join points in heads.** Threaded variables per edge, computed with scope; a loop, assignment or div call in a head jumps to a join point for the rest (J1); `return`'s type from the function's result in every class | U2 | the `return` matrix's non-AA cells: 298; `s1`, `s2`, `s4`, `s5`, `s6`, `rRR`; #493 (three cases), #502, #150 |
| U4 | **Labelled exits and loop values.** `break ℓ e`, `continue ℓ` across total levels (the `up` sum, one test per level) and between machine points (moves closing the sources left); `loop`/`while … else` as values; `else` on every loop that can end | U3 | the labelled matrix (§7.4); `i134`, `i134b`, `i134d`; close-on-exit order programs (§2.6); the exit-propagation lemma |
| U5 | **#58, implicit copies of `imm`** (E1), its own spec entry; E2/E3 after the user's decision | — | `b1`, `dA`–`dW`, `e2`, `e3`, `e6`; with E3, AA in both matrices, `b5`, `e7` |
| (J2) | join points everywhere, replacing `normExits`'s duplication | U3 | counts no higher; the changed cores listed |

**Ordering against the backend.**

- U1–U5 change `Frontend/` only.
- #540 (effect-lowering unit 2) and #544 (unit 1) change `Backend/`. Neither conflicts by file.
- U2 makes new programs machine nests. They run correctly through `drive` before #540, and as
  loops after it. Their performance acceptance (kill criterion 6) waits for #540.
- Option A1 leaves `raise-small`'s cost to effect-lowering unit 8. A2 would duplicate that unit,
  and is not proposed.
- G2, if chosen, would interact with effect-lowering unit 7 (push stages): a total generator's
  `for` is already a handled call. It would need re-planning there.

## 7. Reproduction

All runs: `.lake/build/bin/bcc run <file>` in a checkout of `7a6d275`.

### 7.1 The matrix

#545's script, unchanged. Measured: 19 cells print `i32[241] live 0`. RW, RL, AW, AL give S1; RG,
AG give S2; AA gives S3.

### 7.2 The `return` matrix

#545's headers, with the program:

```
include yield
fn tab(i: i32) -> i32 = i
fn gen(n: i32) -> 1 with Yield[i32] =
  for k in 0..n { yield(k) };
  ()
fn find(n: i32) -> i32 =
  let a = array_new[i32] (4, tab);
  let mut s = 0;
  $(hdr $o i)
    if i == 1 { continue } else { () };
    $(hdr $i j)
      if j == 2 { continue } else { () };
      if i == 3 { if j == 1 { return s } else { () } } else { () };
      s = s + 10 * i + j
    };
    s = s + 100
  };
  for _ in a { () };
  0 - 1
main -> i32 = find(4)
```

Measured: AR, GL, GR, GW, LL, LW, RA, RR, WL and WW print `i32[298] live 0`. GA, GG, LA, LG, LR,
WA, WG and WR give S4; RW, RL, AW, AL give S1; RG, AG give S2; AA gives S3. With
`{ for _ in a { () }; return s }` in place of `{ return s }`, RR gives S8 (`rRR`).

### 7.3 Single programs

Each is `main` (or a function and `main`) as named; `tab(i) = i`, `a`, `b` of length 4.

- `b1`: `for xp in &a { s = s + *xp * *xp }` — "`xp` is used twice".
- `b2`: the same with `let x = *xp; s = s + x * x` — `i32[14]`.
- `b5`: `for xp in &a { let x = *xp; for yp in &a { … } }` — S3.
- `b8`: the matrix's AA over two arrays `a`, `b` — `i32[241]`.
- `dR`…`dW`: each outer header over `for yp in &b { if *yp > i { break } else { let y = *yp; s = s + y } }`
  — "`yp` is consumed in the `inl` arm but not in the `inr` arm".
- `e2`: the same body without `break` (`s = s + 0` in the then-arm) — the same refusal.
- `e3`: `fn f<'l>(r: imm 'l i32) -> i32 = if *r > 2 { 0 } else { let y = *r; y }` — the same refusal.
- `e6`: `fn f<'l>(r: imm 'l i32) -> i32 = *r * *r` — "`r` is used twice".
- `e7`: in `fn f<'a>(v: array_imm 'a i32)`, `let (v, w) = array_copy['a, i32] v; for xp in v { let x = *xp; for yp in w { … } }`
  — "`w` is used twice".
- `s1`: `if c { let mut k = 0; while k < 3 { k = k + 1; s = s + k } } else { () }; s = s * 10` — S1.
- `s2`: `if true { s = spin(3) + 1 } else { () }; s = s * 10`, `spin` a `while` — S7.
- `s4`: `for i in 0..3 { if i == 1 { s = s + spin(i) } else { () } }` — S7.
- `s5`: `while i < n { for j in 0..n { if j > i { return s } else { s = s + j } }; i = i + 1 }` in a `fn` — S4.
- `s6`: `for j in 0..n { … while i < n { if i > j { return s } … } }` in a `fn` — S1.
- `i134`: `let r = for i in 0..10 { if i == 3 { break 0 - 1 - i } else { () } } else { 7 }` — runs.
- `i134b`: `let r = loop { … break 0 - 1 - i … }` — S11.
- `i134d`: `let r : i32 = for i in gen(10) { … break 0 - 1 - i … }` — S10.
- `i134f`: the `i134` loop over a stored generator `g : U (pull i32 1 1)` with `else { 7 }` — runs.
- `i150`: `nth_field` of `corpus/fields.bc` as a `for` over `0..(k + 1)` with `return`,
  `rest : text 'a + 1` ascribed — "`rest` is consumed in the `inr` arm but not in the `inl` arm".
- `i492`: #492's program — as filed. `i492b`: the same without the `for` — `i32[5]`.
- `GR` under `bcc check`: `main : F U (delay i32)`, "`for` is div: `gen` loops".

### 7.4 The labelled matrix (U4)

#545's matrix with the outer header labelled and the inner body's `if j > i { break }` replaced by
`if j > i { break 'outer }` (one run per cell), and a second run with `continue 'outer`. Expected
values are computed by hand when U4 writes the programs. There is no syntax for it today, so
nothing here is measured.

**Unspent and unverified.**

- I have not traced #492's missing drop to its line. It is attributed by `bcc desugar` and by
  `i492b` running.
- §2.6's three laws are hypotheses until U2 and U4 prove them.
- G2's effect on skip-observing consumers is not measured.
