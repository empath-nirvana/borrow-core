# The effect calculus: coarse plan

**Status: agreed by the user (2026-10-03).** Validated first by three adversarial lenses. Three adversarial validators passed it after three rounds: borrow guarantees, decisions, and completeness. Each ran against the shared brief and the code. No GitHub issues are filed until the user agrees this plan and the full spec. Open questions are never issues.

**Shared context:** `docs/effects-state/BRIEF.md` (branch `effects-state`).

**Where this starts.** The effect kernel on `main` works and is proved at `σ = []`. Each unit extends it toward the structure signed off on 2026-10-03:
1. one signature;
2. models and comodels;
3. handler laws over the kernel;
4. one Kripke world `W`;
5. one borrow per printed constant over any well-formed row.

## The first rule

> "NOTHING CAN BREAK THE BORROW CALCULUS." … "There is a big difference between doesn't break the borrow calculus and doesn't change bolo. You can't add an effect system without changing it. They interact." (user, 2026-10-03)

Effects change BoLo's definitions where the two interact. Each unit names those changes, and the obligations that re-establish the borrow guarantees for every program, effectful ones included:
- the fundamental property and adequacy;
- no use after free;
- exclusive mutable borrows;
- lifetimes respected;
- leak freedom;
- no effect feature as a way around borrowing.

## Summary

| # | unit | tier | builds | first unknown |
|---|---|---|---|---|
| 1 | **One signature:** rows as sums, row variables, `raise`, grades, renaming | 1 | item 1 | the grade of a row-variable tail |
| 2 | **Handlers and capabilities:** models, comodels, handler laws over the kernel, stored continuations at `σ = []` | 1 | items 2, 3 | is an answering handler a tail-resumptive `[handle]`? (OQ-1) |
| 3 | **The world `W`:** relativised stop; frame rules and 6.150 at `W`; `vC`/`cC` as `σ = []` | 2 | item 4 | do open frames close on resume, cancel, drop and between lenders? |
| 4 | **Borrows over rows:** one term per printed constant at any well-formed row | 2 | item 5 | can an unrestricted continuation hold a lend? |
| 5 | **Stored lends and async:** stored continuations holding lends, effectful codata, the lead-axis acceptance | 2 | tier 2; acceptance | how a stored continuation holding a lend is bounded (OQ-28) |

Each unit depends on the ones before it. Unit 3's definitions also wait on the OQ-28 probe, because one of its options changes the relation's `U` clause.

## Order

1. **Read the literature.** The foundation is chosen from sources that have actually been read, not recalled:
   - Tang–Hillerström–Lindley–Morris (POPL 2024);
   - *Affect* (POPL 2025);
   - Effekt and System C;
   - Plotkin–Pretnar;
   - Hyland–Plotkin–Power;
   - Ahman–Bauer;
   - Kammar–Plotkin;
   - the hefty-algebra and scoped-effect work.

   This feeds Units 1 and 2, and OQ-60 and OQ-61.
2. **One probe phase for every unit, ordered by risk,** all in `experiments/`:
   1. open frames on resume, cancel and drop, together with a handler between two lenders (OQ-9, OQ-3);
   2. stored continuations (OQ-28);
   3. what `W` holds and its empty-stack instance (OQ-44, 46, 57, 58, 8). In the same batch, decided once: whether a `!` value or an unrestricted continuation may hold an entry of `σ`, with `!`'s outlives rule and 6.60 at stake. Unit 3 owns the definition, and Unit 4 uses it;
   4. the borrow constants at resuming rows: `withswap`'s refold on every exit path (OQ-20), and finalisers at a resuming table (OQ-7);
   5. the async axis (OQ-56, 60, 61, 67);
   6. Units 1 and 2's probes.
3. **Checkpoint 1.** The user sees the outcomes.
4. **The full spec.** Every SPEC entry is written, with open questions boxed, and §19's drift is corrected in E-SIG and E-W. Two definitions change in more than one unit, so each gets one entry, amended in place:
   - **`[handle]`:** Unit 1's premises, Unit 2's carrier and clauses, and the extent OQ-3 may add in Unit 3;
   - **the outlives judgment and 6.60:** `U C` in Unit 2, if OQ-28 picks the outlives form; `!` in Unit 3; `U C` with lends in Unit 5. 6.60 is re-proved at each amendment.
5. **Checkpoint 2.** The spec is agreed.
6. **Then the units, tier 1 first** (OQ-2). Each unit lands its kernel proof, its lowering and its corpus programs, and its done-when includes "the agreed SPEC entry holds as built".

---

## Unit 1: one signature (tier 1)

**Goal.**
- An effect is `{op_i : A_i ↠^{q_i} B_i}`. `raise` is its abortive operations, since errors are a control-flow effect.
- A row is a finite sum of named effects with an optional row-variable tail. `opTable ⟦Σ⟧` is its one interpretation, `F_Σ` its one former, and `[sub]` row inclusion.
- Row abstraction is in the kernel (decision 62).
- The continuation qualifier becomes a grade, as in the Grades experiment.
- Renaming justifies one derivation per site.
- One row function serves the elaborator, checker and backend.

**Changes that touch borrows.**
- **`[let]`'s and `[then]`'s premises** (`S.Weak → Γ₂.Drops`, `S.Unr → Persistent Γ₂`, and the finaliser's abort-only row). Abort-only finalisers stay, expressed as a grade, and OQ-7 may relax them later. They stop an unrestricted continuation copying a `Mut` view, and an affine one dropping owned state or skipping a finaliser.
- **The qualifier's other uses,** which become grades: `contShare`, `KapRel`, the continuation's type, `OpSig.abort`, `cancelOwed` and `[sub]`. `[sub]` on grades must never license dropping a linear continuation.
- **`[handle]`'s premises at a row-variable tail.** The handled row may end in a variable, so forwarding has to be sound at every table that variable can stand for.
- **The law set comes first.** The grade premise is derived from graded algebraicity and linearity, which are fixed in the full spec before this unit lands.

**First unknown.** What grade a row-variable tail carries at `[let]` and `[then]`. A conservative reading ("could be weakening and unrestricted") would force `Persistent Γ₂` on every row-generic `[let]`. "Multi-shot only if free" is the criterion that judges the answer.

**Done when:**
- the rules at sums and row variables are inside `fundamentalC`;
- effect safety and renaming hold;
- a row-generic program runs at parity with its hand-specialised copies;
- **the synchronous half of the no-colouring test passes:** one higher-order function at a row variable, used at the empty row and at an abortive row.

**Open:** OQ-35, OQ-24, OQ-61, OQ-32, OQ-36, OQ-39. Later, for the user: OQ-6 and OQ-55.

---

## Unit 2: handlers as models, capabilities as comodels, laws over the kernel (tier 1)

**Goal.**
- **Handlers and capabilities.** A handler is a model of `Σ`, with `ewp_handle` as initiality. A capability is a comodel of the same `Σ`, run through `withswap` and checked against the same `opTable`. Today nothing checks `withswap` against any table. Answering effects become rows.
- **Build on HandlersAsBorrows.**
- **Unary laws over the kernel relation:**
  - return, operation, forwarding and initiality;
  - the comodel laws;
  - linearity of continuations and the multi-shot condition;
  - the tail-resumptive law and graded algebraicity, which justify the erased lowering classes.

  Whether lowering correctness is a theorem is OQ-23. Fusion and the other equations are binary, and so optional: "optional and don't get pursued unless they become necessary for safety".
- **Cancel and drop** are as SPEC §19 builds them.
- **Stored continuations at `σ = []`.** This is the tier-1 part of OQ-28. The OQ-28 probe chooses the form:
  - a `[gen]` rule, needed because a resource-holding `U C` has no outlives rule today, so `[]I` cannot box a continuation; or
  - an outlives rule at `U C`, which would make the continuation an instance of `[handle]` plus boxing.

  Either way it is stated from the agreed spec entry and law set, not from the `lift-stage1` branch's design. That branch's proved `ewp_gen` is reused as a lemma.
- **Allocation as an effect** (decided): the host handler as a model of the allocation signature, resting on 6.165/6.166. The arena's frame is Unit 4's.

**Failing co-operations raise.** This follows from errors being a control-flow effect. It is derived, not a separate decision. A failing co-operation performs an abortive operation of the lend site's row. The raise happens **after `withswap` has refolded the cell**, using the runner's internal sum, so 6.176's owned payload is never abandoned. It applies at rows that have an abortive operation.

**Changes that touch borrows.**
- **`[handle]`'s clauses and return** are typed at `!` with an empty resource. That is the premise a stateful or capturing clause relaxes, and handler state (decision 59) needs one kernel representation, with use-after-free and exclusivity obligations for state that holds a lend.
- **`[handle]`'s carrier,** under OQ-37.
- **`withswap` as the comodel carrier.**
- **The allocation rules behind the host handler.** No lend into handler-owned memory outlives the handler.
- **The stored-continuation rule.** It is a borrow rule, with these obligations:
  - the body's context and the continuation's argument outlive its bound `@c`;
  - every suspension's resource stays within `@c` (6.62, 6.147);
  - the continuation is called or closed exactly once, and closing it runs §19's cancel.

  Its `σ = []` proof uses T1, so Unit 3 re-proves it at `W`.

**First unknown.** OQ-1: is an answering handler on a lent capability the same protocol as a tail-resumptive `[handle]`?

**Done when:**
- initiality holds;
- the unary laws are proved in their stated directions;
- capabilities cannot perform outside their row or keep state past their borrow;
- the stored-continuation rule, in whichever form OQ-28 chose, is sound at `σ = []` (with 6.60 re-proved under the outlives form);
- the host allocation handler is a model;
- corpus programs run: a map handler at hand-written counts, a capability as a comodel, an answering effect inside a control handler, and a stored generator.

**Open:** OQ-1, OQ-37, OQ-23, the tier-1 half of OQ-28, and OQ-68's host handler.

---

## Unit 3: the world `W` (tier 2)

**Goal.**
- Open lends become a component `σ` of `W = (ρ, ls, σ)`, handed to the table at a stop.
- The relation is re-indexed at `W`, with one order, one monotonicity lemma and arising from `TW`. `vC`/`cC` are its `σ = []` instance.
- 6.64, 6.65, 6.66 and 6.150 are lifted once, by their printed technique.
- The fundamental property and adequacy are proved at every arising `W`, and Units 1 and 2 are restated at `W`.
- T1 becomes a theorem about tier-1 programs. GhostEnd's `vRL*` families are retired into the one relation.

**What happens to each stop conjunct** (`Core/EffDefs.lean:37–40`):
- **`↭` (37)** is relaxed: it is read relative to the closure of `σ'`. It owes 6.48's framing and 6.49's transitivity, and it equals the printed `↭` once `σ'` is closed.
- **`NoOwn` (38)** is kept.
- **`TW`/`Tagged` (39)** are kept. `TW` changes only if a probe requires it (OQ-44).
- **`ps'`/`ls'` preservation (40)** is removed. This conjunct is T1.

Tables, `Ext` (which becomes `⊑`) and how points-to reads a stored payload (OQ-46) change with it. The printed `wpTS` frame rules stay as the `σ = []` instances.

**Obligations, and the first unknowns among them.**
- **Open frames close** on resume, cancel, drop and between lenders (OQ-9, OQ-3). Leak freedom holds at every stop and every cancel.
- **Core's 6.150 variant hypothesis.** `RebChooseTW` is our chooser, not printed. Its dischargers `rebChooseTW_top`, `_deep` and `_pin` quantify over post-worlds with `ls' ≡ ls`. Re-establish them at `W`.
- **Exclusivity at a stop,** over both the 6.65 `mutOf` cell and the 6.66 unfolded owned cell. Entries map injectively to cells, or nest strictly by lifetime. It is proved once, so Unit 4's anti-frame stops are instances.
- **`σ` cannot escape the resource-based checks.** Today every guard against copying or dropping borrowed state reads only the resource `ρ`:
  - `contShare`'s and `KapRel`'s "unrestricted ⇒ empty";
  - the outlives rule for `!`;
  - `Persistent`/`Drops`;
  - `NoOwn` in the tables.

  Each must also constrain `σ`. Whether a `!` value or an unrestricted continuation may hold an entry is decided in the probe phase. This unit defines it, and proves the obligation at the outlives entry.
- **A new lemma: a closed program's final world has `σ' = []`.** With it, `reclaim` and adequacy apply. A handler's value carries no entry whose lender lies inside the handled body.
- **Arising is derived from `TW`,** not stated beside it. That is the remaining work of OQ-45.
- **Core is the `σ = []` instance.** `NilAgreesU` is to be stated. The quantifier placement is settled by stating both candidates in Lean (OQ-8).

**Also here: the two typed worlds.** By default their correspondence is proved at `σ = []` before Core's world changes, so the transcribed 6.151 is the reference.

**Done when:**
- `fundamentalW` and adequacy hold at `W` for every rule;
- the obligations above are proved;
- the frame rules and 6.150 hold at resuming tables;
- T1 is proved for tier-1 programs;
- Units 1 and 2 are restated at `W`, including the stored-continuation rule, whose `σ = []` proof used T1.

**Open:** OQ-9, OQ-3, OQ-44, OQ-46, OQ-57, OQ-58, OQ-8, OQ-54. OQ-54 is the split of `σ` under a fork, stated but not proved, to keep the door open for threads.

---

## Unit 4: one borrow per printed constant over any well-formed row (tier 2)

**Goal.**
- `withbor1`, `withbor2`, `withbor3` and `withload` (6.172–6.175) each become one term, uniform in `Σ`. They are instances of the Shifts schema, each with its printed proof over Unit 3's frame rules.
- The pure rule is the `Σ = ∅` instance, and the `*U` twins become abbreviations.
- `withswap` (6.176) is printed but outside the shift schema. It takes an effectful callback only once its refold on every exit path is proved (OQ-20).
- The slice borrows are ours and get the same treatment.
- A resuming operation may be performed inside a borrow by a continuation that is not stored. Storing it is Unit 5's.
- The arena's frame for allocation goes here, because it needs a handler extent and `W`.

**Well-formed row.** The condition is semantic: the row's table frames under the frame rules (`TableOK`). A syntactic class is only a sufficient condition.

**First unknown.** Does `withswap` refold on every exit path (OQ-20)? Can finalisers run at a resuming table (OQ-7)? Whether an unrestricted continuation may hold a lend is taken from Unit 3's definition. Row variables at a borrow callback are settled with lifetime-polymorphic operation types (OQ-56).

**Guarantees.**
- While a lend is in `σ`, its lender's frame is not exited.
- Operation arguments, answers and the share at a stop lie in the lend's region.
- Neither a continuation nor handler state carries a lend out of that region.
- Finalisers run exactly once, LIFO, on return, unwind and cancel.
- `raise` unwinds through a borrow and returns the cell.

**Done when:**
- the four constants, `withswap` at its rows, the slices and the between-lenders case are inside `fundamentalW`;
- `gen-self-borrow`, `for-lend-resumes`, `yield-callback` and lends across resumed and cancelled operations are accepted;
- each runs at parity with a hand-written state machine.

**Open:** OQ-56, OQ-7, OQ-20, OQ-29, and OQ-68's arena frame.

---

## Unit 5: stored lends, effectful codata, async (tier 2)

**Goal.**
- A stored continuation holding a lend is bounded by a lifetime (OQ-28). That covers a continuation holding a lend of its own frame, and a generator stored in a record holding a lend of its own state.
- The effectful affine closure gets its rules.
- `Loop_Σ` can be observed with a lend open across observations.
- A handler can span observations of a div computation (OQ-67).
- Then the lead-axis acceptance: the async program ("a scheduler written as a handler over state machines") and the asynchronous half of the no-colouring test.

**Changes.** An outlives rule at `U C`, or the `[gen]` rule extended to lends. No resource-holding `U C` has an outlives rule; `!U C` holds nothing. The stored-continuation rule of Unit 2 is the one rule that bounds a `U C`, at `σ = []`. 6.60 is re-proved either way.

**Guarantees.**
- A stored continuation holding entries cannot be resumed after its bound ends.
- A stored `Mut` lend belongs to exactly one continuation.
- Dropping it runs §19's cancel and closes its entries.
- Cancelling a parked queue finalises every task.

**Done when:**
- the stored-lend theorems, the effectful closure, spanning `Loop_Σ` and the spanning handler are inside `fundamentalW`;
- 6.60 is re-proved;
- SPEC entries 13, 20 and 21 are re-checked at `W`;
- the async program, the no-colouring test and `async-borrow.bc` run at parity.

A restriction does not close this unit; an obstruction goes to the user.

**Open:** OQ-28 (lends), OQ-67, OQ-60. The lead-axis options of OQ-61, OQ-56 and OQ-7 also bear on it.

---

## Not in this first pass

| item | why |
|---|---|
| Binary laws and kernel equations, fusion included, with its composite-handler term (OQ-49) | "optional and don't get pursued unless they become necessary for safety" (user, 2026-10-02). TwoRun was considered for them; it does not build on `main`, and nothing here depends on it. |
| Multi-shot beyond what is free | "we also don't need multishot unless we get it for free" (2026-10-02) |
| Higher-order operations | decision 57: out of scope, read as not now |
| Shallow handlers | handlers are deep (decision 62) |
| Threads beyond the split of `σ` | required eventually. The split is stated so the door stays open. |
| Generative instances | deferred, not decided. Decision 57 said "only if the pattern bites" on the Option-2 apparatus that decision 62 superseded. |
| User-facing runners | not user-facing |

## What is retired

| unit | retires |
|---|---|
| 1 | first-match lists; the two row computations |
| 2 | the answering encoding as a second mechanism; EffModelRel and `Core/Handlers.lean` as the laws' home |
| 3 | T1 as a definition; the `wpG` frame copies; the abortive-only frame lemmas, which become instances; GhostEnd's `vRL*` families |
| 4 | the six `*U` proofs; `Row.Unwind` as the callback class; the surface rejections of resuming operations under a lend |
| 5 | the stored-generator restriction |

## Process

- **The hard stop** is not in force while we plan ("There's no hard stop phase now we are just planning"). How it applies once units run is the user's call then.
- **An obstruction** is reported as an elaborating `def … : Prop` or a discharged configuration, whose witness has been checked to arise in `TW`.
- **A unit that cannot meet its agreed entry stops and reports.** Amendments to agreed definitions go back to the user.
- **The compiler is never stale.** Agents gate once, when the unit is ready.
