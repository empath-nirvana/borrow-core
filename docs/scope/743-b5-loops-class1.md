# Scope: #743 B5 (step 1′) — loops as the kernel's `Div`, with class 1, rebuilt from main

Step B5 of #743's build plan, approved by the user on 2026-10-30. This is a scoping note and changes
no code. The build is phase 2, after review.

**Kernel target.** The class-1 kernel rules, rebuilt on main with their proofs:

- a lend held across operations resumed in scope (the handler resumes tail-resumptively, inside the
  lend's world);
- a lend held across a loop's `tick` when the runtime or `div_fuel` drives the loop in scope.

The lemma family is `cwp_lendM`, `cwp_lendI`, `withbor2L_compatX` (with `withbor1L_compatX`) and
`handleT_compatC`. `fundamentalC`, `adequacyC` and `adequacyD` are extended to the changed rules
**with their statements unchanged**, and no `PinLaw` field is used. `CDerivesP` mirrors the changed
premises, so `LendFrame`'s domain grows with them (box Q3, decided). Surface loops elaborate to `Div`
(SPEC §14, *The effect `Div` in the kernel*), so P1–P4's class-1 shapes are typed by those rules.

**Decided, not reopened.**

- #743's plan, B5 row (user, 2026-10-30, "I approve the plan").
- Grades take the M1 shape (user, 2026-10-22, on #654). The world is a lifetime bound on `eff`,
  and replaces #654's `c : Bool`. B5 builds the world axis only, and the larger rework this needs
  is accepted.
- The answers to the first review (boxes Q1–Q9). Q3, `CDerivesP` mirroring class 1, rests on the
  decision that PinLaw's schemas are uniform in depth and holder.
- Written fixes (user, 2026-10-31): a program that should work may be refused only if it has a
  written fix, named in the refusal message, or if a named later step recovers it (section 4).
- Correct over consistent (user, 2026-10-21, on #646): "If we need to refuse we need to refuse."
  Programs that ran only through the elaborator's per-observation lend may move to refused by the
  kernel, each listed. They go to `corpus/pending/`, not `reject/`.
- `imm` is linear with a derived copy (#746 decision 3, 2026-10-29). The checker inserts the copy
  at a split (#756).
- `class1-revive`, `b2-div` (#646) and `call-grade` (#654) are not resumed, merged or
  cherry-picked. They were read for their proofs and their elaboration. Everything below is
  rebuilt from main.

**Sources read.**

- #743: the consolidation (§1–§7), the 10-29 plan, the "Step 1 progress" comment, the 10-30 spike
  and build plan, and `~/repos/scratch-archive/743/plan.md`.
- #644 and #646 with all their comments, including the 10-21 amendments and the 10-31 close.
- #649 and #654 with their comments, including the M1 decision and the 10-31 close.
- `~/repos/scratch-archive/grades-lit/report.md` §2.4 and §5. `~/repos/673-work/design.md` v3 §1.1
  (#673, closed with the abandoned rewriter plan) is read as evidence only.
- SPEC on main: §14 (*Borrow scopes over loops, per observation*, *The effect `Div` in the
  kernel*), §29 (R1 under `PinLaw`), §41, §47–§52.
- On main: `Frontend/Elab/LoopLend.lean`, `Frontend/Check/DerivedCopy.lean`, `Core/Classes.lean`,
  `Core/PinLaw.lean`, `Core/Fundamental.lean`, `Core/DivHandle.lean`, `Backend2/Convert.lean`, and
  `docs/scope/` for the format.
- `call-grade`: `Core/EffLend.lean`, `EffWp.lean`, `EffDefs.lean`, `EffBorrow.lean`, `EffFin.lean`,
  `DivHandle.lean`, `DivRuntime.lean`, `DivPrograms.lean`, `Fundamental.lean`.
- `b2-div`/`b2-main`: `Frontend/Sugar.lean` (the `Div` elaboration) and
  `Frontend/Elab/DivPlacement.lean`.
- `class1-revive`: its merge resolutions, `Backend2/Convert.lean`, `Frontend/Check/ImmCopies.lean`
  and SPEC §62–§66.
- `750a-kernel`: the `git diff --stat` against main, plus `Types.lean`, `EffRules.lean` and the
  pin template.

**Measurements** (read-only, no build). These are `bcc check`/`bcc run` with binaries already
built:

- main: `borrow-core-spec42` at 6d47bf7c. Its Frontend and Backend are identical to 32bbf65d.
- b2-div: ddc1d6de.
- call-grade: about ae50262c.
- class1-revive: built 10-29 from its working tree.

Every B5 result below is a **prediction**: there is no B5 binary.

---

## 1. The kernel rules

### 1.1 What class 1 is in the kernel: premises, not new constructors

#654 added **no `CDerives` constructor**. Its constructor lists are identical to `b2-div`'s:
`CDerives` 96, `CDerivesP` 99, `CDerivesAt` 96. Class 1 is a grade on operation signatures,
together with premise changes on five existing rules. B5 keeps that shape. The brief asks for every
new constructor: there are none. Every changed rule is listed below with its new premise.

`b2-div` changed nothing in `Core/`, `Support/` or `Paper/`. Every kernel part of class 1 is
#654's. Main already has `Div` in the kernel from #567:

- `divEff`, `tickSig`, `iterate`, `div_fuel`, `reify`, `cwp`, `Closing`;
- `effHandleT` and `handleT_compatC` in their ungraded forms;
- `effHandleL` (§51);
- `runtime_every_run` and `divFuel_every_run` at `[tickSig]`.

### 1.2 The grade under M1: the world axis, two points

**Amended (2026-10-31).** The world axis is the two-element lattice `World := op | top` with
`op ⊑ top`. The user approved `{ℓ_op, ⊤}` on 2026-10-22, in #673's consolidated review (comment
6350336829, item 4: "Yeah sounds good"). "M1 world = a lifetime bound" was a stale note, not a user
decision. The phase-2 spike (21363bd9) found that a lifetime bound collapses to the same two
points: decision 71, `docs/decisions.md`.

- `World` (`Core/Types.lean`) has its laws proved: the order is reflexive, transitive and
  antisymmetric with `op` least; the meet; `World.le_iff`.
- `OpSig.wld : World := .top`, and `CTy.eff … (wld : World) C`.
- `Owed en ls ls' ρ` is `Ext ls ls' ρ` at `top`, and the same members at `op`.
- The laws stated with the kernel:
  - the meet a handler's clauses take (`hCN_iff_le`);
  - independence from the count axis (`owed_q_indep`);
  - no world at an abortive operation (`entWld`, `Row.Lend.entWld`).
- `Row.Lend S x`: every non-abortive operation is `op`, `lin`, with closed-data answers.
- B5 builds the world axis only. The count, position, storage and pending-finaliser axes are not
  in its scope.


### 1.3 The changed rules, as built (two-point world)

These are on the branch (`5c2b17b7`, merged with main in `0b9034a0`). The rules differ from main
only in the marked premises.

```lean
def Row.Lend (S : Row) (x : LifeVar) : Prop :=
  ∀ o ∈ S, o.n ≠ 0 ∧ ¬ VFree x o.A ∧ (∀ Δ a, VOutlives Δ a o.A) ∧
    (o.abort = true ∨ (o.wld = .op ∧ o.q = .lin ∧ ¬ VFree x o.B ∧ ∀ Δ a, VOutlives Δ a o.B))

  | divFuel {Δ Γ} {c : World} (S : Row) (A : VTy) (hS : ∀ o ∈ S, o.n ≠ divEff)
      (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val divFuelV) (.val (divFuelTy S A c))                              -- c: new
  | withbor1U … (hS : S.Lend x) …        -- was S.Unwind x
  | withbor2U … (hS : S.Lend x) …        -- was S.Unwind x
  | effHandleT … {c : World} …
      (hCN : c = .op → ∀ o ∈ SN, o.wld = .op)                                             -- new
      (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs rcsNil c ++ S) A))) : …   -- c: new
```

**Rules that do not change:**

- `reify`: its tick is `tickSig`, world `top`.
- `effHandleL`, `effHandleV` and `effHandleVB`: their handled rows are at `top` (`Row.ofEff`'s
  default).
- `iterate`.
- `withbor3U`, `withloadU`, `sliceBorrowMU` and `sliceBorrowIU`: they keep `S.Unwind x`.

**The extended judgments.** `CDerivesP` and `CDerivesAt` carry the same premises. They are
regenerated by `gen-pin.py`; check-hygiene reports them up to date.

### 1.4 The proofs: what was ported

`call-grade`'s proofs were ported with `call : Bool` replaced by `wld : World` (`false ↦ top`,
`true ↦ op`):

- `Owed` (`Ext` at `top`, the same members at `op`), `contShare`/`KapRelT` over it, and the
  conservativity lemmas;
- `OpSig.LeF`/`OpEnt.Le` with `o.wld = .op → o'.wld = .op`, and `FinLe`/`PendLe`/`ThenLe` with the
  same edge;
- `wpG_*_frameAt`;
- `Core/EffLend.lean`: `lendM_frame`, `lendI_frame`, `cwp_lendM/I`, `withbor1L/2L_compatX`;
- `KapRelT.owed` and the graded `handleT_compatC`;
- `divFuel`, `runtime_every_run c`, `runtime_main_every_run`, `io_rt_every_run`.

Main-only users received mechanical edits: `DivHandleLast`, `DeclLend`'s `Sf_unwind.lend`,
`AwaitCancel`, `Classes`, and #750's `then` lemmas. At `op` a stop is owed only at its own
members, so the re-lend in `lendM_frame` needs no locality argument.

### 1.5 The theorems

- `fundamentalC`, `adequacyC`, `adequacyD`, `fundamentalD` and `total_every_run` are textually
  unchanged, and `fundamentalC_pin` keeps its statement.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of them and for every
  ported lemma.
- `runtime_every_run`, `divFuel_every_run` and `runtime_main_every_run` take the world `c`.

---

## 2. The elaboration of surface loops to `Div`

### 2.1 What B5 builds, and what main already has

**On main:**

- the kernel `Div`;
- `TExpr.iterate`, `TExpr.divFuel` and `TExpr.reify` with their `TDerives` cases;
- `effHandleT` and `effHandleL`;
- `bounded_fix` at a resuming row, which Backend2 compiles (§48);
- the old backend's `expandIter`.

**Only on branches, so rebuilt here:**

- the core-text forms `iterate[…]` and `reify[…](res)`, and the `div` row spelling, in
  `Parser`/`Syntax`/`Print`;
- `TTied` emission of `iterate` and `reify`;
- the checker's emission of `handle_tail` and `handle_last` (`effHandleT`, `effHandleL`);
- the elaboration itself (`b2-main` `Sugar.lean:1047`–`:1960`);
- the deletion of `lendBind`, `lentDef` and `Env.lendCall`.

### 2.2 The rule table

There is one rule per construct, over the whole loop grammar of SPEC §14 *The loop node*. A rule
places its sub-terms by the rules for their own constructs and decides nothing about borrows.
There is no fallback and no trial elaboration.

`b2-div` decided whether a body performs `Div` by elaborating it once with a `machine` flag and
restoring the state, and `forYield` did the same with a `tryCatch`. Both are **replaced** by one
judgement, and the `tryCatch` fallback is not ported.

**`div ∈ row(M)`** is read off the row that inference assigns to the body (§14 *Inference and
markers*), computed bottom-up with one clause per construct over the whole grammar:

| construct | `div ∈ row(·)` |
|---|---|
| `while`, `loop` | always |
| `for x in it`, a drain | always |
| `for x in D`, data | `div ∈ row(body)` |
| `for x in g(e)` | `div` is in `g`'s row, or in the clause's work |
| an application `f V` | `div` is in the row of `f`'s inferred type |
| `x <- M; N`, `let`, `case`, `(V, W)`, a borrow block, `[then]` | the union over the parts |
| `with h { M }` | `row(M)` less what `h` handles; no surface handler handles `Div` |
| `λ`, a thunk, a stored generator | `∅`: `div` stays in the value's type |
| a terminal, a variable, a literal | `∅` |

The shapes listed in D0 are examples of this judgement, not its definition.

| # | construct | kernel form | reads |
|---|---|---|---|
| D0 | a div body: `div ∈ row(M)` (above; e.g. a `while`, a drain, a looping generator's `for`, a call at a row holding `Div`) | the body at `F_{tick, Σ}(B ⊕ R)`; a terminal `return v` is `inl v` | syntax, inferred callee types |
| D1 | `while c { M }; N` | `iterate(step, s₀)`. The step is `<turn & close>`. The turn is `case c { false → inl (inl j) \| true → M; inr s′ }`. The close hands back the residual. The state is the variables of `c`, `M` and `N` by name, plus the held sources and capabilities | names in scope, their inferred types |
| D2 | `loop { M }; N` | D1 without the test. The join type is `0` when there is no `break` | as D1 |
| D3 | `for x in it`, over an iterator or a stored generator (a drain) | `iterate` holding `it`; the turn observes `it.1`, the close is `it.2` | the source's inferred type |
| D4 | `for x in D`, over data: a count, a view `fam (imm/mut)`, `&a`, an owned array of a persistent type, a sized iterator, or `imm 'a (array A)` / `mut 'a (array A)` (see D4′) | body with `div ∉ row(body)`: today's total counted loop (§16), unchanged. Body with `div ∈ row(body)`: `bounded_fix` at the row `div, Σ` (#646 amendment: "a counted loop with `Div` in its body is `bounded_fix` at the row"). A lend around the source is held across the ticks, and the kernel decides | the source's type |
| D4′ | `for x in v` with `v : imm 'a (array A)` (or `mut`) | a reborrow through `withload` (the existing `borrow imm *v { 'y, w -> … }` sugar, `Sugar.lean:3760`) to the view `array_imm 'y A`, then D4 over the view. When the body does not tick, no lend crosses a tick. When it ticks, `withloadU` stays `Row.Unwind` and the kernel refuses | the source's type |
| D5 | `for x in g(e)`, over a generator | `handle_tail` (`effHandleT`) when every exit resumes and nothing raises; otherwise `handle_last` (`effHandleL`, §51), around `g`'s direct call. A clause whose work has `div` in its row is a div body of its own (D0). The loop's state is threaded through the clause's answer, so **the operation's signature carries the consumer's state** (`x × ws ~> ws`). This choice is forced by the kernel rule, not by the language: `effHandleT`'s clauses are closed values (`Hr.ValFormIn Γ₁`, `Hc.ValFormIn Γ₁`, `Ctx.DeadP Γ₁`), so the loop's live variables can reach the clause only through the operation. A generator's signature therefore depends on its consumer, which is why `makeInst` makes one instance per use, with or without borrows (box Q8). When the state holds a borrow, that signature mentions a lifetime, and decision R (one closed signature per operation, `Core/Tied.lean`) refuses it. That refusal is the kernel's and is listed in 4.2. D5 never threads the owner in place of the borrow: that is the per-observation lend | the clause's exits (syntax) |
| D6 | a direct-style call of a div function | inlined at the caller's row: the call, then `case inl/inr`. On `inr`, close what is held and leave with the residual (D9) | the callee's type |
| D7 | a loop used as a value (`U(Loop B R)` expected) | `reify_res[B, R, Σ](res)(thunk M)`, with `res` the closed residual function | the expected type |
| D8 | `main` that loops | `main`'s own core form, run by the runtime (`rtMain`, `Core/DivRuntime.lean:418`) at `tickSigW c`, with its own server id. It is not `reify`, whose tick is at `top`. The body runs in place, and `c` is the world §2.3's solve gives the runtime's server (the runtime accepts both) | `main`'s inferred row |
| D9 | `break`, `continue`, `return` | `inl (inl j)`, `inr s′`, `inl (inr a)`, each after closing the held sources, innermost first. The residual hands back **exactly what the loop holds, by name**. `b2-div`'s `eAbort` matched capabilities by type (`capOf`); that is not ported (box Q6) | names |
| D10 | a borrow block whose body is a div body; `let r = &x` before a loop; a lend at a direct-style call of a div function | the kernel's lend (`withbor1U`/`withbor2U`, or the slice/`withbor3U`/`withload` forms) with its callback a div body at the enclosing row. The elaborator neither splits it per turn nor refuses it. The kernel accepts (`Row.Lend`, class 1) or refuses (`Row.Unwind`) | the place's type |
| D11 | loops inside handler clauses and effect bodies | D0–D10 at the clause's row. A `[handle]` around a ticking computation is `effHandleT`/`effHandleL` only (§14) | — |
| D12 | an `imm` borrow used at every turn | threaded by name in the state (D1). Each turn is a split between the body's use and the back edge's `inr s′`, and #756's rule inserts the kernel copy there (section 3) | — |

**Tick placement (decided, box Q5).** Ticks are the ones the kernel rule fixes: `iterate`'s own
back-edge ticks (§14), and no others. `b2-div`'s forward placement (a tick at every move to a point,
plus one before a terminal reached before any point, #644 step 0) existed to match the old machine's
observation counts, and it is not ported. Section 4.5 lists the measured effect on outputs.

**World (box Q2): one component of the elaborator's row inference** (§2.3). The elaborator writes
every operation's world in the core text; the checker reads it and the kernel re-checks it.

### 2.3 World inference (Q2 resolved: route 4)

**Decided (user, 2026-10-31, route 4).** The world is a component of the elaborator's existing
effect-row inference: SPEC §18 (a function's inferred row; a written row is a promise checked
against it) and §38 (rows inferred with types). It is solved with the rest of the row. The
inference decides no guarantee: the kernel re-checks every world. `Div` in rows (B2) and `Alloc`
(#763) are to be inferred the same way, so the world is designed as one more row component, not a
world-specific mechanism. This reverses option (A) of box Q2, inference inside the checker. That
checker's `CRow` is the kernel `Row` at a closed `World`, so it can hold no metavariables.

**What the row inference is today** (`Frontend/Elab/Effects.lean`).

- A function's row is a `List Inst`, one entry per effect instance (effect, type arguments, name).
  It is computed by a bottom-up walk over the surface term (`rowV`/`rowC`, `:727`–`:820`), with
  union (`Env.addInst`/`Env.union`, `:577`–`:607`). There are no row variables and no unification.
  It runs per definition, in declaration order, and per recursive group (`defineGroup`).
- A written row is a membership check (`Env.checkWritten`, `Env.slotOf`, `:3464`–`:3505`,
  `:3986`–`:4010`).
- **Rows are polymorphic by copies, not schemes.** A function with a row is elaborated once per
  assignment of its slots to what serves them (`copyFor`, `:2950`). A copy is keyed by the static
  site names that serve it (`copyName f ["n3", …]`), and a block by its sites (`blockKeys`,
  `:1472`). This is `[let-poly]`'s premise term (SPEC §24): terms carry no rows.
- The copy's kernel row is written as `Row.cons n i q A B` (`Env.rowOf`, `:504`;
  `Frontend/Syntax.lean:190`–`:192`). Core text has no `wld`, `fin` or `rc` field: `elabRow`
  (`Frontend/Check/Elab.lean:401`–`:412`) fills in `fin = ret unit`, `rc = false`, `wld = top`.

**Servers.** A **server** is what serves a slot: a control handler site, `main`'s runtime, a
`reify`, or a `div_fuel`. Each has a static **server id** from the one counter `freshSite`
(`Effects.lean:333`). The id is separate from the kernel operation's name. A control site's id is
its site name `n`. The `Div` tick has one kernel name (`divEff`), and its servers each get an id of
their own. Copies are keyed by server id (`n{id}`), as they are keyed by site name today.

**The world is one attribute per server.** Every kernel premise that fixes a world fixes it for a
whole site:

- `Row.ofEff n E 0 fs rcsNil c` gives every operation of the site `n` the one world `c`;
- `effHandleV`/`VB`/`L`'s handled rows are at `top`;
- `Row.Lend` leaves an abortive operation free (`entWld`).

So the world rides on the per-server copies, and **control sites need no schemes**. `for_each(f)`,
used once under a lend served by site 3 and once under a `handle_last` at site 5, gives the copies
`for_each__n3` and `for_each__n5`, each at its own site's world.

**Which lend form a borrow block takes** (one syntactic rule, replacing the order in
`Sugar.lean:4229`–`:4262`, where R1 is tried first). Let `r` be the block's row (narrowed below).

- **Class 1** (`withbor1U`/`withbor2U`, `Row.Lend`) when every non-abortive operation of `r` is
  `lin`, unmarked (`rc = false`), and served by a server whose emitted form accepts `op`
  (`handle_tail`, `main`'s runtime, `div_fuel`).
- **R1** (`withbor2r`, §29) otherwise, for a `mut` borrow of a `ref` cell.
- **Class 1** otherwise. The kernel refuses it: message R at a non-`lin` operation, W-L at a
  server that needs `top`.

*Why this rule.* Each premise it reads is syntax: the qualifier and the mark are the operation's
declaration, and the server's form is what the elaborator emits (the form condition, below). Class 1
is the stricter mode where it applies: it admits ticks, abortive operations, answers other than `1`
and uses of the context outside the view, all of which `Row.ResumeO`/`ResumeOC` and R1's closed
callback refuse. R1 is the mode for a suspension: a marked wait, a cancellable resumption, or a
server that stores `κ` (BOXED-κ), which class 1 can never accept. Neither mode's other premises are
read: the kernel checks them.

**Narrowing `r`.** `r` is the enclosing row narrowed per operation `(n, i)` to what the block's body
performs, by §2.2's row judgement (the one that gives `div ∈ row(·)`): λ, thunks and stored
generators are `∅`, an application performs its callee's row. One function computes it for both
uses. It replaces `opsC` (`Sugar.lean:4229`), which counts λ and thunk bodies, narrows by site
rather than by operation, and is fuelled; keeping `opsC` would be a second copy of the judgement,
and it over-forces.

**When a handler is `handle_tail`** (the T rule, syntax; the strictest mode that works). A control
`with` is emitted as `handle_tail` (`effHandleT`, `tailTuple`) when:

- every clause of a non-abortive operation resumes `κ` once, in tail position, on every path (the
  shape of SPEC §18's *A resume in every arm*), and the elaborator writes the clause as its answer;
- every operation its clauses perform is `lin` and not abortive (`hLin`);
- the handler has no state (§21): `effHandleT`'s clauses are closed values (`Hr.ValFormIn Γ₁`,
  `Ctx.DeadP Γ₁`). A handler with a `mut` parameter is state-passing and is not T until box Q8's
  route (ii);
- whether or not the body ticks.

Otherwise it is `handle` (`effHandleV`, or `VB` at `boxK`), or `handle_last` by D5. The T rule
replaces no checker classification: `effHandleT` has no `κ` to classify, since its rule writes the
resume.

**The constraint table, keyed by the form the elaborator emits.** `world(s)` is the world of the
server `s`, under the order `op ⊑ top`.

| form emitted (where) | kernel premise | constraint |
|---|---|---|
| a class-1 lend `withbor1U`/`withbor2U` at the narrowed row `r` (`Const.unwinding`, `Frontend/Sugar.lean:3144`; emitted at `:3804` and the other `cbRowed` sites `:3793`–`:4007`) | `Row.Lend r x` | `world(s) = op` for the server `s` of each operation of `r` that is non-abortive and `lin`. A non-`lin` operation forces nothing: its server stays `top`, and `Row.Lend` refuses with R |
| the relaxed lend `withbor2r` (R1, `Sugar.lean:3184`–`:3191`) | `ResumeOC` (after #750 A) | none: its row's own premises |
| `withbor3U`, `withloadU`, the slice borrows | `Row.Unwind` (every operation abortive) | none: a resuming operation is refused whatever its world |
| `handle` with plain or boxed `κ` (`effHandleV`/`VB`; `boxK`, `Effects.lean:2525`; `hndCtlC`, `Sugar.lean:4445`) | the handled row at `top` | the site needs `top` |
| `handle_last` (`effHandleL`; D5) | the handled row at `top` | the site needs `top` |
| `handle_tail[n @w]` (`effHandleT`; the T rule) | the handled row at `c`; `hCN : c = op → ∀ o ∈ SN, o.wld = op` | `world(n)` free; the edge `world(n) = op ⇒ world(m) = op` for each server `m` of `SN` (what the clauses perform). `c` is written on the node |
| `reify` (D7) | `tickSig` at `top` | the server needs `top` |
| `main`'s runtime (D8: its own form, `rtMain`, `Core/DivRuntime.lean:418`, at `tickSigW c`) | `runtime_every_run c` | `world` free |
| `div_fuel` | `divFuelTy … c` | `world` free |
| everything else | — | none |

Abortive operations of a site take its world too. Every rule is unconditional or keyed by a
syntactic fact (the form, `OpSig.abort`, `q`, `rc`), so the system is Horn. `[sub]` needs no edges:
every occurrence of a server's operations carries one world, so `rowLeB`'s exact comparison
(`Frontend/Check/Decide.lean:857`) stays correct. The cancel-row edges (`FinLe`, `ThenLe`,
`LastFinOK`) are vacuous here: core text writes no cancel row, and the checker builds only
`finsNil`.

**The solve.** It runs once, after Sugar, over the program:

1. the forced set: every server some class-1 lend forces to `op`;
2. closed along the `hCN` edges;
3. each forced server whose form needs `top` recorded as a conflict, with its path. Nothing is
   refused here;
4. the rewrite: every `Row.cons` of a control site `n` gets `world(n)`; every tick entry gets the
   world of the `Div` server whose scope it is in (each copy serves one server, and a `reify`,
   `div_fuel` or the runtime opens its scope); each `handle_tail` node gets `@world(n)`, which the
   checker's T producer reads as `c`; every other entry is `top`.

At a conflict the forced `op` is still written. The kernel premise then refuses:
`effHandleV`/`VB`/`L`'s handled row at `top`, or `reify`'s `tickSig`. **The elaborator refuses
nothing**, so it decides nothing even where the solve is not principal.

The solve is principal for control sites, by this argument: only a server's own form forces `top`,
and `[sub]` moves only `top → op`. So a uniform world per server is accepted exactly when the
kernel's minimal solve is (phase-2 check, below).

**The messages.** The checker's refusal at the handle or `reify` node is the message. The solve's
path is attached to it as a diagnostic, as `renderError` attaches a sugar's origin
(`Frontend/Elab/Pipeline.lean`): the lend, each copy hop (from the `.copy` keys: "through `f`,
called at L3"), each `hCN` edge ("through the clauses of `g` at L4"), and the server.

- **W-L**, at `effHandleV`/`VB`/`L`: "the lend of `x` at L1 is held across `op` at L2 (the site of
  `h`), whose handler is a general handler (`[handle]`): end the borrow before `op`, or move it
  inside the handled body below `op`." The fix "resume in tail position in `h`" is added only when
  `h` meets the T rule except for its clauses' shape. Fix **(a)**.
- **W-R**, at `reify`: "the lend of `x` at L1 is held across the loop's turns at L2, whose stop is
  stored by `reify`: lend inside each turn, where the consumer drives the loop." Fix **(a)**;
  **(b)**, recovered by B7, for a stored generator's self-borrow.
- **R**, a lend across a resuming operation that is not `lin`, is not a world conflict.
  `Row.Lend` asks `q = lin`, and the refusal is the checker's (4.6's message R). `effHandleL`'s
  operations are cancellable or abortive, so a lend across one is R, not W-L.

**`Div` (component-generic).** `Div` is a row slot like any control effect: §2.2's `div ∈ row(·)`
table is its entry inference, and its servers (the runtime, each `reify`, each `div_fuel`) have
server ids in the copy keys. A div function called both inside a `reify` and across a lend in
`main` is two copies, each at its server's world. Without the ids, one world per `divEff` name
would conflict where the kernel accepts. **Div-alt**, a world per definition with `rowLeB` deciding
`OpSig.LeF` (`rowLeB_sound`) and `[sub]` at each call, is a second mechanism. It is not built. If
server ids turn out to be more than a slot in the copy keys (the D6 call, D9's residual and D7's
`res` keyed per server), that is reported, with Div-alt beside it, before anything is built.

**The form condition.** Every form the table keys on is one the elaborator writes:
`handle`/`handle_tail`/`handle_last` (`tailTuple`/`lastTuple`, SPEC §51), `reify`, `main`'s runtime
form, and the lend constants. The elaborator never predicts which kernel rule types a node: it reads
the form it emitted. If the checker ever has to classify T or L out of a plain `handle`, or main's
form out of a `reify`, the elaborator would have to re-derive it. That is a STOP.

**The generic part.** B2's `Div` and #763's `Alloc` take the same shape:

- server ids from one counter, separate from kernel operation names;
- an attribute slot on core-text `Row.cons`;
- attribute = f(server), so it rides on the per-server copies;
- a constraint table keyed by emitted form;
- one Horn solve per program, with span paths;
- the rewrite by server scope.

This is the slot B2 and #763 need. Only the order `op ⊑ top`, the forcing table and the lend-form
rule are world-specific. `Div`'s presence in a row is an entry, inferred by §2.2, not an
attribute. Whether `Alloc`'s operations reach kernel rows (control) or stay capabilities
(answering) is not checked; if control, the world rule applies unchanged.

**The kernel re-checks every world.** The inference decides no guarantee, and a wrong solve is a
refusal, never unsoundness. These rules catch it:

- `Row.Lend` at `withbor1U`/`withbor2U`;
- `effHandleT`'s `hCN`;
- `effHandleV`/`VB`/`L` at `c = top`;
- `reify`'s `tickSig`;
- the runtime and `div_fuel` theorems, stated for both worlds;
- `RowLe` in `[sub]`, `hSN`, `hMS`, `hDS`, and decision R (`sigsOkB`, `Frontend/Check/Tied.lean:691`)
  on worlds nested in signatures.

**Cost and files** (about 650–900 lines).

| file | change | lines |
|---|---|---|
| `Frontend/Syntax.lean:190`–`:192`, `:919`; `Frontend/Parser.lean:780`–`:790`; `Frontend/Print.lean:133`–`:134`; `Frontend/Elab/{Subst:66,Respan:76,RenameLife:74}.lean` | a world on `Row.cons` (written `@op`; absent = `top`), with its parse, print and traversals | 40–60 |
| `Frontend/Elab/Effects.lean:504`–`:507`; `Frontend/Sugar.lean:3137`–`:3141` (`surfRow` drops `wld`) | carry the world | 10–20 |
| `Frontend/Check/Elab.lean:401`–`:412` | `elabRow` reads the written world instead of `top` | 5–10 |
| `Frontend/Check/Steps.lean:541` | **trap:** `effRow?` rebuilds each `OpSig` with `.top` and drops `wd`; it must keep it, or the world is lost silently | 1–5 |
| `Frontend/Elab/Effects.lean` (`copyFor`, `blockKeys`, `freshSite`) | server ids for the runtime, `reify` and `div_fuel`; copies keyed by them | 60–100 |
| `Frontend/Sugar.lean:4225`–`:4262` | the lend-form rule; narrowing by §2.2's judgement in place of `opsC` | 60–100 |
| `Frontend/Elab/Effects.lean`, `Frontend/Sugar.lean` (`hndCtlC`) | the T rule: the clause shape, `hLin`, no state; the clauses written as answers into `tailTuple` | 100–150 |
| `Frontend/{Syntax,Parser,Print}.lean`, `Frontend/Check/Checker.lean` | `handle_tail[n @w]` carries `c` and the T producer reads it (the producer itself is §2.1's work); `main`'s runtime form at `tickSigW c` | 40–60 |
| `Frontend/Sugar.lean` (the class-1 lend sites, `hndCtlC`, D5/D7/D8's emission) | record each constraint at the form it emits | 80–120 |
| `Frontend/Elab/Worlds.lean` (new) | the store, the `hCN` closure, the conflicts and their paths, the rewrite by server scope over the program (no generic Row traversal exists; `Subst.lean` is the model) | 250–350 |
| `Frontend/Elab/Pipeline.lean` (`renderError`) | the path attached to the checker's refusal | 10–20 |
| `corpus/reject/` | `world-lend-handleL.bc` (W-L), `world-lend-reify.bc` (W-R), `world-lend-cancel.bc` (R) | — |
| `corpus/` | `world-poly-for-each.bc`: the copies case, accepted | — |

**Tempting shortcuts, and the STOP each raises.**

| shortcut | STOP |
|---|---|
| Default every operation to `op` | **PRINCIPLED**: refuses every `effHandleV`/`VB`/`L` and `reify` program |
| A per-handler or per-effect special case | **KERNEL WORK** |
| Refuse a conflict in the elaborator | **KERNEL WORK**: write the forced `op`; the kernel premise refuses |
| Predict which kernel rule types a node (T or L from a plain `handle`, main's form from a `reify`) | **FORM**: a second copy of a typing rule |
| Choose the lend form by a premise the kernel checks (closed-data answers, outer uses) | **KERNEL WORK**: the rule reads `q`, `rc` and the server's form only |
| Keep `opsC` for narrowing beside §2.2's judgement | **PRINCIPLED**: two copies of one judgement |
| A pre-pass with its own typing rules, or worlds inferred inside the checker | **Q2**: route 4; the world is a row component |
| A retry or fallback solve | **PRINCIPLED**: one principal solve |
| Skip the kernel re-check | **KERNEL WORK** |
| One world per `divEff` name | **PRINCIPLED**: spurious conflicts between `reify` and the runtime; `Div`'s servers have ids |

**Effect on the acceptance list (section 4).** The predictions that change are listed in 4.3 and
4.4 (rows marked *2.3*): the R1/class-1 rule, the retirement of the elaborator's lend refusals
(2.5), and the messages, which are now the checker's with the solve's path. `world-poly-for-each` is
accepted by copies. Phase 2 measures every program in 4.1–4.4 again and lists any difference.

**Phase 2 checks these first** (not verified in the feasibility check):

1. Server ids are unique across all copies in one run (one `St.site` counter).
2. §2.2's judgement, per `(n, i)`, gives each lend's `r`; no lend is emitted at the full enclosing
   row.
3. Narrowing: a lend never forces a server whose operations its body does not perform.
4. How D5–D8 emit `handle_tail`, `handle_last`, `reify` and `main`'s form: distinct forms (the form
   condition).
5. Principality: a uniform world per server is accepted exactly when the kernel's minimal solve is.
6. R1's closed callback and its exclusion of abortive operations are premises of the kernel's R1
   rule (`LendForm`, `Row.ResumeOC`), so retiring the elaborator's checks (2.5) leaves the kernel's.
7. Which corpus programs take R1 today with only `lin`, unmarked operations served by an
   op-accepting server; under the rule they take class 1.

### 2.4 What it reads

The elaboration reads the syntax and the types that inference gives (`TCx`). It reads no borrow,
lifetime or linearity judgement, and makes none. Every such judgement is the checker's, made on the
core term that the elaboration emits.

The brief says "checked facts only". No pipeline exports checker facts to the elaboration: inference
runs before checking, on every branch. Box Q7 covers how this scope reads that requirement.

### 2.5 What retires

The per-observation lend in `Frontend/Elab/LoopLend.lean` retires. That code is kernel work done in
the elaborator: it decides each lend's extent per turn.

- `lendBind` (`:388`): splitting a borrow block per stretch and per `for` body.
- `lentDef` (`:495`): rewriting a div function over a borrow to take its owner.
- `Env.lendCall` (`:257`): rewriting `f(b)` to `f(&t)`.
- The error sites `iterError` (`:297`, `:342`) and the rename check (`:424`), with `lentDef`'s
  refusals (`:518`).

What stays:

- `lendLet` (`:439`), `let r = &x; S` as `borrow imm x { r -> S }`. It is used by programs with no
  loop.
- `escapeError` (`:290`), which every borrow block reuses (`Sugar.lean:3777`–`:4009`).

LoopLend shrinks to about 140 lines.

Also retired:

- The per-body `unfold` state machine for loops (`mWalk`, `mLoop`, `divMachine`, `divBody`). It is
  replaced by D0–D9.
- `forDataDiv` (`Sugar.lean:4935`), now D4.
- `io_hwf` (`:5197`), now D5.
- The spine rule S1 (`Sugar.lean:156`): a `while` is no longer confined to the spine, because a
  loop is a term, not a machine state.
- The refusal of `&a` or an owned array with a resuming body (`:4566`–`:4574`, `:4931`), now D4 and
  D10: the kernel decides.
- The refusal of a borrow block whose body performs a resuming operation ("only an abortive
  operation crosses a borrow's scope", #172; `Sugar.lean:4257`–`:4259`). It is an elaborator refusal
  on borrow grounds, and `Row.Lend` with the world (§2.3) now decides it. The block takes the form
  §2.3's lend-form rule gives.
- R1's elaborator refusals: an abortive operation beside a resuming one (`:4236`–`:4239`) and a use
  of the context outside the view (`:4251`–`:4254`). Each restates a premise of the kernel's R1 rule
  (`Row.ResumeO`/`ResumeOC` admit no abortive operation but the cancel target; `LendForm`'s callback
  is closed), so the kernel refuses the same blocks (phase-2 check 6 of §2.3). Under §2.3's rule a
  block with only `lin`, unmarked operations of op-accepting servers takes class 1, where neither
  premise exists.

  *Programs whose acceptance or message changes* (4.3, 4.4): `reject/state-across-borrow` (still
  refused, by the checker at `effHandleV`, W-L's path attached), `reject/gen-self-borrow` (still
  refused, by R), `reject/async-r1-raise-across` and `pending/async-bank` (still refused, by the
  kernel's R1 premises; `-- expect:`/`-- now:` change), and the R1 blocks phase-2 check 7 lists,
  which take class 1. P1's acceptance (4.3) depends on the #172 retirement, through D10.

**Docs made stale and edited:**

- SPEC §14, *Borrow scopes over loops, per observation*, and its *Elaboration* and *One state
  machine per body*.
- `Core/PinDerives.lean:17` and `:531`, which describe R2 as what "Core's elaboration (`LoopLend`)"
  requires. These are doc comments in a generated file. Box Q3 covers them.
- `lib/lend.bc:12`.

`lib/lend.bc`'s library (`loop_lend_*`, `pull_lend_*`, `array_each_imm`) is user code over
`unfold`, and stays.

---

## 3. The `imm` re-read at each turn

`iterate`'s step is `!U(S ⊸ …)`. `bangThunkV` asks every live slot to be `!A` (`Ctx.Banged`), and
`imm` is not persistent (`Core/Persistent.lean:49`). So an `imm` borrow cannot be a free variable
of the step, used again at each turn. It is threaded in the state, D12:

1. The turn binds it by name from `s`.
2. The body uses it, and the back edge `inr s′` mentions it again. Those are the two parts of a
   split.
3. #756's rule (`Frontend/Check/DerivedCopy.lean`, `Env.copyVars`) fires at that split and inserts
   `copyE`. The result is a `CDerives.copy` node at `Imm @a A` (or `CDerives.arrCopy` under
   `bangE` at `[Imm @a A]`) in `copy_derives`' shape (`Core/Classes.lean:342`).
4. The close component shares the turn's context: `&` is additive, so there is no split there. It
   drops the borrow by its derived drop: `imm` is `Forgettable`, `OwnFree ∧ HasDtor`
   (`forgettable_iff`, `Core/Classes.lean:390`).

So every copy is a rule node that `CDerives` licenses. The checker decides where it goes, by the
split's masks, and the elaborator inserts none.

`DerivedCopy` (`Core/Classes.lean:313`) is exactly:

```lean
inductive DerivedCopy : VTy → Prop where
  | imm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.imm a A)
  | arrImm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.fam (.imm a A))
```

It holds for every `A`. The `imm` borrow of a declared (`Tok`-owning) value is therefore
`DerivedCopy`. Copying it copies the borrow, not the owned value: #746 decisions Q11, "borrows of
declared types stay copyable".

A **pair** holding a borrow is not `DerivedCopy`. An example is `reject/lend-escape`'s
`q : imm 'x array i32 ⊗ i32`. Such a pair stays refused at the split. Widening `DerivedCopy` is a
kernel change, and is not in B5 (`746-imm-copy.md` §4).

> **STOP (linearity).** Stop on anything that makes a value copyable or droppable that was not, or
> that weakens a linear or owed obligation. B5 adds no copy, no drop and no persistence. A copy
> appears only where #756's rule fires, at `DerivedCopy`, and the kernel checks it.
>
> This was E1's failure on `class1-revive` (commit 4ad53247, `Frontend/Check/ImmCopies.lean`). E1
> was a source rewrite before checking (`Val.copyImm`, renaming to `x#d.i`). It copied an `imm`
> binder that the program had declared with `linear x <- M`, and let the copies drop.
>
> On main, the binder `linear x <- M` is gone (SPEC.md:10439), and the copy is a node of the typed
> term. If any program needs a copy that #756's rule does not insert, it is refused and listed in
> section 4. It is never repaired.

---

## 4. Programs whose acceptance changes

**Mechanisms:**

- **K-lend**: class 1 accepts a `withbor1U`/`withbor2U` lend whose callback ticks, or performs, at a
  row where the world bounds the lend: driven in scope by the runtime or by a tail-resumptive
  `effHandleT`.
- **K-copy**: the `imm` re-read is #756's derived copy (section 3).
- **K-unwind**: a lend that stays `Row.Unwind` refuses a tick in its callback. These are the slice
  borrows (`&a` of an array, `borrow mut a` of an owned array, a buffer or literal's view),
  `withbor3U` and `withloadU`.
- **K-sig**: decision R, one closed signature per operation (`Core/Tied.lean`; SPEC §19).
- **D-elab**: the `Div` elaboration with no lend involved.

The "main" and "branch" columns are measured. The "B5" column is predicted, with
`borrow-core-spec42`'s binary for main (its Frontend and Backend are 32bbf65d's), and with b2-div's
and class1-revive's binaries.

**The written-fix rule** (user standing rule, 2026-10-31): a program that should work may be refused
only if it has a written fix. Each refusal below says one of:

- **(a)**: the fix available today, which the refusal message must name. The message text is given
  in 4.6.
- **(b)**: no fix until the recovery step. **⚑** marks a (b) that is an ordinary-looking loop.

### 4.1 Accepted on main, accepted under B5 (the mechanism changes)

These seven ran through LoopLend's per-observation lend. With the four programs in 4.2 they are
#646's set of eleven (the twelfth, `lend-div-iter`, is `sugar/lend-div` in 4.2). class1-revive
measured each of the seven on main's file.

| program | main | class1-revive | B5 | mechanism |
|---|---|---|---|---|
| `corpus/axes/borrow-across-loop` | i32[60] | i32[60] | i32[60] | K-lend + K-copy |
| `corpus/hygiene-borrow-loop` | i32[207] | i32[207] | runs | K-lend + K-copy |
| `corpus/lend-mut` | i32[604] | i32[604], Backend2 native | runs | K-lend (`mut`, no copy) |
| `corpus/lend-server` | i32[65] | i32[65] | runs | K-lend at the call + K-copy |
| `corpus/lend-shadow` | i32[105] | i32[105] | runs | K-lend + K-copy |
| `corpus/sugar/lend-block` | accepted | accepted | accepted; `.core.bc` rewritten | K-lend + K-copy |
| `corpus/sugar/lend-let` | accepted | accepted | accepted; `.core.bc` rewritten | K-lend + K-copy |

### 4.2 Accepted on main, refused or at risk under B5 (new refusals)

| program | main | class1-revive | B5 | why | fix | recovered by |
|---|---|---|---|---|---|---|
| `corpus/lend-copy` ⚑ | runs | refused 37:3: `borrow mut a { … while … }` over an owned array holds its lend across the tick | **refused** → `pending/` | K-unwind (slice) | **(a)** lend inside each turn: `while c { borrow mut a { 'x, v -> … } }` (message U) | **B2** W-tick (`lendRT`) at `LendForm` fam |
| `corpus/lend-pipeline` | i32[361] | refused 39:1: "operation 1.0 has two signatures" | **refused** → `pending/` | K-sig; cause below | **(a)** move the borrow into the body: `let v = borrow imm t { b -> get(b, x) }`. **Measured**: `lp-r1.bc` prints i32[361], `live 0`, on main's and class1-revive's binaries (message S) | no plan step; needs lifetime-polymorphic `Ξ` (box Q8) |
| `corpus/lend-config` | runs | refused 40:3: "`stdin` is not consumed in its scope" | **at risk** | class1-revive's close did not hand back the lent capability. Under D9 (hand back by name) it is expected to run | if refused: **(a)** borrow at each use instead of once: `for c in bytes(&mut stdin) { acc = scale(&config, …) }; cap(&config, acc)` (message U′) | B5 itself, by D9 as a rule; otherwise a listed refusal |
| `corpus/lend-div`, `corpus/sugar/lend-div` | runs / accepted | refused 42:7: "expected `i32`, but this has type `i32 + 1`" | **at risk** | class1-revive §62: a borrow block whose body is a direct div call was not typed at `B ⊕ R`. D10 composed with D6 places it at `B ⊕ R` | if refused: **(a)** bind the call's result inside the block, then return it | B5 itself, by D6/D10; otherwise a listed refusal |

**lend-pipeline's cause** (diagnosed from class1-revive's `bcc desugar`; the scratchpad files are
cited in the report):

1. D5's push elaboration threads the `for` site's state through the operation's answer:
   `x × ws ~> ws`.
2. With LoopLend gone, `ws` holds the borrow itself (`imm 'io_l5 array i32`). Main's LoopLend held
   the owner, `ref array i32`.
3. The generator is a generic instance, and §15's `makeInst` (`Sugar.lean:6257`–`:6305`) gives it
   its own lifetime binder `'io_q0`. So its `perform` is at `'io_q0`, while `main`'s handler is at
   `'io_l5`.
4. `sigsOkB` (`Frontend/Check/Tied.lean:691`) then reports one operation with two signatures
   (`Program.lean:156`).

This is **not a checker bug**. Instantiating the definition's signatures at the use's lifetime would
still leave a signature that mentions `main`'s lifetime, and decision R requires a closed one. So it
is an existing rule refusing what D5's threading produces. `pending/state-machine-audit` is the same
case: the handler capability `mut 'fx_l_audit …` is threaded, and class1-revive and b2-div refuse it
at 91:1.

### 4.3 Refused on main, accepted under B5

| program | main | branches | B5 | mechanism |
|---|---|---|---|---|
| **P1** `scratch-743/t/p01-while-handler-op` | refused 3:1 (`escapeError`, the per-observation rewrite) | class1-revive: i32[20], Backend2 native | **accepted** | K-lend: `&mut c` is lent across `walk`'s ticks (the runtime, at `op`) and `count`'s tail-resumptive `tick()` (`effHandleT`, `c = op`) |
| **P3** `scratch-743/t/p05-iter-borrowed-vec` | refused 20:12 (`iterError`) | class1-revive: refused 20:24, "`*` … has type `1`" | **accepted**, i32[6] | D4′ (decided in scope): `imm 'a (array i32)` was not data (`dataSrcOf`, `Sugar.lean:2633`), so it fell to the drain path and `x` got type `1`. The loop is total, so no tick crosses the lend; copies go only through #756's rule |
| `reject/lend-iter-borrow` | refused 28:5 (`iterError`) | class1-revive: i32[60] | → corpus | K-lend + K-copy |
| `reject/while-in-counted-for` | refused 10:5 (S1) | all three: i32[4] | → corpus | D-elab (S1 retired) |
| `reject/for-data-gen-loop` | refused 15:19 (S2) | all three: i32[30] | → corpus | D-elab |
| `pending/for-view-local` (#491) | refused 14:1 (`lentDef`) | all three: i32[3] | → corpus | D-elab: the counted walk over a view is total |
| #545 matrix RW, RL, RG | refused (S1, S2) | b2-div and class1-revive: 241 | run | D-elab |
| new: `lend-imm-copy`, `lend-call-copy`, `lend-nest3`, `lend-depth3`, `lend-order3` (from call-grade), `lend-shadow-core` (from class1-revive) | absent | accepted | added, accepted | K-lend (+ K-copy); depth 3 and order 3 |
| *2.3*: a `borrow mut` of a `ref` cell whose body performs only `lin`, unmarked operations of op-accepting servers (a `while` under the runtime; a `must_resume` operation of a T handler), today routed to R1 | refused by R1 (`ResumeO` takes no tick and no abortive operation; the callback is closed) | — | **accepted**, predicted: class 1 by §2.3's lend-form rule | K-lend. The programs are listed by phase-2 check 7 of §2.3; none is named here |

The matrix goes from 18/25 to 21/25.

`reject/lend-div-two` is refused at 14:14 by `lentDef`. It has `lend-div`'s gap: once D6/D10 type
it, it either moves to the corpus or the kernel refuses it, and the result is listed.

### 4.4 Refused on main, still refused under B5

| program | main | B5 (predicted, from class1-revive) | why | fix | recovered by |
|---|---|---|---|---|---|
| **P2** ⚑ `p02-lines-print`, `x02-lines-noprint`, `x02b` | refused 4:1 (`lentDef`); `x02b` 8:14 (`iterError`) | **refused**: `s`'s view is lent across `main`'s ticks | K-unwind (buffer view); see below | **(a)** the loop is inside a callee: `echo` takes the owner `s` and walks it with a cursor, borrowing inside each turn (`borrow imm s { t -> print_str(line_at(t, i)); next_line(t, i) }`), or uses `lib/lend.bc`'s `loop_lend_imm` (message U′) | **B2** W-tick (`lendRT`) at `LendForm` fam; **B6** for the finite-observation shape only |
| **P4** ⚑ `p06`, `p06b` | refused 8:5, 9:5 (S1) | **refused** 6:3: `&a`'s slice lend crosses the inner `while`'s ticks | K-unwind (slice) | **(a)** index in each turn: `for i in 0..n { let x = a[i]; while … ; … a[i] … }` (message U) | **B2** at `fam` |
| #545 matrix AW, AL, AG | refused (S1, S2) | refused 9:3, the same as P4 | K-unwind | **(a)** as P4 | **B2** |
| `pending/for-buf-borrow` (#501) ⚑ | refused 16:55 (`iterError`) | refused 16:11 (buffer view) | K-unwind | **(a)** as P2 | **B2** at `fam` |
| `pending/parse-recover-gen` | refused 136:7 (`iterError`) | refused 136:5 (a literal's view held by a generator) | K-unwind, and class 2 (the generator is stored) | **(b) ⚑** | **B7** (generator holding a view), with B2 |
| `pending/state-machine-audit` | refused 72:1 (`escapeError`) | refused 91:1: "operation 1.0 has two signatures" | K-sig (4.2) | **(a)** `drive` owns the state and runs `with audit(&mut st) { … }` per event. **Measured**: `sma-r1.bc` prints the expected tuple, `live 0`, on both binaries (message S) | as `lend-pipeline` (box Q8) |
| `pending/aoc-2020-07` | refused 34:1 (`lentDef`) | refused 91:27: "`memo` consumed in one arm" | #492, not a lend | **(a)** consume `memo` in both arms; #492's message | #492 |
| `reject/lend-escape` | refused 20:11 (`escapeError`) | refused 23:34: "`q` used twice … `imm 'x array i32 * i32` is not persistent" | a pair is not `DerivedCopy` | **(a)** take the pair apart before the loop, `let (v, n) = q` (message C). After that the block's escape is refused, as the reject intends | stays a reject |
| `reject/lend-shadow` | refused (the rename check) | refused 23:53 on a type error the old check hid | — | stays a reject; `-- expect:` changes | — |
| `reject/for-lend-resumes` (P5) ⚑ | refused | unchanged: `for x in &a { yield(*x) }` in a generator | class 2 | **(a)** index in each turn, `for i in 0..n { yield(a[i]) }`: each read's lend ends before the `yield` (message R) | **B7** |
| `reject/gen-self-borrow` | refused 12:3 (the #172 refusal, retired in 2.5) | **refused**, message R (*2.3*): `imm` borrow, so not R1; `yield` is cancellable, so it forces nothing and `Row.Lend`'s `q = lin` fails; `-- expect:` changes | class 2 (a self-borrow across `yield`) | **(b)** | **B7** |
| `reject/state-across-borrow` (*2.3*) | refused 19:5 (the #172 refusal, retired in 2.5) | **refused**, predicted, unverified: `get`/`put` are `lin`, so the lend is class 1 and forces `state`'s site to `op`; `state` has a `mut` parameter, so it fails the T rule (§21's state-passing; T at box Q8's route (ii)) and is `effHandleV`, whose handled row is `top`. The checker refuses there, W-L's path attached; `-- expect:` changes | the world (§2.3) | **(a)** end the borrow before the operation: `let n = sum.get(); borrow imm line { v -> () }; sum.put(n + 1)` (message W-L, without the tail-position fix: `state` is not T-eligible) | box Q8 (ii), which would make `state` T |
| `reject/async-r1-raise-across` (*2.3*) | refused 12:11 (R1's elaborator check, retired in 2.5) | **refused** by the kernel's R1 premise (`ResumeOC` admits no abortive operation but the cancel target); `-- expect:` changes. Its resuming operation is `yield`, cancellable, so the block stays R1 | R1 | **(a)** as its comment says: handle `Fail` inside the block (`corpus/async-r1-effects.bc`) | — |
| `pending/async-bank` (*2.3*) | pending, 32:17 (R1's elaborator check, retired in 2.5) | **still pending**: the kernel's closed R1 callback refuses the use of `n`; `-- now:` changes | R1 | as listed in the file | — |

⚑ marks an ordinary-looking loop. Every ⚑ program has a written fix (a), still to be measured
(check 6). The one (b) that is ordinary-looking is `parse-recover-gen` ⚑: a generator over a
literal's lines, which is ordinary in Rust.

**Two refusal classes beyond these programs.** Each is listed because ordinary programs fall into
it:

- **D4′ with a ticking body** ⚑: `for x in v` over `imm 'a (array A)` whose body has `div` in its
  row. The `withload` reborrow is `Row.Unwind`, so the kernel refuses (K-unwind).
  **(a)** index in each turn, `for i in 0..len(v) { … v[i] … }` (message U). Recovered by **B3**
  (the view case) or **B2**.
- **K-last**: a lend held across an operation handled by `effHandleL` (`[handle-last]`, a clause
  that works, then resumes or cancels). Its operations are cancellable or abortive, never `lin`, so
  the lend forces no world and `Row.Lend`'s `q = lin` fails (*2.3*: the message is L, a case of R,
  not W-L). **(a)** end the lend before the operation, or write the
  handler so that it resumes in tail position (message L). Recovered by **B2** (a `LendForm` at a
  cancellable row).

**A new reject test:** `reject/loop-linear-owner-each-turn.bc`. A declared (`Tok`-owning, linear)
owner is used by value at every turn of a `while`. It is refused at the turn's split, because its
type is not `DerivedCopy`. This pins that B5 never copies a linear value.

**P2 reconciled with spike round 4.**
`spike743/experiments/Spike743/bc/reify/p2-shape-iterator-over-view.bc` checks `unconditional`.
Its shape is this:

- The lend is `withbor1` of a cell, closed at a row **with no `Div`**.
- Inside it, `echo`'s loop is a `reify`d loop value.
- The block observes that value **a fixed number of times** (three `nu_out`s) and then closes it.

The loop holds the view, not a lend, so no tick crosses the lend.

P2 as written is different. `main` runs `borrow imm s { 't, t -> echo(t) }`, and `echo` drains
`lines(t)` to its end. Under D6, `echo(t)` is a direct-style div call, so the block's callback ticks
once per line at `main`'s row, driven by the runtime. Under D3/D7, a `reify` with a consumer that
drains it is still observed once per turn by a loop whose back edge ticks inside the block. So the
lend of `s`'s view (a buffer: a slice lend, `sliceBorrowIU`) is held across ticks whichever way the
loop is elaborated.

So B5's D-rules cannot produce the spike's shape for P2 or `x02`. The spike's shape needs an
observer that stops after a known number of observations inside the block, and P2 has none.

What recovers P2 is a lend form for the buffer's view across ticks:
- B2's `lendRT` at `LendForm` fam, asserted under `LendFrame`; or
- a class-1 frame for `sliceBorrowIU`. This is #654's Open, a new proof outside the plan.

B6's `for`-to-`reify` elaboration recovers only the variant that observes a fixed number of times
(the spike's). P2's fix today is (a).

### 4.5 Outputs under back-edge-only ticks (decided placement)

**Measured by simulation.** No binary implements back-edge-only ticks. class1-revive's `bcc desugar`
output had every explicit forward `perform[4294967295.0] ()` replaced by *next*, and was run with
class1-revive's binary. Under this, a `while` with k turns takes k observations instead of k+1.

Over all 381 corpus/axes/sugar programs and 49 book and internals blocks, **no output changes**.
Every difference was traced to a parser, printer or branch artefact, and the round-trip of
class1-revive's unmodified core gives the same result.

| program | effect | listed reason |
|---|---|---|
| `io-fuel` `count_lines` | budget 3 reads 4 bytes, not 3. The output is unchanged because byte 4 does not end a line | the comment at `io-fuel.bc:11`–`:12` ("three bytes read") becomes wrong and is corrected. `reify` runs the first turn when the loop value is built |
| `sugar/hof-{returned,closure,local}` | threshold 2 → 1 observations. Output unchanged at budget 10 | — |
| book `iteration.md:87` `collatz` | 112 → 111 observations. Output unchanged at budgets 200/50 | — |
| everything else in `#644`'s list | unchanged: hand-written `unfold`, counted loops, or generators at a row (which already tick only at back edges) | — |

### 4.6 Refusal messages that name the fix

Each message is the checker's text at the refusal it reports. It decides nothing. W-L and W-R are
the checker's refusals at `effHandleV`/`VB`/`L` and `reify`, with the world solve's path attached
as a diagnostic (§2.3).

- **U** (K-unwind, a slice, buffer, `withbor3` or `withload` lend whose callback ticks): "`a` is lent
  at L1 and the lend is still open at the loop's next turn (L2): a {slice | buffer view | reborrow}
  lend is held only across operations that abort. Borrow inside each turn instead, so that the lend
  ends before the turn does: index `a[i]` in the body, or put the borrow block inside the loop."
- **U′** (K-unwind or K-lend, where the loop is inside a callee): "`t` is lent to `echo` at L1, and
  `echo` loops (L2), so the lend is held across its turns: pass the owner `s` to `echo`, and borrow
  it inside each turn of the loop there; or borrow at each use (`f(&s)`) instead of once before the
  loop."
- **L** (K-last): "the lend of `x` at L1 is held across `op` at L2, whose handler works before it
  resumes, or may cancel (`[handle-last]`): end the borrow before `op`, or resume in tail position
  in the handler."
- **S** (K-sig at a threaded loop state): "operation `n.i` would carry the loop's borrow of `t` in
  its signature (`'l0` here, `'l1` at L2), and an operation has one closed signature: borrow `t`
  inside the loop's body (`let v = borrow imm t { b -> … }`) so that the loop holds the owner."
- **C** (a pair holding a borrow, used at two splits): "`q` is used twice and its type
  `imm 'x A * B` is not copyable: take it apart first (`let (v, n) = q`), so that the borrow is
  copied alone."
- **R** (class 2, a lend across a stored loop's or generator's stop): "the lend of `a` at L1 is held
  across `yield` at L2, whose continuation is stored: read `a[i]` inside each turn, so that no lend
  is open at the `yield`."

### 4.7 Counts

| change | count |
|---|---|
| keep running by a new mechanism | 7 |
| firm new refusals | 2 (`lend-copy`, `lend-pipeline`), each with a fix (a) |
| at risk | 3, plus `reject/lend-div-two` |
| newly accepted | P1, P3, 3 rejects, 1 pending, 3 matrix cells |
| new programs | 6, plus the reject `loop-linear-owner-each-turn` |
| still refused | P2, P4, AW/AL/AG and 7 corpus programs; all but `parse-recover-gen` and `gen-self-borrow` have a fix (a) |
| outputs changed | 0 (one comment) |

**P1–P4:**

| probe | B5 |
|---|---|
| P1 | **accepted** |
| P2 | refused (a); B2 |
| P3 | **accepted** |
| P4 | refused (a); B2 |


---

## 5. NOT-do list

- **No `PinLaw` change.** `Core/PinLaw.lean`'s `LendFrame`, `LoopFrame` and `PinLaw` keep their
  statements and fields. The one edit to `Core/PinLaw.lean` is the arity of three `OpSig`
  literals (box Q4). What grows is `CDerivesP`, and with it the derivations `LendFrame` ranges
  over (box Q3, decided). That is stated in SPEC and shown by `bcc trusted`.
- **No relaxed (asserted) rule.** Neither `lendR` nor `lendLoopR` is emitted. Nothing new is
  asserted.
- **No `LifeNatural`, and no stack-indexed relation.** These lines are closed by the user.
- **No change to `fundamentalC`, `adequacyC`, `adequacyD`, `fundamentalD` or `total_every_run`.**
- **No class 1 for `withbor3U`, `withloadU` or the slice borrows.** These are #654's Open, and the
  plan puts them at B2 and B3.
- **No checker or elaborator decision of a guarantee** (STOP: KERNEL WORK). The elaborator neither
  refuses on borrow grounds nor splits a lend per turn (#646 amendment; 0c800b7 reverted).
- **No per-program elaboration case.** The `tryCatch` fallback and the `machine` trial are not
  ported (section 2.2).
- **No copy outside #756's rule.** No `ImmCopies`, no `Val.copyImm`.
- **No Backend lowering that decides ownership.** Every Backend2 drop and copy names its
  `DropRule`/`CopyRule` and passes Lint's premise check (#746 step 3).
- **No count, position, storage or finaliser axis of M1.** B5 builds the world axis only.
- **No third world.** The world is `{op ⊑ top}` (decision 71). A third point needs predicates local
  to a tree-shaped lifetime order, which is unverified and not pursued.
- **No grading of user effects beyond what `effHandleT`'s `hCN` checks.** #654 Open.
- **No premise beyond 1.3's** on `withbor1U`, `withbor2U` or `effHandleT`. The named-risk STOP
  (1.4) is not met by restricting the lend's lifetimes to inside `r`, or by any other added
  premise.
- **Not resumed, merged or cherry-picked:** `class1-revive`, `b2-div`, `call-grade`. `750a-kernel`
  is not touched.

## 6. Tempting shortcuts, and the STOP each raises

| shortcut | STOP |
|---|---|
| Keep LoopLend's per-observation lend for the programs `Div` refuses (`lend-copy`, P2, P4) | **KERNEL WORK.** It decides a lend's extent in the elaborator. The programs go to `pending/` with the lend and the tick, as #646's amendment says |
| A checker copy where the copy rule does not apply: copying the pair in `lend-escape`, copying the state wholesale, or a copy for a non-`DerivedCopy` slot | **LINEARITY.** Refused and listed, never repaired |
| A grade special case for one handler (`count` in P1), or a world chosen per program | **KERNEL WORK.** The world is solved as a row component by one constraint table (§2.3), re-checked by the kernel; one rule for every `effHandleT` |
| Add a third world, or a lifetime-valued world, to recover a program `{op ⊑ top}` refuses | **DECISION.** The world is `{op ⊑ top}` (decision 71); a lifetime bound collapses to these two points (spike 21363bd9). Name the program and STOP |
| Meet the named risk in `lendM_frame` by an added premise (restricting `A`'s lifetimes inside `r`) | **PRINTED-RULES.** No premise beyond 1.3's; STOP and report the step |
| Thread the owner instead of the borrow through a generator's operation to avoid decision R (`lend-pipeline`) | **KERNEL WORK.** That is the per-observation lend; the refusal stands with its fix (a) |
| Fold B2's W-tick (`lendRT`) in early to recover P4, `lend-copy` or AW/AL/AG | **SCOPE.** B2 waits on #750 and is asserted under `LendFrame`; B5 asserts nothing |
| Give `sliceBorrowMU/IU` or `withbor3U` `Row.Lend` "since the proof is the same" | **SCOPE plus a new proof.** #654 left them Open; frames for them are not proved. Stop, report, do not assert |
| Give `reify`'s tick a bound so that P5 or `gen-self-borrow` types | **SOUNDNESS.** A stored loop is owed at every extension (class 2, B7) |
| Repair `lend-config` or `lend-div` by a case that matches their shape | **PRINCIPLED.** Only D6, D9 and D10 as written. Otherwise they are listed refusals |
| Lower a stored loop (`reify` other than `main`'s) by a state machine where the program does not keep the generator | **COMPILER-FIRST.** Machines are the fallback only where a stored κ is real (decision 2026-10-21) |
| Port `class1-revive`'s Backend2 `genIter`/`genIterK` with their untyped `.drop` | **#746.** Every drop names its rule and is listed in `scripts/PinSites.lean` |
| Keep `b2-div`'s `eAbort` matching of residual capabilities by type | **PRINCIPLED.** The residual hands back what was lent, by name (D9) |

---

## 7. Lowering

**Backend2 on main does not compile `Div`.** `Backend2/Convert.lean:2722` sends `iterate`, `divFuel`,
`reify`, `effHandleT`, `lendR` and `lendLoopR` to `outside`. Loops compile today only as the
elaborator's `unfold` machines: §45's η-thunk `nuEta`, the runtime drive of `main`'s loop, and §48's
`bounded_fix` (`genFix`, `:1864`). B5 must therefore lower `Div` from the checked term, or every
looping program leaves Backend2's fragment ("compiler never stale").

**From the checked term**, under N2's effect erasure (§47, resume-once = call):

- `iterate` becomes one function per node, its back edge a tail call (`class1-revive`'s `genIter`,
  re-done under #746's drop discipline).
- `tick` under the runtime clause is erased and answered *next* (`tickTm`). That is the handler law
  for a tail-resumptive clause, read from the `effHandleT`/runtime node in the typed term.
- `main`'s `reify`, with the runtime as its only `Div` handler, runs in place (`convMain`). Its row
  is `F[div]` with `tick` at the solved world. The world is erased with the row; nothing in Backend2
  reads it.
- `effHandleT`/`effHandleL` around a ticking computation use §47's erasure (`handle_tail` → call;
  `[handle-last]` as §51's lowering, already on main for non-ticking bodies).
- `withbor1U`/`withbor2U` at a `Row.Lend` row are §29 *Lowering*: the lent cell is never moved
  (`genLendU` gains the row).
- A `reify` whose loop value is **stored** (it escapes into data or a cell, or is held and stepped
  by hand) is a state machine (`genIterK`, §49). That is the sanctioned fallback where the program
  keeps the loop.
- A `reify` whose observer sites are static (a `for` over it, a direct drain) goes through the
  erasure pass (§47): no machine.
- `div_fuel`'s kernel constant stays outside Backend2. The elaboration never emits it; the
  library's `div_fuel` over loop codata (`lib/div.bc`) is ordinary code.

**Replaced:** the per-body `unfold` machine lowering at elaborated loops (§45 `nuEta` and §49's
drive at `main`'s loop). Both remain for hand-written `unfold` and `pull`.

**The old backend:** `iterate` stays `expandIter` (`Backend/Clos/Convert.lean:894`). Each looping
program gains one indirect call (`counts.expected`). The zero-cost target ("allocate or indirect only
where C/Rust would", measured by corpus counts) is held on Backend2, which has none of these calls.
Whether the old backend, retired at N6, is still held to it is **marked for the user**. If it is, B5
must lower `iterate` natively there too.

**Lint and StackK.** B5 changes neither `Backend2/Lint.lean` nor StackK:

- `Driver.lean:479` (`StackKHandOver`);
- `Convert.lean:1403` (`genStackMach`);
- `Syntax.lean:185`–`:211`;
- `Interp.lean:664`.

New drop and copy sites register through the existing `DropRule`/`CopyRule` and
`scripts/PinSites.lean`. **Conflict:** #746's recent commits touch exactly these files (c7ad8b21,
cf512491, e8024b25, 57d2cdf3), and 750a adds `effThenDiv`/`effAwait` nodes that Backend2 must also
send `outside` or lower. If B5 needs any Lint rule change, STOP and report.

---

## 8. The smallest change and its accounting

| file(s) | change | reason |
|---|---|---|
| `Core/Types.lean` | `World`, its laws; `OpSig.wld : World`; `CTy.eff … rc wld …` | M1 world axis, two points (1.2) |
| `Core/EffDefs.lean`, `Core/EffRules.lean` | `OpEnt.wld`, `Owed` (`Ext` + records inside the bound), `Owed.anti`, `owed_unbounded`, `contShare`/`KapRelT` over `Owed`, `OpSig.ent`, `Row.ofEff … w`, `contShare_ungraded`, `kapRelT_ungraded` | 1.2, 1.4 |
| `Core/EffFin.lean` | `OpSig.LeF`, `OpEnt.Le`, `Row.gradeAt`, `rowLe_gradeAt`, `effWp_gradeAt` | `[sub]`: `top → op` (`OpSig.LeF`) |
| `Core/EffBorrow.lean` | `Row.Lend Δ`, `Row.Unwind.lend`, `Row.Lend.resumes/unwind` | 1.2 |
| `Core/EffWp.lean` | `wpG_M_frameAt`, `wpG_I_frameAt`; `frameX` re-derived, statements unchanged | 1.4 |
| `Core/EffLend.lean` (new) | `lendM_frame`, `lendI_frame`, `cwp_lendM`, `cwp_lendI`, `withbor1L_compatX`, `withbor2L_compatX` | 1.4 |
| `Core/DivDefs.lean`, `DivFuel.lean`, `DivHandle.lean`, `DivHandleLast.lean`, `DivRuntime.lean`, `DivPrograms.lean` | `tickSigW`; `divFuelTy … w`; `KapRelT.owed`; graded `handleT_compatC`; `effHandleL` mechanical; `runtime_every_run w`; `rtMain`, `runtime_main_every_run`, `io_rt_every_run`; `divFuel_every_run w` | 1.3, 1.5 |
| `Core/Fundamental.lean` | the premises of 1.3; the `fundamentalC` cases | 1.3 |
| `Core/Tied.lean` | `CDerivesAt` premises | mirrors `CDerives` |
| `scripts/pin/*.tmpl.lean` → `Core/PinDerives.lean`, `Core/PinFundamental.lean`, `Frontend/Check/{TDerives,TExpr,TLife}.lean` (generated) | the premises of 1.3; the `fundamentalC_pin` cases call the same compat lemmas | box Q3 |
| `Core/PinLaw.lean` | **only** `pinAwaitSig`/`pinYieldSig`/`pinRaiseSig`'s anonymous-constructor arity | box Q4 |
| `Core/PinDerives.lean:17`, `:531` (via the template) | the doc comments that tie R2 to LoopLend; the `CDerivesP` docstring on `Row.Unwind` | stale under B5 |
| `Core/DeclLend.lean:202` | `Sf_unwind.lend` | premise change |
| every `.eff` pattern (Core, Frontend/Check, Backend2; ~220 occurrences in 36 files) | one more argument | arity |
| `Core/Types.lean` (`CTy.applyLSub`, `VFree`, `CFree`, `VScoped`), the substitution lemmas, the row-in-type wf | the `wld` clause | a lifetime inside `CTy.eff` (1.4) |
| `Frontend/Check/Externs.lean` | `IORun.rt`, `IORun.rt_every_run` | D8 |
| `Frontend/{Parser,Syntax,Print}.lean`, `Frontend/Check/TTied.lean` | core text `iterate[…]`, `reify[…](res)`, `div` row; the checker emits `iterate`/`reify`/`handle_tail`/`handle_last` | 2.1 |
| `Frontend/Sugar.lean` | D0–D12; delete the loop machine, `forDataDiv`, `io_hwf`, S1 | 2.2, 2.4 |
| `Frontend/Check/` (the refusal sites) | messages U, S, C, R naming the fix | 4.6 |
| `Frontend/{Syntax,Parser,Print}.lean`, `Frontend/Elab/{Subst,Respan,RenameLife,Effects}.lean`, `Frontend/Sugar.lean`, `Frontend/Check/Elab.lean` (`elabRow`), `Frontend/Check/Steps.lean:541` (`effRow?`), `Frontend/Elab/Worlds.lean` (new) | the world on `Row.cons`, server ids, the lend-form rule, narrowing, the T rule, main's form, the constraints at each emitted form, the solve, the path diagnostics; about 650–900 lines | 2.3 |
| `Frontend/Elab/LoopLend.lean` | delete `lendBind`, `lentDef`, `lendCall`, `iterError` | 2.4 |
| `Frontend/Sugar.lean:4257`–`:4259` | delete the #172 refusal of a borrow block with a resuming body; `corpus/reject/state-across-borrow.bc` and `gen-self-borrow.bc` get their new `-- expect:` lines (W-L, R); `docs/expressiveness.md`'s quote of the message | 2.5 |
| `Backend2/Convert.lean`, `Backend2/Driver.lean`, `scripts/PinSites.lean` | section 7 | lowering |
| `SPEC.md` | a new entry (version after #750 A's, 1.22 if A lands first, fixed at merge); §14's per-observation lend and machine sections rewritten; §29: `LendFrame`'s domain grows with `CDerivesP`'s rules, B5's included (Q3) | spec-first |
| `corpus/` | section 4's moves; 6 new programs; the falsifier's nested-lend programs (check 7); `reject/loop-linear-owner-each-turn.bc`; the measured (a) rewrites (check 6); `io-fuel.bc`'s comment (4.5); the 12 programs' comments; `axes/README.md`; `-- expect:` and `-- now:` lines | section 4 |
| `corpus/*.expected` | `counts` (+1 indirect per loop, old backend); `counts-backend2` (rows for 4.2 out, 4.3 in); `erasure-backend2`; `handled` (`main` gains the `Div` name); `kinds` | measured diffs on `class1-revive` |
| `corpus/sugar/*.core.bc` | up to 22 pairs; `lend-div.core.bc` deleted | the emitted core changes. Each pair is re-checked, not just regenerated |
| `docs/kernel-usage/census.tsv`, `docs/kernel-usage.md`, `scripts/AxiomCheck.lean` | the new lemmas | census |
| `book/src/guide/iteration.md` ("Borrows and loops"), `book/src/elaboration/divergence.md`, `docs/internals/elaboration/divergence.md` | prose | docs |

**Theorem statements changed:** `runtime_every_run` and `divFuel_every_run` gain `w`, with the old
statements kept as the `top` instances. `handleT_compatC` gains `c` and `hCN`.

**Hypotheses added:** `hCN`, a premise of the `effHandleT` rule, not of any theorem. At `c = top`
it is trivial and gives today's rule; it is non-vacuous at `c = op`, where P1's `count` meets it.

**Not changed:** any `fundamentalC`/adequacy statement, `PinLaw`'s fields, `LendFrame`,
`LoopFrame`, `fundamentalC_pin`, `adequacyD_pin`.

## 9. Phase-2 checks

1. `lake build` clean. Iterate with targeted `lake build Core.EffLend` and similar.
2. `scripts/check-hygiene.sh`: no `axiom`, `sorry`, `native_decide`, `implemented_by`, `opaque`,
   `partial` or `unsafe`.
3. `scripts/check-pins.sh`: the generated pin files match their templates.
4. `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]` for `fundamentalC`, `adequacyC`,
   `adequacyD`, `fundamentalC_pin`, `adequacyD_pin`, every lemma in 1.4, and
   `runtime_main_every_run` and `io_rt_every_run` (`scripts/AxiomCheck.lean`).
5. The golden and corpus checks: `scripts/check-corpus.sh`, sugar pairs, clause kinds, handled
   names, cell classes, both `counts` files, erasure, the Backend2 corpus, and native.
6. P1–P4 run by hand against section 4's table. **Every (a) fix is written out and measured**, on
   main's binary and on B5's, and recorded in the PR with its output: `lend-copy`, `lend-config`
   (if refused), `lend-div` (if refused), P2/`x02`, P4/AW/AL/AG, `for-buf-borrow`, the D4′-with-tick
   class, K-last, `aoc-2020-07`, `lend-escape` and `for-lend-resumes`. `lp-r1.bc` and `sma-r1.bc`
   are already measured. **STOP:** an (a) that fails becomes (b) and is raised with the user.
7. **The falsifier on nested lends (condition of Q3; results go in B5's PR).** Programs, each run
   under `--check tags`, `--check fresh` and `--alloc least`, and the stress generator (several
   hundred seeds per mode, as in the 743 spike):
   - `nest-c1-in-r1`: a task's R1 `borrow mut` across `await`, whose callback holds a class-1 lend
     of a second local across a tail-resumptive handler's operation, and across a `while`'s ticks
     driven by the runtime.
   - `nest-r1-in-c1`: a class-1 `borrow mut x { while … { … } }` at `main`'s row, whose body spawns
     a task holding an R1 lend of its own local across `await`.
   - `nest-c1-r1-c1`: depth 3, alternating, with the inner lend read after the middle one's stop.
   - `nest-cancel`: `nest-c1-in-r1` with the task cancelled while the class-1 lend is open, and with
     an abortive operation raised inside the inner lend.
   - `nest-imm`: the `imm` variants, the re-read at each turn through #756's copy.
   - `nest-fin` (after #750 A): a `[then]` whose finaliser's row holds `Div` (`effThenDiv`), and
     whose finaliser holds a class-1 lend across a `while`'s ticks, run on the raise path and the
     normal path.

   Kill: a run that gets stuck, leaks, gives a wrong answer or trips the tag check. That is a hard
   stop, reported before the PR.
8. **`bcc trusted`** shows `LendFrame` at every R1 site whose callback contains a class-1 lend
   (`nest-c1-in-r1`, `nest-c1-r1-c1`), `PinFin` at `nest-fin`, and nothing new at class-1-only sites
   (`lend-mut`, P1).
9. One `make gate`, run only as `~/repos/scripts-local/gate-serial.sh gate` from the worktree,
   once, at the end.

## 10. Questions: decided, and still open

> **Q1. World carrier: DECIDED, two points `{op ⊑ top}`** (user, 2026-10-22, #673 review item 4;
> decision 71). A lifetime bound collapses to these two points (spike 21363bd9).

> **Q2. Who decides the world: RESOLVED (user, 2026-10-31, route 4): the elaborator's row
> inference, as one more row component** (§2.3). Option (A), inference inside the checker, was
> decided earlier the same day and is reversed. The reason: rows are already inferred in the
> elaborator (SPEC §18, §38), and `Div` (B2) and `Alloc` (#763) are to be inferred there the same
> way, so the world is one more component of that inference, not a mechanism of its own. The
> checker's `CRow` is the kernel `Row` at a closed `World` and can hold no metavariables. The world
> is one attribute per server (a control site, the runtime, a `reify`, a `div_fuel`), riding on the
> per-server copies. The elaborator writes it into the core
> text, and the kernel re-checks every world, so the inference decides no guarantee.

> **Q3. `CDerivesP` mirrors `S.Lend`: DECIDED by the top foreman,** answering from the across-loops
> decision (2026-10-29/30: PinLaw's schemas are uniform in depth and holder, so a class-1 lend nested
> in an R1 callback is more depth and holders under the same schema, not a new assumption), with the
> conditions below. **The user is being told.**
> **Exactly what widens:**
> - `LendFrame` (`PinLaw.lean:91`) quantifies over callbacks `M` with
>   `CDerivesP Δb [⟨V, true⟩] M (.comp (CTy.effOf S (.box (.var x) B)))`.
> - Before B5, every `withbor1U`/`withbor2U` node inside such an `M` had a row of abortive
>   operations only (`S'.Unwind y`).
> - After B5, `M` may contain a `withbor1U`/`withbor2U` node at `S'.Lend y`: a lend of a local
>   `y`, inside the R1 callback, whose own callback performs non-abortive linear operations at world
>   `op`. These are tail-resumptive handler operations, and `Div` ticks driven by an in-scope
>   `div_fuel`. The R1 row itself is `ResumeOC` after #750 A, which holds no `tick`.
>
> Those derivations are the new members of `LendFrame`'s domain. Nothing else in `CDerivesP` changes.
> `LoopFrame`'s steps `N`, `K` and `s0` gain the same nested nodes inside handlers they contain: their
> own rows are `.ret`.
>
> **The same growth after #750 A** (`750a-kernel`'s `Core/PinLaw.lean`). There, `PinLaw` has three
> schemas:
> - `LendFrame` is over `LendForm` at `Row.ResumeOC S x` (SPEC §29a). Its `M` gains the same
>   class-1 nodes. `ResumeOC` holds no `tick` either.
> - `LoopFrame`: as on main.
> - `PinFin` (`:138`) is over `[then]` with `Row.divB SD = true` (`CDerivesP.effThenDiv`), and
>   quantifies over `CDerivesP` derivations of `M`, `N` and the finaliser `D`. After B5, `D` may hold
>   a class-1 lend across its own ticks (`Div` is in `SD`), and so may `M` and `N`. Those are new
>   members of `PinFin`'s domain.
>
> The statement in SPEC names all three.
> **Conditions:**
> - Phase 2's check 7: the falsifier on nested lends, with the results in the PR.
> - SPEC's B5 entry, and §29, say plainly: "`LendFrame`'s domain is every `CDerivesP` derivation of
>   the callback; it grows with the rules `CDerivesP` admits, and B5's class-1 premises are such
>   rules."
> - `bcc trusted` reports `LendFrame` at those sites, and `PinFin` at the `effThenDiv` sites with a
>   class-1 lend inside (check 8; `nest-fin` in check 7).

> **Q4. `PinLaw.lean`: DECIDED, the literals' arity only.** B5 adds `wld` after `fin` on main and
> takes #750 A's layout at merge (`wld` after `rc`). The textual merge covers every `.eff` pattern,
> `scripts/pin/*.tmpl.lean`, the `CDerivesP` template's stale docstring (`:14`, "at a row of abortive
> operations only") and SPEC. The SPEC version is fixed at merge (1.22 if A lands first). Any other
> `PinLaw.lean` edit is a STOP.

> **Q5. Tick placement: DECIDED, `iterate`'s own back-edge ticks** (correct over consistent).
> Measured by simulation: no output changes. `io-fuel`'s comment is corrected (4.5).

> **Q6. The residual at an exit (D9): hand back by name.** This is as written. `lend-config` and
> `lend-div` test it; a program it cannot express is a listed refusal with a fix (a).

> **Q7. "Reads checked facts": an interpretation, for the user.** The foreman confirmed the reading:
> the elaborator reads syntax and inferred types, and decides no guarantee. It is an interpretation of
> "checked facts only": no pipeline gives the elaborator checker output. It is **marked for the user**
> to confirm.

> **Decided (user, 2026-10-31): route (ii), handler-owned state on `effHandleT`, as its own unit after B5.**
>
> **Q8. K-sig: a generator's signature depends on its consumer. A menu.** The diagnosis (4.2) shows
> the root. D5 threads the consumer's loop state through the producer's operation (`x × ws ~> ws`),
> because `effHandleT`'s clauses are closed. So a generator's signature depends on whoever consumes
> it, and `makeInst` makes one instance per use, with or without borrows. A borrow in `ws` only makes
> the dependence visible, as a lifetime that decision R refuses.
>
> | option | kernel change | what it fixes | cost |
> |---|---|---|---|
> | **(i)** a lifetime-polymorphic `Ξ` | `Core/Tied` (1008 lines): `Ξ` indexed by the lifetime context, or signatures closed under `∀'l`; `RowAt`/`SigsAt` and `sig_prefix_of_rowAt` instantiate it. `Frontend/Check/Tied.lean`'s `sigsOkB` compares up to lifetime instantiation | `lend-pipeline` and `state-machine-audit` as written | the symptom only. Signatures still depend on the consumer, and `makeInst`'s per-use instances stay. Unestimated; it touches decision R |
> | **(ii)** handler-owned state on `effHandleT`: a parameterised tail clause `Hc : P × A → F(P × B)` | `effHandleT` gains a state type `P` and an initial state; the handler threads `P` from clause to clause and returns it with the result. `handleT_compatC` is restated with `P` in `KapRelT`'s answer. The erasure law (§47) becomes "resume-once = call with the state passed" | the root: operation signatures are the user's declared ones (`Yield[i32]: i32 ~> 1`), closed and independent of the consumer. `makeInst` needs one instance per generator, not per use. A borrow in the loop state lives in `P`, typed under the handler's `Δ`, never in a signature | a new rule's proof, about the size of `DivHandle.lean`'s `effHandleT` part (`DivHandle.lean` is 875 lines; `DivHandleLast.lean` 975), plus D5's emission, Backend2's lowering of `P` as a loop-carried variable, and the same for `effHandleL`. Parameterised handlers are the literature's standard form (Plotkin–Pretnar) [recalled] |
>
> **Is (ii) in B5's scope?** Not as B5 stands: it is a new kernel rule, with its proof and lowering,
> and B5's acceptance does not depend on it. *Recommendation:* (ii), as its own unit after B5, because
> it removes the cause, and (i) leaves it. **The user's call**, raised through the foreman.
>
> **What B5 does meanwhile:** D5 as written. `lend-pipeline` and `state-machine-audit` go to
> `pending/` with message S and their measured fix (a). D5 states that its state-in-signature choice
> is forced by closed clauses (2.2).
>
> **Other refusals with no step in the plan:** P2's buffer view is recovered by B2 (`lendRT` at fam),
> not B3 or B6 (4.4); `aoc-2020-07` is #492.

> **Q9. D4′: DECIDED, in scope,** as a rule by type, with copies only through #756's rule.

## STOPs carried into phase 2

- **Q3:** the falsifier on nested lends (check 7) breaks a run.
- **Q4:** `PinLaw.lean` needs more than the literal arity.
- **S2:** a written fix (a) fails when measured. It becomes (b) and is raised with the user.
- **2.3:** a uniform world per site is not principal (phase-2 check 5 of §2.3), or a construct's
  constraint is not Horn.
- **2.3, form condition:** the checker has to classify `handle_tail`/`handle_last` out of a plain
  `handle`, or main's runtime form out of a `reify`, so the elaborator would have to predict a
  kernel rule.
- **2.3, `Div`:** server ids for `Div`'s servers are more than a slot in the copy keys; report it
  with Div-alt (a second mechanism) before building.
- **2.3, refusal:** the elaborator refuses a world conflict instead of writing the forced `op`.
- A class-1 port that needs a changed `fundamentalC`/adequacy statement, or a new hypothesis on
  them.
- A program accepted only with a copy that #756's rule does not insert.
- A Lint rule change.
- A stored-loop machine where the program does not keep the loop.
- Any frame for `withbor3U`, slices or `withload`.
