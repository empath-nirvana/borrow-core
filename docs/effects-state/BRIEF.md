# Effects: the shared starting brief

Every agent working on the effect calculus gets this file in full. It says:
- what exists;
- what works;
- where the first approach reached its limits;
- what was proved, refuted or stopped;
- what the user has decided;
- what is genuinely open;
- the rules for working.

The evidence for every line is in the files beside it:

| file | contents |
|---|---|
| [01-kernel.md](01-kernel.md) | the effect kernel and toolchain on main, file:line |
| [02-experiments.md](02-experiments.md) | every effects experiment: goal, proved, refuted, open, world |
| [03-attempts.md](03-attempts.md) | the history, episode by episode, with the user's redirects |
| [04-decisions.md](04-decisions.md) | the decisions register, with the user's words and strength |
| [05a](05a-open-questions-1-34.md), [05b](05b-open-questions-35-68.md) | the draft spec's 68 open questions, classified against decisions and evidence |
| [06-bolo-machinery.md](06-bolo-machinery.md) | the BoLo machinery, and where effects work uses, re-derives or bypasses it |

**Read the detail file before relying on a line here for anything load-bearing.**

> **The first rule: nothing can break the borrow calculus.**
> In the user's words, 2026-10-03: "NOTHING CAN BREAK THE BORROW CALCULUS."
>
> This is about the borrow calculus's **guarantees**, not about leaving BoLo's text untouched. The user: "There is a big difference between doesn't break the borrow calculus and doesn't change bolo. You can't add an effect system without changing it. They interact."
> - **Effects change BoLo.** The world, the wp and its stop condition, the relation and the borrow rules at effect rows are expected to change where effects and borrows interact.
> - **Borrow safety is never weakened.** The extended calculus must still prove borrow safety for every program, effectful ones included: the fundamental property, adequacy, no use after free, exclusive mutable borrows, lifetimes respected, leak freedom.
> - **No effect feature is a way around borrowing.**
> - **Each change is proved.** A changed BoLo definition comes with the proof that the guarantees still hold. It is never assumed.

---

## 1. What works

The work is not starting from zero. A coherent effect kernel is built, proved and running on main. Every result in this section is sorry-free and axiom-free. Each one holds at Core's one relation (`vC`/`cC` over `wpTS`/`wpG`/`ewpTS`, with the typed world `TW` inside `wpG`). That is the planned world `W` at the empty lend stack, `σ = []`.

**Kernel**
- **Machine.** Six `Prim`s, with no new `Expr` former: `perform`, `raise`, `hnd`, `ubind`, `ccatch` and `cfin`, plus `boundedFix`.
  - Head steps for return, operation, unwind, finalise and cancel.
  - Handlers are deep, and forwarding is structural.
  - Unique decomposition and determinism hold with effects (`Core/Steps.lean`).
- **Types.**
  - Per-operation layers `CTy.eff n i q A B C`. A row is a first-match list keyed by `(n, i)`.
  - Continuation qualifiers `lin`, `aff` and `unr`.
  - `F_Σ R = CTy.effOf`.
- **Typing.** `CDerives` has `[sub]`, `[perform]`, `[raise]`, `[let]`, `[then]` (finalisers), `[handle]` and `boundedFix`, plus six unwinding borrow constants (`withbor1U/2U/3U`, `withloadU`, `sliceBorrowMU/IU`).
- **Semantics.** One generic `opTable` gives the protocol table of a row. `ewpTS` is the least fixed point over `wpG`. `contShare` and `KapRel` put the Kripke quantifier on the continuation.
- **Handler soundness.** `ewp_handle` (`Core/EffRules.lean:615`) proves a handler sound by induction on the inner fixed point.

**Metatheory**
- `fundamentalC` covers every effect rule.
- `adequacyC`, `adequacyD` and `adequacyD_obs` say every run under every allocator reaches `()` with empty memory, and is never stuck.
- Leak freedom: `NoOwn` plus `reclaim`.
- Effect safety: `adequacyD` at `F_∅ 1`, together with `ewp_bot`. It has no separate name.
- The totality theorems.
- `bounded_fix` is sound at every computation type.
- Both cancel outcomes are machine-checked (`Core/EffCancel.lean`).
- Ten acceptance programs are closed derivations, run by adequacy and by the interpreter (`Core/EffPrograms.lean`).

**Around the kernel**
- Outlives and `'main` (SPEC §23).
- Affine closures as ν codata (SPEC §22), with positivity only for the effectful form.
- Bounded recursion and `Exhausted` (§20/§21).
- `Loop_Σ` as codata.

**Toolchain**
- Surface stages 1–3 of #188 and #232 compile and run.
- Handling is erased:
  - an abortive operation becomes a branch per call;
  - a control operation becomes a state machine;
  - a tail-resumptive operation becomes a direct call.

---

## 1a. What the language actually does

Effect work is easy to do against the proof model alone and get the implementation wrong. Read this first. Sources: `docs/pipeline.md`, `Backend/README.md` (Pipeline, Representation, Stack, Memory discipline, Counts), and decision 31 in `docs/decisions.md`.

**The pipeline.** `file.bc` is parsed, elaborated and checked into a Core `Expr` with a proof of `CDerives`. It is then compiled through a closure IR and a flat IR to WebAssembly, and run on wasmtime with tail calls. Programs that can't be spelled in the surface, such as §19's capturing handlers, enter at the compile stage (`bcc kernel`).

**Linearity is enforced before the backend.** The check stage inserts the destructor of every owned value that a path leaves unused (SPEC §12). So the `Expr` handed on consumes each value exactly once.

**Effects compile with no runtime handlers, the way Rust compiles `async`** (`Clos/Capture.lean`, `Clos/Unwind.lean`). There is no handler stack and no search.
- **Abortive operations** become branch-per-call propagation, Rust's `Result` and `?`: a code that may raise answers a sum, and a `raise` arrives at the `case` of the frame that catches it.
- **A tail-resumptive operation** whose handlers have one closed clause is a direct call.
- **A code that may suspend** answers its outcome: `inl v`, or `inr (payload, k)`.
  - The suspended computation `k` is a closure of a resume code over its **state**.
  - The state is an n-ary sum, one variant per resumption point, holding the variables live there. At a call point it also holds the callee's `k`, so a continuation's size is known statically.
  - Resuming switches on the state. Cancelling runs the callee's `k` first, then the point's finalisers innermost first, and drops every other variable.
- **Answering operations** are calls on a capability.

**Where values live** (Representation). Pairs, sums, integers and closures are words, not objects. A closure is a stack value: its code's tag, then its captures, defunctionalised. Only `alloc` makes a cell, and an array is one allocation. A suspended computation is a value, a state-machine state, not a heap object.

**The model's "heap" is the abstract store, not malloc.** BoLo's locations are semantic. The backend maps them to words, stack values, state-machine fields, or a real allocation where necessary. `bcc-counts` tracks runtime allocations, indirect calls and deep copies against `corpus/*counts.expected`, and every run prints `live N`, where `live 0` is the runtime leak check. A resource in the model does not imply a runtime allocation.

**Host resources are opaque types** (decision 31): `VTy.opq k`, for example the I/O handles in `Core/Stdio.lean`. They are not persistent and have no destructor, so they can only be moved or handed to externs, never copied or dropped. Their linearity comes from the typing. In the relation an opaque value is a pure predicate, `⌜k.Holds v⌝`, holding no resource, so leak freedom does not cover them today. Captured continuations are in the same position: linear by typing, invisible to the semantics.

**Known runtime cost:** a place that spans a suspension stays a real cell today, one allocation each. Inline placement in a pinned frame is open (P13, synthesis §11).

**What the language already has, built and running.** Check this list, and grep SPEC and the corpus, before proposing any mechanism. A proposal that duplicates one of these must say why the existing one doesn't suffice.

| feature | SPEC | corpus |
|---|---|---|
| codata `νX. C`, observed by drivers | §7 | `nats`, `iter-*` |
| divergence as an effect (`Loop`) | §14 | `core-effects-loop` |
| generators (`Yield`, pull, adapters, close, a generator stored in a cell) | §15 | `gen-*` (14), `core-yield-*` |
| counted loops, `for` over data | §16 | `count-*`, `for-*` |
| buffers, text, literals | §17 | `utf8`, `split`, `trim`, `parse` |
| effects and handlers: answering capabilities | §18 | `effects-*` |
| native capture: `handle`/`perform` with suspend, resume, cancel and finalisers, compiled to state machines | §19 | `capture-*`, kernel programs |
| recursion: bounded and deep drivers, `Exhausted`, the fixed point of a generator | §20, §21 | `rec-*` |
| affine closures (codata with arguments) | §22 | `aff-*` |
| non-strict outlives, `'main` | §23 | `lend-*` |
| externs and I/O capabilities (linear, opaque host resources) | §11, decision 31 | `io-*` |
| arrays and slices | §9 | `array-*`, `slice-*` |
| implicit destructors | §12 | throughout |
| zero-size cells cost nothing at run time (`zeroCell`) | §23 | |

So coroutines and generators are already effects with suspension. What is missing is lends held across a suspension (tier 2) and the proofs that tie this to an abstract effect algebra, not the mechanisms.

## 2. The machinery to build on

Use these by name. Don't rebuild them. Details and paper page numbers are in [06](06-bolo-machinery.md).

- **BoLo, as printed.**
  - The resource algebra.
  - `Life = ℕᵒᵈ`.
  - ⦇ρ⦈ and `↭`.
  - И freshness ([TR] 6.108–6.112).
  - Imm Frame (6.64), Mut Frame (6.65) and Anti Frame (6.66). Their `wpG` forms are `wpG_I_frameX`, `wpG_M_frameX` and `wpG_M_antiFrameX` in `Core/EffWp.lean`.
  - The reborrow rule 6.150, as `wpG_reborrow`.
  - Outlives 6.60.
  - The borrow constants 6.172–6.176.
  - The fundamental lemma 6.151.
- **Resources that arise.** This is the typed world `TW`, with `TI`/`TW.inv` (`Core/World.lean:110`, `Core/Invariant.lean`; adjudications §12.72–§12.73). §6 quantifies over resources that ARISE. That is settled, and it is how the paper rules out unreachable counterexamples. **Use `TW` for arising.** Don't build a parallel guard.
- **Kernel effect lemmas.**
  - The `ewp_*` fixed-point and bind lemmas, and `opTable_mono`.
  - `ewp_abortive` and `ewp_unwind`/`ewp_end`.
  - The frame lemmas at abortive tables (`ewpTS_*_frameU`).
  - `ewp_kappa_resume` and `ewp_kappa_cancel`.
  - `ewp_frame_plain` and `ewp_frame_then`.
- **Experiments with reusable results.** See [02](02-experiments.md) for the world each one lives at.
  - `HandlersAsBorrows`: `handle` becomes `withbor`, an answering handler opens a fresh lifetime, plus `effect_safety` and `handle_is_shift`. It sits at the paper layer.
  - `HandlersControl`: SPEC §19's motivating results.
  - `Shifts`: one schema for every borrow constant.
  - `Grades`.
  - `EffModelRel`: every algebraic law, proved in a sibling calculus with no bridge to Core.
  - `GhostEnd`: lends spanning yields, including through a cancel.

**Duplication to know about.** These are not a licence to add more:
- The `wpG` frame rules are line-for-line copies of `Core/FrameRules.lean`.
- The six `*U` twins each re-run the proofs of 6.172–6.175 at `ewpTS` instead of deriving from their pure versions.
- The typed world exists twice: in `Support/TypedWorld` at BoLo's types, and in `Core/` at the CBPV types. No theorem relates the two copies.
- Rows are computed twice: by name in the elaborator and by `(n, i)` in the core and backend. No lemma relates them.

---

## 3. Where the first approach reached its limits

These are properties of the current kernel, each with a location.

1. **No lend spans a suspension. Two conjuncts of `wpG`'s stop do this, not one.**
   - **T1, conjunct 40** (`Core/EffDefs.lean:40`) requires the open Imm (6.64) frames and records to equal those at entry. It stops an Imm frame from spanning a stop.
   - **`↭`, conjunct 37** (`ResU.UpdV ρ π`) stops a Mut (6.65) lend from spanning a stop. A 6.65 lend leaves the frame and record lists unchanged, so T1 accepts it, but `↭` forbids a run ending with a new `mut` cell.

   This is machine-checked in the targets library (`experiments/Targets/Targets/Restricted/RunEnd.lean`, branch `targets`), using LoopBorrow's `not_upd_of_new_mut`. So tier 2 must change the update relation at a stop, not only lift T1.
   - It is our conjunct, not a printed row: [TR]'s `wp` ends at a value.
   - Its consumers are every `F_Σ` clause, `wpG_bind`, and the `hFs` hypotheses of the frame lemmas.
   - Downstream it causes: borrow callbacks restricted to `Row.Unwind` (abortive operations only); and the surface rejecting a resuming operation inside a borrow block or a resuming `for` body over a lend.
2. **No world component for a lend open across a stop.** `TW`'s `ps` exists but must be unchanged, and a Mut lend leaves no `ps` entry.
3. **Frame lemmas at `ewpTS` exist only at abortive tables.** So no borrow constant takes a callback that performs a resuming operation.
4. **Handler laws live off the kernel.**
   - No return, operation, forwarding or fusion law is stated over `hnd`/`ewpTS`. `ewp_handle` is a compatibility lemma.
   - The laws exist only in EffModelRel (a sibling calculus) and in prose (`docs/effects-tr`).
5. **Two handler mechanisms.** One is the `withswap` answering encoding (`Core/Handlers.lean`, run facts only); the other is `hnd`. They are unrelated, and no table checks `withswap`. SPEC calls `withswap` "not a borrow" and gives it no unwinding form.
6. **Rows are lists of layers, not sums of a signature.** There is no single signature object. `Row.Unwind`, `LinResume` and `[lend]` do not compose.
7. **Handlers open no lifetime.**
8. **SPEC §19 drift:**
   - SPEC writes `CTy.eff Σ A`; the Lean has per-operation layers.
   - SPEC says operation types are closed in lifetimes, but neither `effPerform` nor `effHandle` requires it. Only `Row.Unwind` and `EffLeaf` do.
   - §19 *Theorems* names `ewp_perform`, `ewp_bind`, `ewp_ubind`, `wpTS_*_frameU` and `cancel_compatC`, which don't exist.

---

## 4. What was tried

Each result names the world it lives at:
- **Core σ=[]**: the kernel relation.
- **GE**: a GhostEnd `vRL*` relation.
- **SIB**: the EffModelRel sibling calculus.
- **PAPER**: a paper-level BoLo encoding, or prose.

| line of work | outcome | world |
|---|---|---|
| Tier-2 "ghost-end" route: end internal lends at a stop, re-lend fresh at resume. This is OQ-9 option (b). | Instances PROVED at today's stop: `withbor_spans_yields_cC`, `imm_spans_yield`, `spans_two_affine_yields` (the cancel path) and `withborR_compat`. The general theorem is open. | Core σ=[] |
| D16.1, the lend-stack-indexed relation (#282), and the uniform stack step (#283) | PROVED: definable by structural recursion; the stacked lemmas hold at every stack. | GE |
| GFP, the generalised fundamental lemma (#284) | REFUTED as we stated it (`not_gfp`). This is our statement, not a printed lemma. The witness does NOT arise (`wpG_below_not_arises`, #285). | GE |
| The arising-guarded GFP (#285) | The `lam` and `allI` rows are PROVED, and `gfpAtA_nil` reduces it to `fundamentalC`. GFPA in general is OPEN. The guard `TabAtS` is GhostEnd's own and is not related to `TW`. | GE |
| Borrow callbacks at every stack extension (#287) | `callback_ext` PROVED. `vRLk` has no `σ = []` lemma. The Kripke product-world reading is in §17 of the effects TR. | GE |
| Five relation families beside `vC`/`cC`: vRL, vRLg, vRLs, vRLa, vRLk | Each closed one gap. Only `vRLs` and `vRLa` reduce to `vC` at σ = []. These are the main evidence for the accretion pattern in §8. | GE |
| Re-stratification as naturality (#257) | `mut_not_natural` REFUTED. Whether the witness arises was never checked, yet it steered the work to the ghost-end route. | Core-adjacent |
| Phase A/B effect model (#235, #237, #247) | Every algebraic law PROVED, plus safety and `safety_obs`. `nu_op_fails_multishot` arises for `unr` operations. No bridge to Core. | SIB |
| Effects TR (#248–#256) | Laws, the adjunction, stored continuations and the Mut cell. | PAPER |
| Stage-1 kernel lift (#274), branch `lift-stage1` | `ewp_gen` (L14.3) PROVED. T14.4, T14.6 and the `[gen]` rule were never written. The work stopped, and the user judged the incremental lift ad hoc. #274 is still open, with no rejection recorded on it. | Core σ=[] |
| First-order effect callbacks (#233) | Closed by the user: "solves the first-order case only". | — |
| TwoRun: binary facts from determinism up to renaming | `head_rename` covers part of the machine (no arrays, no capture). It **does not build on main** (FrameTheorems.Footprint and Optics.Runs fail, as of 2026-10-03). | Core (stale) |
| Effects audit (#288, PR #289) | Verdict CONSOLIDATE. The target structure was signed off 2026-10-03. | — |
| Spec-and-plan workflow (#290) | The draft spec (PR #461, draft) failed validation in both rounds. 170 issues were filed and then deleted. | — |

**The draft spec** (`docs/effects-calculus/` on branch `effects-calculus-spec`) is a list of questions, not an authority. Its structure section and its open-question register are useful. Its claims are only as good as the citations behind them.

---

## 5. The target the user signed off (2026-10-03)

This is the audit's structure, with the critic's corrections:

1. **One signature object.** Rows are sums, and `opTable` is the interpretation.
2. **Models and comodels.** Handlers are models and capabilities are comodels of the same signature; `withswap` is the co-operation carrier. One `IsModel` lemma, with `ewp_handle` as initiality.
3. **Handler laws over the kernel relation.**
4. **One Kripke world `W = (ρ, ls, σ)`.**
   - Resource × lend stack × TW's own state.
   - The stop condition is relativised.
   - `vC`/`cC` are the `σ = []` instance, and the five `vRL*` families are retired into it.
   - Where the future-world quantifier goes (at the binder clauses, as #287 does, or at `U`/`contShare`/`KapRel`, as the audit proposes) is OPEN. A Lean statement settles it, not prose.
5. **One borrow per printed constant, over any well-formed row.** The frame lemmas are lifted once, and the `*U` twins become abbreviations.

**Critic's corrections:**
- Build on HandlersAsBorrows.
- Tier 2 did not "halt".
- Probe the unknowns first: what happens to open frames when a continuation is cancelled, dropped, or resumed between lenders.
- Changing the stop condition is a kernel definition change and needs a SPEC entry.
- State laws at `W`, or show they survive the re-index.
- Include TwoRun, Grades, Shifts, SPEC entries 13 and 19–21, `raise`, lowering and threads.
- Read the literature; don't recall it.

**Tiers.** Tier 1 keeps T1. Tier 2 is self-referential suspension, and it is in scope. The hard-stop rule is not in force while we plan. In the user's words: "There's no hard stop phase now we are just planning." (2026-10-03)

---

## 6. Decisions, at the strength the user used

The full register, with sources, is [04](04-decisions.md). Only entries marked decided constrain a design, and even they stay open to the user. How code is built today is not a decision.

**Decided**
- **Multi-shot is ignored as a design goal** (decision 63, 2026-10-04). In the user's words: "TOTALLY IGNORE MULTISHOT AS A DESIGN GOAL. If it works it works, if it doesn't, it doesn't, I don't care either way." It never blocks, shapes or costs anything. On friction, restrict or remove the `unr` qualifier, and don't ask.
- **Effects are core.** They live in the kernel, on a literature-backed foundation.
- **Laws first.** Design from the equational theory; never improvise a mechanism.
- **The actual calculus.** "Make sure the agents are building the actual effects calculus not an approximation of it." No first-order fragment, no effect-ish encoding.
- **Spec first.** A full specification, with open questions boxed, before any kernel work.
- **No step-indexing** (decision 7).
- **Effect handling is erased at runtime.** No runtime handlers.
- **No function colouring.** This is the lead axis. A function's type *does* show its effects; colouring is about types the programmer writes, and lowering is chosen by specialisation.
- **Divergence** is an effect: `Loop` codata. Totality is not a goal.
- **Errors** are a control-flow effect: `raise` plus handlers (#168).
- **Handler state** is passed to each clause and at each resume (decision 59).
- **Nothing can break the borrow calculus** (2026-10-03). See the first rule above. It is about the guarantees; BoLo's definitions are expected to change where effects interact.
- **Row variables are in the kernel** (2026-10-03). In the user's words: "of course we have row variables in the kernel." This supersedes decision 57's first bullet.
- **Handlers are deep** (2026-10-03), as SPEC §19 builds them. This revises decision 15.
- **Cancellation is what the unwinding effects do as built** (SPEC §19). In the user's words: "Whatever they do is what we decided." (2026-10-03)
- **No hard-stop phase while planning** (2026-10-03). The tier-2 hard-stop rule of 2026-10-02 is not in force.
- **Process:**
  - unknowns first;
  - no changing an agent's scope mid-run;
  - **no GitHub issues until the plan and spec are agreed with the user**;
  - open questions are never issues;
  - the first-pass plan stays coarse.

**Defaults and deferrals (not prohibitions)**

- **Kernel equations and binary laws:** "optional and don't get pursued unless they become necessary for safety" (2026-10-02).
- **Higher-order operations:** "out of scope" in decision 57 (2026-10-01). Read this as not now.
- **Runners:** not user-facing. As an internal architecture, BoLo-as-runner is "kind of genius", "not yet decided".
- **Threads** are required eventually. Keep the door open.
- **Traits** are up in the air. **Interior mutability** is open.
- **Our names, not Rust's.** Rust names appear only as comparisons.
- **Externs and unsafe** are outside the proofs by design.

---

## 7. Open questions: what is actually open

The draft boxed 68 questions. Classified against decisions and evidence ([05a](05a-open-questions-1-34.md), [05b](05b-open-questions-35-68.md)), most are not open.

**Decided, answered elsewhere, duplicate, moot or optional.** About 40 questions, including:
- OQ-2: tier 1 first.
- OQ-4: binary laws optional.
- OQ-12: higher-order operations not now.
- OQ-15: div is codata.
- OQ-16: multi-shot is ignored.
- OQ-19: runners are not user-facing.
- OQ-25: handler state.
- OQ-31: no step-indexing.
- OQ-38: site freshness is checked by the elaborator.
- The questions that depend on options nobody chose: OQ-41, 59, 63, 65 and 66.

**Posed on a misreading**
- OQ-1 and OQ-30 treat effects in a type as colouring.
- OQ-20 omits the TR's "fail to the lend".
- OQ-21: settled. Cancellation is as built.

**Settled by the user on 2026-10-03**
- **OQ-13:** row variables are in the kernel.
- **OQ-21:** cancellation is as built.
- **OQ-26:** handlers are deep.
- **OQ-33:** no hard stop while planning.

**Need the user later:** OQ-6 (typed role declarations, a one-way door) and OQ-23 (is lowering correctness a theorem?).

**Real unknowns, settled by proof**
- **Building `W`:** OQ-44, 45, 46, 57 and 58. OQ-57 needs the user only if one world cannot hold the closing obligation.
- **Tier 1:** OQ-1 (how answering and control handlers relate) and OQ-28 (storing a continuation).
- **Tier 2:** OQ-3, 7, 8 and 9.
- **The async lead axis:** OQ-56, 60, 61 and 67. Three of these need the user after their probes. Decision 7 already rules out the options that need negative recursion.

---

## 8. How the first approach went wrong

Each pattern is evidenced in at least two episodes ([03](03-attempts.md)). Recognise them, and stop and report when you see one starting.

1. **A narrow build with a gap list, then a restart.**
2. **Surface spelling or role-by-shape treated as the mechanism.**
3. **Scope changed while an agent was running.**
4. **"Reduces to one more lemma", with a new relation family each step.**
5. **Laws proved at a world other than the kernel's, and never lifted.**
6. **A refutation steering the work before anyone checked that its witness arises.**
7. **Residuals carried forward and never done.** The 6.150 lift to resuming tables appears in six reports.
8. **Work planned or filed before its target structure was agreed.**
9. **Decisions recorded more strongly than the user said them.**

---

## 9. Records that are stale or conflicting

Don't cite these as authority. Most of them wait on the user.

- **Decision 48** still says "Effect rows never enter the core" (`docs/decisions.md:606`). PR #234, which corrects it, is unmerged, and SPEC §18 and `Core/Handlers.lean:8` still cite it.
- **"Decision 19 forbids rows"** (`docs/effects-scoping.md`, `docs/effect-polymorphism.md`) is an agent's reading. Decision 19 forbids only an unused index added for later use.
- **Decisions 51–53** are not marked superseded.
- **Decision 15** (shallow handlers primitive) is revised by decision 62: handlers are deep.
- **Decision 57's "no row variables in the kernel"** is superseded by decision 62. Docs that cite it, such as `docs/effect-polymorphism.md`, are stale on that point.
- **Multi-shot.** Older records give three strengths. All are superseded by decision 63: multi-shot is ignored as a design goal.
- **Cancel errors.** The #186 comment of 2026-09-30 ("always receives 'cancelled'") is superseded: what SPEC §19 builds is the decision (decision 62).
- **`docs/effects-tr/08-decisions.md`** was written by an agent, with no user confirmation found.
- **"Recursion is an effect"** is superseded ("a pretty idea, not a hard req", 2026-10-01). It is still presented as current in `docs/rec-effect/README.md`.
- **PR #141:** the providers decision there is missing from `docs/decisions.md`.
- **SPEC §19 Status** says "in progress"; it also lists `unwindClause?`, and its §16 Open is out of date.
- **`experiments/README.md`** says TwoRun and FrameTheorems build; they don't. They matter only for binary laws, which are optional. It also lists EffModelRel's safety as open; it is proved.
- **The hard-stop memory and the frozen tier-2 list (#275–#280)** are not in force while we plan.

---

## 10. Rules for every agent

- **Nothing can break the borrow calculus.** BoLo's definitions may change where effects interact with borrows. The borrow guarantees may not weaken: each change comes with the proof that they hold for every program, effectful ones included.
- **Build the actual calculus.** If something can't be specified or proved yet, box it as an open question in the spec. Never narrow silently.
- **Say which world every result lives at:** Core σ=[], GE, SIB, PAPER, or `W`. A result at σ = [] is not a result at `W`.
- **Read before touching borrowing.**
  - Read the existing BoLo Lean in `Core/` and the paper: [CONF] `~/repos/borrow_lang/3764117.pdf`, and [TR] `~/repos/borrow_lang/3764117-supplement.pdf` for the full proofs.
  - The paper is not wrong. Where something will not reconcile, name what our side is missing.
  - Where a BoLo proof is reused or extended to effects, follow its printed technique rather than a shorter route; later lemmas reach for the technique.
- **No new relation families, twin constants or side mechanisms.** If you need one, stop and report. That is a finding about the structure.
- **Use `TW` for arising.** A counterexample must arise before it steers anything.
- **A blocker is a claim.** Report an obstruction only as a named `def … : Prop` that elaborates, or as a Lean configuration with every hypothesis discharged.
- **No `sorry` or `axiom` in landed work.** Record an unproved step as an enumerated `sorry` in experiments only.
- **No GitHub issues, comments or closures** unless the user has agreed the specific plan. No commits to main. Use worktrees.
- **Gate once.** Iterate with targeted `lake build <module>`; run `make gate` when the work is ready.
- **Quote the user's decisions at their strength.** "Not now" is not "never".
- **Comments and docs explain the thing, not its history.** No counts, no puffery.
