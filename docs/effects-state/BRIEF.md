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

1. **T1 is one clause.** At every stop, `wpG` requires the open Imm frames and records to equal those at entry (`Core/EffDefs.lean:40`), so no internal lend spans a suspension.
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

**Tier 1 first.** In the user's words: "Stage 1 … at tier 1 … proceeds regardless" (2026-10-02). Tier 2 (self-referential suspension) is in scope, under the hard-stop rule in §6.

---

## 6. Decisions, at the strength the user used

The full register, with sources, is [04](04-decisions.md). Only entries marked decided constrain a design, and even they stay open to the user. How code is built today is not a decision.

**Decided**
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
- **The hard-stop rule for tier 2** (2026-10-02). Tier 2 runs on a frozen finite list, and any item that spawns a new unknown halts it. In the user's words: "If the new work is n+1 and we are done, it's fine. If it's 3 and then 4 and then 5, no."
- **Process:**
  - unknowns first;
  - no changing an agent's scope mid-run;
  - **no GitHub issues until the plan and spec are agreed with the user**;
  - open questions are never issues;
  - the first-pass plan stays coarse.

**Defaults and deferrals (not prohibitions)**
- **Multi-shot:** "we also don't need multishot unless we get it for free" (2026-10-02).
- **Kernel equations and binary laws:** "optional and don't get pursued unless they become necessary for safety" (2026-10-02).
- **Higher-order operations:** "out of scope" in decision 57 (2026-10-01). Read this as not now.
- **Row variables:** decision 57 says none in the kernel (2026-10-01). Whether it survives the 2026-10-02 laws-first reset is unrecorded (OQ-13).
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
- OQ-16: the multi-shot criterion.
- OQ-19: runners are not user-facing.
- OQ-25: handler state.
- OQ-31: no step-indexing.
- OQ-38: site freshness is checked by the elaborator.
- The questions that depend on options nobody chose: OQ-41, 59, 63, 65 and 66.

**Posed on a misreading**
- OQ-1 and OQ-30 treat effects in a type as colouring.
- OQ-20 omits the TR's "fail to the lend".
- OQ-21 calls the built cancel-error policy a decision; see §9.

**Need the user now**
- **OQ-13:** do row variables stay out?
- **OQ-21:** the cancel-error discrepancy.
- **OQ-33:** how the hard stop applies under this structure.

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
- **Shallow vs deep.** Decision 15 says shallow handlers are primitive; SPEC §19's primitive is deep. Decision 15 is not marked revised.
- **Multi-shot** is recorded at three strengths. The user's words are in §6.
- **Cancel errors.**
  - The user decided on #186 (2026-09-30) that the canceller "always receives 'cancelled'".
  - SPEC §19, committed after that, re-raises the first error.
  - No record shows the user approved the change.
- **`docs/effects-tr/08-decisions.md`** was written by an agent, with no user confirmation found.
- **"Recursion is an effect"** is superseded ("a pretty idea, not a hard req", 2026-10-01). It is still presented as current in `docs/rec-effect/README.md`.
- **PR #141:** the providers decision there is missing from `docs/decisions.md`.
- **SPEC §19 Status** says "in progress"; it also lists `unwindClause?`, and its §16 Open is out of date.
- **`experiments/README.md`** says TwoRun and FrameTheorems build; they don't. It lists EffModelRel's safety as open; it is proved.

---

## 10. Rules for every agent

- **Build the actual calculus.** If something can't be specified or proved yet, box it as an open question in the spec. Never narrow silently.
- **Say which world every result lives at:** Core σ=[], GE, SIB, PAPER, or `W`. A result at σ = [] is not a result at `W`.
- **Read before touching borrowing.**
  - Read the existing BoLo Lean in `Core/` and the paper: [CONF] `~/repos/borrow_lang/3764117.pdf`, and [TR] `~/repos/borrow_lang/3764117-supplement.pdf` for the full proofs.
  - The paper is not wrong. Where something will not reconcile, name what our side is missing.
  - Follow printed proofs; don't take shorter routes.
- **No new relation families, twin constants or side mechanisms.** If you need one, stop and report. That is a finding about the structure.
- **Use `TW` for arising.** A counterexample must arise before it steers anything.
- **A blocker is a claim.** Report an obstruction only as a named `def … : Prop` that elaborates, or as a Lean configuration with every hypothesis discharged.
- **No `sorry` or `axiom` in landed work.** Record an unproved step as an enumerated `sorry` in experiments only.
- **No GitHub issues, comments or closures** unless the user has agreed the specific plan. No commits to main. Use worktrees.
- **Gate once.** Iterate with targeted `lake build <module>`; run `make gate` when the work is ready.
- **Quote the user's decisions at their strength.** "Not now" is not "never".
- **Comments and docs explain the thing, not its history.** No counts, no puffery.
