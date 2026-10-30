# 03 — What we were trying to do, and what happened

This is the chronological arc of the effects work in borrow-core, from #18 (2026-09-26) to the
withdrawn effect-calculus plan (2026-10-03). Each episode gives:

- the goal, in the user's words where they exist;
- what was built;
- what was proved or refuted, and at which world;
- why it stopped or changed direction;
- what is reusable.

A last section lists the failure patterns that recur across at least two episodes.

It is an inventory, not a design. Status words follow the shared vocabulary: PROVED,
REFUTED (with whether the counterexample arises), PAPER-ONLY, ATTEMPTED-FAILED,
REJECTED/ABANDONED, and OPEN.

**Worlds.** A result is located at one of five places, and none of them is the planned Kripke
world `W = (ρ, ls, σ)` of the draft spec:

- **Core**: the kernel's relation `vC`/`cC`, with `ewpTS` at the empty lend stack (σ = []);
- **GhostEnd**: one of the experiment's relations (`Relend`/`Open`, `vRL`/`cRL`, `vRLg`,
  `vRLs`, `vRLa`, `vRLk`);
- **EffModel / EffModelRel**: the sibling calculus, with no BoLo resources and no kernel
  machine;
- **paper**: `docs/effects-tr/`;
- **BoLo + `!`**: the paper-faithful layer used by the #170 spikes.

**Dates and times** are UTC, taken from GitHub timestamps. Commit dates are local time (−04:00).

**Quotations.** Quotes are the user's own words. Where a quote comes from the brief for this
inventory and no written record was found, it says so.

---

## Timeline at a glance

| dates | episode | outcome |
|---|---|---|
| 09-26 → 09-30 | 1. #18: effects as borrowed capabilities | requirements accumulate on the issue; still OPEN |
| 09-30 | 2. Scoping and S1, effects by elaboration (#151, #164–#166) | merged; S1b's `Fail` special case rejected (#168); superseded the same day |
| 09-30 | 3. Decision: effects are core; spikes #170 (#184, #185) | PROVED at BoLo + `!`; merged as experiments |
| 09-30 → 10-01 | 4. Kernel effects, SPEC §19 (#186: #187, #189, #191, #193, #204) and lowering (#205: #206, #207) | merged; PROVED at Core |
| 10-01 | 5. Surface on the kernel (#188: #214, #220); S2–S4 issues #155–#161 | #214 and #220 merged; #155–#161 never built in their staged form |
| 10-01 → 10-02 | 6. Recursion: #227, then the #231 spike, then #232 | #227 merged with gaps, its `rec` site withdrawn by #232 |
| 10-01 → 10-02 | 7. Effect polymorphism (#221) and first-order callbacks (#233) | #233 closed unmerged |
| 10-02 | 8. Phase A/B models (#235: #237, #247) | merged as experiments; laws PROVED at EffModelRel only |
| 10-02 | 9. `Clo` closures (#236, #238, #239, #240) | in the kernel (SPEC §22) |
| 10-02 | 10. Outlives (#241, #242, #243, #244) | in the kernel (SPEC §23) |
| 10-02 | 11. Effects TR and its satellites (#245/#248, #249/#255, #250/#252, #251/#254, #253/#257) | merged; mostly PAPER-ONLY, plus EffModelRel and Restrat Lean |
| 10-02 | 12. GhostEnd chain (#258 → #273, #281); regress question (#269/#272); prior art (#270/#271) | merged as experiments; tier decision and hard stop |
| 10-02 | 13. Stage-1 kernel lift (#274, branch `lift-stage1`) | stopped mid-transcription; not merged |
| 10-02 → 10-03 | 14. Tier 2: D16.1 (#282), stack step (#283), GFP refutation (#284), arising repair (#285), borrow callbacks (#286/#287) | #282/#283 merged; #284, #285, #287 open PRs; tier 2 halted |
| 10-03 | 15. Audit (#288/#289) | verdict CONSOLIDATE; target structure signed off |
| 10-03 | 16. Spec and plan workflow (#290, PR #461) | 170 issues filed and then deleted; plan withdrawn; spec unvalidated |

---

## 1. #18: effects as borrowed capabilities (2026-09-26 → 2026-09-30)

**Goal.** Issue #18 (created 2026-09-26) was titled "Experiment: effects as borrowed
capabilities". Its premise: "Handlers provide a capability as a borrow …; effect safety from
borrow soundness; divergence, allocation and IO as capabilities; rows are contexts only."

Over four days the user's requirements accumulated as comments (#18, 09-26 to 09-30):

- **No function coloring** (09-27): "no async/sync split in the source", with effects as
  capabilities passed as arguments.
- **User-definable effects** (09-27): "async is a user-definable effect that lives in the std
  lib — no privileged built-in".
- **Polarity** (09-27): the returning/suspending split is polarity, read off shift cancellation.
- **Unsafe operations as an effect** (`RawMem`), with handlers as an assurance ladder.
- **Memory as the outermost linear `State` handler** (09-27).
- **Erasure** (09-30): "Part of 18 needs to be effect handling is erased", refined to cost parity
  with the hand-written Rust program.
- **Seven target examples** (09-30), including the operator reconciler
  `… |> timeout(30s) |> retry(backoff) |> log(json(stderr)) |> kube(client)`.

**Built.** Nothing on this issue directly. It is the requirements record.

**Status.** OPEN. Its last comment (09-30 20:05Z) records the decision that effects are core
(episode 3).

**Reusable.** The requirement list, the target examples and the cost-parity criterion. These
are restated in the memory files `effect-handling-is-erased`, `no-function-coloring` and
`lead-axis-no-coloring`.

---

## 2. Scoping and S1: effects by elaboration (#151, #164–#166, #168; 2026-09-30)

**Goal.** Scope #18, then build a first slice. PR #151 (`docs/effects-scoping.md`) proposed that
"a handler's meaning is its elaboration into core". Safety would then come free from the
existing Fundamental Property, and "the erasure theorem's statement is empty by definition".

It named five places where the principle breaks: K1 (a spanning lend across a suspension), K2,
K3, K4 and K5. It also staged the work S1–S5 and opened #152–#162. Decision 48 recorded the
scoping, including the line "Effect rows never enter the core".

**Built.** Each PR merged within minutes of the next on 09-30, all by elaboration with no
kernel, rule or checker change:

- **#164 (S1a):** effect signatures, stateful handlers and `with`, elaborated to `withbor` plus
  `!` clause calls (SPEC §18, `Frontend/Elab/Effects.lean`). Cost parity was checked
  (`effects-map` against its hand-written version, 11/0/0).
- **#165 (S1b):** `Fail`, with built-in `try`/`catch`/`map_err`, a rule that a raising function
  answers `T + X`, and abort as a sum exit.
- **#166 (S1c):** laws on the elaboration schema in `Core/Handlers.lean` (`op_tail`,
  `op_answer`, `handle_fold`, `abort_passes`, `return_resumes`, `loop_abort`) and lowering
  reports.

**Proved.** The laws in `Core/Handlers.lean` are PROVED at Core. They are statements about the
elaborated terms, not about a handler construct.

**Why it changed direction.**

1. **The `Fail` special case.** S1b special-cased `Fail` in the elaborator. The user: "yeah i hate
   that" (memory `no-effect-ish-approximations`, 2026-09-30). #168 (09-30 19:14Z) restated the
   requirement as a general non-resuming handler class with no `Fail`-specific code. Within three
   minutes it was sharpened twice:
   - "error is a control flow effect full stop" (19:16Z);
   - "no sugar at all for now" (19:17Z).

   The user's diagnosis: "i don't want to do any sugar right now because i feel like starting
   with surface syntax caused the agent to think the syntax was what we wanted" (memory
   `mechanism-before-syntax`).
2. **The whole elaboration route was superseded.** At 20:05Z the user said: "I want effects to be
   core to the language, we aren't going to be able to implement them correctly with sugar, and
   we need to build them on a mathematical foundation backed by the literature" (#18; memory
   `effects-are-core`).

   S1 was then "a provisional probe", and #168 was "Paused: subsumed".
3. **Decision 48's wording was hardened.** The user later said: "I never said, btw that row
   doesn't enter core. You have a habit for turning not now into never" (2026-10-02; memory
   `not-now-is-not-never`). The correction is PR #234 (branch `decision-48-wording`), still
   OPEN.

**Reusable.**

- The cost-parity harness (counts files, reports).
- The tail-1 and abort laws, as statements of what an answering or abortive clause must do.
- The K1–K5 list. K1 became T1/#172, the thread through every later episode.

---

## 3. Effects are core: the #170 spikes (#184, #185; 2026-09-30)

**Goal.** #170 (09-30 20:10Z) asked: "Is a lexically scoped effect handler (Effekt / System Ξ …)
an instance of borrowing in BoLo?" The setting was the paper's calculus plus `!` only, "a
statement about BoLo, not about borrow-core".

**Built.**

- **#184** added `experiments/HandlersAsBorrows`.
- **#185** added `experiments/HandlersControl`, stacked on it.

Both merged 09-30 21:20Z.

**Proved** (all PROVED at BoLo + `!`, standard axioms):

- **Typing preservation.** `translate_typed` translates a Ξ fragment of answering handlers into
  `DerivesWf`.
- **Effect safety as a corollary of the FP.** `effect_safety` and `effect_safety_open`
  (`experiments/HandlersAsBorrows/HandlersAsBorrows/Safety.lean:55,71`).
- **The escape check.** `capability_not_outlives`.
- **Separation from Ξ.** `d_sepProg` separates BoLo + `!` from Ξ, but explicitly **not** from
  System C.
- **Aliasing refused.** `twoBlocks_refused`, `not_sharedCapture`.
- **State behind control** works, at bounded depth only. `no_uniform_comp`
  (`experiments/HandlersControl/HandlersControl/Behind.lean:53`) shows that no BoLo type solves
  the uniform capability type.
- **The reentry rule is admissible.** It is linearity of the state token
  (`not_borrowSpansForward`).
- **Continuation modes.** Multi-shot holds iff captures are persistent (`lam_bang_persistent`),
  and `forget` has no typing at `⊸` (`forget_not_lolli`).
- **The capture-bounded closure is BoLo's box.** `box_lolli_outlives_iff`.

**Why it moved on.** It succeeded. #186 (the kernel follow-up) was opened at 21:21Z.

**Reusable.** All of it. #184 is the result the user later said "we proved … and then never
built on it coherently" (memory `laws-first`, 2026-10-02).

---

## 4. Kernel effects: SPEC §19 and the lowering (#186, #205; 2026-09-30 → 2026-10-01)

**Goal.** #186 asked for native capture (`handle`/`perform`) with an effectful weakest
precondition `ewpTS` in the de Vilhena–Pottier shape, proving four things:

- compatibility lemmas for `do`, `let` and `handle`;
- every existing compat lemma lifted;
- the frames 6.64–6.66 over `ewpTS`;
- adequacy.

**User decisions added during the run** (#186 comments):

- "several effects at once … must work in this kernel work, full stop" (09-30 21:33Z);
- cancellation is not interceptable, option C, after the machine-checked `prog_stuck`
  (23:00Z);
- multi-shot is "low … only if it falls out for free" (10-01 00:30Z).

**Built.**

- **#187: SPEC §19, Entry 18.** It was revised three times within an hour:
  - two kinds of operation, with static per-site names instead of generative labels;
  - unwind mode and cancel;
  - structural qualifiers, with `raise` as abortive.
- **#189: `Core/EffWp.lean`.** `wpG`, `ewpTS` as a least fixed point, and the LIFO frame lemmas
  at abortive tables.
- **#191: the rules.** The machine primitives and head steps, determinism, `CTy.eff` rows, the
  rules `[sub]`, `[perform]`, `[raise]`, `[let]`, `[then]` and `[handle]`, and `fundamentalC`,
  `fundamentalD` and `adequacyD` extended.
- **#193: the unwinding forms of the borrow constants** (`withbor1U` … `sliceBorrowIU`) and
  `F_Σ` as a `ν` observation leaf (`Loop_Σ`).
- **#204: the six acceptance programs** (`Core/EffPrograms.lean`) and branch-per-call lowering
  of abortive operations.
- **#206 and #207: the remaining lowering.** State machines for captured continuations, cancel
  as the state's destructor, and tail-resumptive operations as direct calls. Every acceptance
  program compiles with `live 0` at cost parity.

**Proved.** PROVED at Core (σ = []). The kernel FP and every-run adequacy cover the effect
rules. `withswap` gets no unwinding form (SPEC §19).

**Why it moved on.** It was complete for its scope. #186 closed 10-01 02:04Z. The follow-ups
filed were:

- #188, the surface;
- #205, lowering (done);
- #208, lowering follow-ups;
- SPEC §19 *Open*: generative labels (T2), K3 policies, the relevant qualifier and multi-shot.

**Reusable.** This is the kernel that exists today. The audit (#289) judged its unary core "one
coherent proof algebra and conforms to the literature". Two of its pieces later became the
audit's top incoherences:

- **C1.** The lexical stop condition in `wpG`, `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)`
  (`Core/EffDefs.lean:39` @ main).
- **C4.** The pairwise-exclusive row classes for borrow callbacks.

---

## 5. Surface stages on the kernel; the S2–S4 issues (#188, #214, #220; #155–#161; 2026-10-01)

**Goal.** #188: replace S1's elaborated handlers with the kernel's, make `Fail` a library
effect, rebuild generators on `Yield`, and more. Principles: "Mechanism before syntax" and "No
effect-specific code in the elaborator".

**Built.**

- **#214 (stage 1, merged 10-01).**
  - Rows, `perform`/`abort`/`handle_with` and the unwinding borrows in the core text.
  - A certifying checker for §19's derivations.
  - `Fail` as `lib/fail.bc`. `grep -wE 'Fail|raise|map_err|to_result|Log' Frontend/` finds
    nothing.
- **#220 (stage 2, merged 10-01).** `Yield[T]` as a library effect, `for` over a generator as a
  handler site, and the old generator system removed.

**Kernel limits these met**, each recorded rather than routed around:

- an error cannot carry an owned value (#215, OPEN);
- a `!` clause cannot capture non-`!` values (#216, OPEN until #232's elaboration);
- `retry` needs functions over computations (#161);
- a generator cannot hold a capability across a `yield`, because a cancel would have to hand
  back a residual (#220).

**The S2–S4 issues.** #155 (named capabilities), #156 (IO bundles), #157 (`|>`), #158 (`rec`),
#159 (`Yield`), #160 (projection operations), #161 (stored effectful callbacks) and #162
(suspension with input) are all still OPEN. They were written for the elaboration route of
decision 48. Their content was later taken up piecemeal:

- #158 by #227 and #232;
- #159 by #220;
- #161 by #221 and #233;
- #157 by #233's `|>`.

None was built in its staged form. #160's derived type (T21) and #162's K1/K2/K3 remain open
theory (#172).

**Why it stopped.** #188's comment (10-01 22:10Z): "Stages 4–5 on hold until the second-class /
System C spike reports … #227's `rec` elaboration is provisional."

**Reusable.** The library effects (`Fail`, `Yield`), the certifying checker's effect rules, the
drop-glue insertion, and the corpus at parity.

---

## 6. Recursion: #227, the #231 spike, #232 (2026-10-01 → 10-02)

**Goal.** #188 stage 3 (#158): "recursion as an effect". The design in `docs/rec-effect/` had
the user's example `fib |> memo(cache) |> fuel(1000) |> fix`.

**Built.**

- **#227 (merged 10-01 21:50Z).** A recursive group is an SCC. Self-calls are the group's `rec`
  operation, handled by a site per group. One kernel constant, `bounded_fix[A, C]`
  (`Core/BoundedFix.lean:91`, `boundedFix_compatX`, PROVED by induction on the budget at every
  row). Drivers `bounded`/`deep`, and the effect `Exhausted`, found by its structure.
- **#229 and #230** were filed at once with #227's gap list:
  - no resuming operations or answering capabilities inside a recursion;
  - no loops inside one;
  - no generic recursion;
  - no members with different result types.

**Redirect.** The user saw the gaps as a symptom: "there must be something theoretical we're
missing", and "I just don't want to get in the trap of implementing shallow solutions and
thinking we can patch them later when a deep solution might be a fundamentally different thing"
(2026-10-01; memory `deep-before-shallow`). #229 and #230 were parked (10-01 22:10Z): "Don't
patch it piecemeal." The success criterion: "what i want is a bunch of things falling like
magic not something that half implements what we were looking for with no obvious way of
progressing."

**Built next.**

- **#231 (spike, merged 10-01 22:46Z).** `docs/second-class-and-system-c.md` and
  `experiments/SecondClass`. Its finding: the gaps "are not one family". One principle closes
  five of eight with no kernel change: effectful code is `!` code with its environment passed
  at each call, and a recursive group is the fixed point of a generator (Cook–Palsberg).
  - PROVED at Core: `boundedFixEnv_compatX`, `recLog_derives`, `d_handleAbortCapture`.
  - PROVED in the experiment: `handleAt_compatC`
    (`experiments/SecondClass/SecondClass/Prompts.lean:75`), handling at a run-time name.
- **#232 (merged 10-02 00:15Z).** "Closure conversion at the seams" (SPEC §21, decision 59):
  - the `rec` operation and site are removed;
  - layers become generator transformers;
  - #216's clause captures are handled.

  It closes three of #229's items. The user: "recursion is an effect was more a pretty idea than
  a hard req" (2026-10-01; memory `structured-recursion-only`).

**Still open.** A loop inside a recursion turned out to be "no handler can wrap a div
computation" (SPEC §21 *Open*). It was parked "as not a priority" (#229, 10-02 00:23Z). Branch
`loophandle` (`docs/handlers-over-div.md`, 10-01) holds the spike notes, "parked by the user
before any Lean or probe was written". Also open: effects under `deep`, generic recursion,
recursion through a site (#173), and `memo` (#211).

**Reusable.** `bounded_fix` and its proof, the generator fixed point, `d_handleAbortCapture`,
and `handleAt_compatC` as the semantic half of generative names.

---

## 7. Effect polymorphism and first-order callbacks (#221, #233; 2026-10-01 → 10-02)

**Goal.** #161: stored effectful callbacks. #221 (`docs/effect-polymorphism.md`, merged 10-01)
recommended "Option 2: monomorphisation over static names":

- no row variables;
- ports for provided control effects;
- tunneling for the rest;
- site freshness R3.

The user's choices became decision 57, which records "Operations that take computations
(higher-order effects) are out of scope".

**Built.** #233 (branch `effect-callbacks`, opened 10-02 02:21Z) implemented R2a: computation
parameters, closure values with lent environments, ports, `|>` and `lib/callbacks.bc`. Its own
target table:

- **working:** `retry` over a lend, `|>`, `each`/`fold`, shared capabilities, the parser, and
  callbacks passed on;
- **pending:** callbacks taking callbacks (rank 2), stored or returned computations (R6), policy
  values, effectful codata, and recursion through a value with a capability.

It gave the precise limit: the checker compares `∀`-binder types by `=` without α-conversion.

**Why it stopped.** Closed unmerged (10-02 04:10Z): "It solves the first-order case only, and
the higher-order cases … were left pending behind workarounds. The goal was the general form,
so we're stepping back to restate what we're trying to do before building again."

The user's words, as relayed in this inventory's brief: "I literally said i don't want a first
order solution". No written record of that sentence was found in the tracker.

Within the hour the user also said:

- "whatever we built, it isn't an effect algebra or we wouldn't be having these problems";
- "I think we basically need to find the laws that we have to implement instead of trying to
  wing it" (2026-10-02; memory `laws-first`).

And on process: #233 "got its higher-order targets bolted on mid-run, built the first-order
version, and parked the rest" (memory `no-midstream-redirects`). The user: "No we get bad results
by changing them midstream."

**Reusable.**

- The branch is "kept for reference".
- `docs/effect-polymorphism.md`, including its provided/tunneled split and the renaming lemma
  (stated, not built).
- The list of pending targets became phase A's acceptance list (episode 8).

---

## 8. Phase A and B: executable effect model and binary relation (#235, #237, #247; 2026-10-02)

**Goal.** #235 (10-02 04:53Z): "a standalone executable model of the effects design, checking
that it has the properties we want before any kernel surgery". The design basis:

- adjoint CBPV;
- effects as algebras at every computation type;
- capabilities as comodels;
- the comodel–model tensor;
- instances with `ν`.

It "Supersedes: the closed #233 (first-order only)". The acceptance list was the laws, the
programs "that broke us", and the four refusals. The issue was filed after launch, at the
user's prompt: "Make sure we're running these off of GH issues" (memory `agents-off-issues`).

**Built.**

- **#237 (phase A, merged 10-02 06:05Z)**: `experiments/EffModel` and `docs/effect-model.md`.
  - **Laws:** 21 laws checked by `#guard` over 952 generated contexts.
  - **Programs:** all 10 run with no special case, including callbacks taking callbacks, stored
    computations, a policy value, and a generator holding a resource.
  - **Refusals:** 11. An ablation shows T1 necessary.
  - **The independence principle** "fell out" as one rule covering multi-shot persistence, 4.A,
    #216 and #9.
- **#247 (phase B, merged 10-02 15:32Z)**: `experiments/EffModelRel`. A binary relation with no
  step index, with worlds as name bijections.
  - **PROVED at EffModelRel:** `fundamental`, `soundness`, algebraicity, the H-laws, tensor,
    idem-ν/new-ν/ν-ν, no accidental handling, and `resource_safety`.
  - **REFUTED at EffModelRel:** ν/op at a multi-shot operation (`nu_op_fails_multishot`,
    `experiments/EffModelRel/EffModelRel/Examples.lean:223`). It is a `CtxEq` counterexample in
    the sibling calculus, so arising in the typed world is not applicable.
  - **The method's limit:** `no_negative_domain` (`Obstruction.lean:35`), i.e. T15.
  - **OPEN:** T1 soundness.

**Why it moved on.** Phase B handed T1 and the lift to the TR (#245) and the narrow run (#249).
The user: "we don't need multishot unless we get it for free" (2026-10-02; #235 comment 14:48Z;
memory `multishot-only-if-free`). "Still worth understanding" became side issue #246.

**Status.** Every law is PROVED only at EffModelRel, which has no resources, no machine and
unmoded `CtxEq`. The audit's C3: "Every algebraic law lives off the kernel."

**Reusable.**

- The executable matrix as a regression oracle.
- The independence principle.
- The instance/`ν` design, which became stage 1's item 1 and the spec's K-NAME.
- `no_negative_domain` as the T15 tripwire.
- The TR's three rule fixes (see episode 11).

---

## 9. `Clo` closures (#236, #238, #239, #240; 2026-10-02)

**Goal.** #236: a `Clo` closure callable through a `Mut` borrow, "higher-order from the
start". Requirements: called repeatedly, passed at any depth, nested, stored or returned within
captured lifetimes, dropped, and coerced between the three modes. The issue says it is "what
every higher-order effect attempt (#161, #233) built by hand".

**Built.**

- **#238 (merged 10-02 06:05Z)** found `Clo^c A B ≜ νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`. It is an
  abbreviation needing two relaxations of `ν` positivity, proved in a fork of Core.
- **#240 (merged 10-02 07:12Z)** lifted the patch into the kernel as SPEC §22:
  - `Core/Clo.lean` (`cC_clo_iff`, `clo_coind`);
  - `Core/CloRules.lean` (`d_callMut`, `d_ofFn`, `d_once`);
  - `lib/clo.bc`;
  - all six requirements as corpus programs.

  The fork was deleted. The name `Clo` is provisional (decision 60), following the user's
  "Our names, not Rust's".

**Proved.** PROVED at Core. The FP and adequacy are unchanged.

**Why it moved on.** It was complete. Strict outlives costing extra scopes became #241.

**Reusable.** `Clo` is the object the Mut-cell lemma (episode 11) and `[gen]` (episode 13)
build on. This episode is the one case where an experiment fork was promoted cleanly into the
kernel.

---

## 10. Outlives (#241, #242, #243, #244; 2026-10-02)

**Goal.** #241: "where does BoLo's strict outlives (`⊏`) cost us, and which of those places admit
a non-strict `⊑`?". The issue adds: "the relaxation is an extension, not a correction".

**Built.**

- **#242 (spike, `experiments/Outlives`, `docs/outlives-strictness.md`).**
  - PROVED at the probe: K1, the non-strict box rule (`vC_outlivesL`, `boxIL_compatC`), and K2,
    the non-strict `withbor` side condition (`withbor2Le_compatX`), with
    `fundamentalL`/`adequacyL`.
  - Obstructed in Lean: the `Imm`/`Mut` rules under `[]I` when non-strict
    (`not_vC_outlives_le`), and non-strict strata (`no_nonstrict_stratum`, Cantor).
- **#244 (merged 10-02 13:10Z), SPEC §23, decision 61.** K1, E1 (`'main`), B1 (lifetime bounds
  `where S: 'c`) and K2 at every rule. Scaffolding in the `clo-*` programs went from 10 scopes,
  6 cells and 18 `boxed` annotations to 1, 1 and 4.

**Proved.** PROVED at Core. `Paper/` and `Support/` are unchanged.

**Reusable.** `no_nonstrict_stratum` reappears as the T15 guard in the Mut-cell lemma (episode
11). The strict-strata cut-off is one of #272's five cut-offs that keep the relation step-free.

---

## 11. The effects TR and its satellites (#245/#248, #249/#255, #250/#252, #251/#254, #253/#257; 2026-10-02)

**Goal.** #245 (10-02 14:30Z) asked for a paper proof "written before the final mechanisation
and the kernel lift. Those then transcribe it, the way the BoLo mechanisation transcribes
[TR]". The factoring: BoLo's resource world plus local control, meeting at three points.

Several inputs were added after launch, marked "not a change to the running brief":

- **A decisive test:** "T1 should be a theorem, not a rule".
- **External review:** a free-algebra lfp relation, capture rebasing, T1 as a precondition, and
  destructors limited to answering operations.
- **The runner framing.** The user called it "kind of genius" and voiced the concern "wildly
  complex to reason about", with the criterion that it is adopted only if it removes proof work.

**Built and found:**

- **#248, the TR (`docs/effects-tr/` §§1–12, merged 10-02 15:30Z).**
  - PAPER-ONLY: unary FP, resource safety, operational soundness, the destructor form, and
    writers commute.
  - **Three of phase A's rules let programs go wrong.** Each is machine-checked against phase A's
    model and fixed in the TR's rules.
  - "T1 is not needed once the lend owns its capability". T1 belongs to the lift.
  - OPEN: O1 (ν/op), O2/O3 (T1 in the lift), O4.
- **#255, the narrow run (#249, `experiments/EffModelRel`, merged 10-02 17:06Z).** The brief was
  adjusted before launch.
  - The TR's three fixes are mechanised (`movedLend_not_moded`, `resEscape_not_moded`,
    `retTwice_not_moded`).
  - `Rw` rows of `(instance, lifetime)` replace `Eb`.
  - Effect and resource safety with lends (`safety`, `safety_obs`).
  - **REFUTED at EffModelRel:** ν/op at a linear operation too (`nu_op_fails_linear`,
    `Ownership.lean:72`). O1 restated over moded contexts, OPEN.
  - **The cell lemma** is PROVED in a stratified model of places (`Cell.lean`). T1 is the return
    of a borrow at the place's drop.
  - **T15 appears only without strata** (`no_place_store`, `Cell.lean:1239`).
  - The typing from the calculus into the cell model is "not built".
- **#252, the adjunction framing (#250, `docs/effects-tr/13-adjunction.md`,
  `14-stored-continuations.md`).** Verdict: "The `F ⊣ U` framing removes no obligation." Capture
  rebasing does reduce open work: O3 reduces to one stated lemma, L14.4/O5.
- **#254, the Mut cell (#251, now `docs/effects-tr/15-mut-cell.md`).**
  - T14.5 (now T15.5) is PAPER-ONLY for rebased continuations, via `clo_coind` and `d_callMut`.
  - The internal-lifetime case is OPEN as O15.1. Route 1 (refold at the old lifetime) is
    REFUTED by `refoldKripke_false` (`experiments/LoopBorrow/LoopBorrow/Obstruction.lean:245`),
    and `refold_fails_at_consumer_frame` shows the failing list arises. Route 2 is not derived.
  - #256 renumbered O14.x to O15.x.
- **#257, Restrat (#253, `experiments/Restrat`).**
  - The audit found no definition relating outer and inner lifetimes by `↓`.
  - Naturality is PROVED for most definitions.
  - **REFUTED:** naturality at `𝒱⟦Mut 'a (Imm 'b 1)⟧` (`mut_not_natural`,
    `Restrat/MutCounterexample.lean:148`). Whether the witness arises was **not checked**
    (`experiments/Restrat/README.md:96`).
  - `wp` naturality OPEN.

**Why it moved on.** `mut_not_natural` was read as requiring "freeze them into `own` cells, then
re-lend". That reading started the GhostEnd line (#258), whose brief said "Also check whether
`mut_not_natural`'s witness arises". GhostEnd's README (step 3b) answers only "The shape arises
… Whether `ρ₀` with these numerals arises in a run is not checked".

**Reusable.**

- The TR's §§1–12 structure and transcription guide.
- The three rule fixes.
- T1 as the `withswap` discipline.
- The Mut-cell lemma (PAPER-ONLY), which the stage-1 plan treated as fully specified (`[gen]`,
  D14.7).
- The rebasing/naturality audit.

---

## 12. The GhostEnd chain, the regress question and the tier decision (#258 → #273, #281; #269/#272; #270/#271; 2026-10-02)

**Goal.** Close O15.1: a lend opened inside a suspended computation and still open at the
suspension, i.e. T1 on the continuation side. The method was ghost-ending internal `Mut`
borrows at freeze and re-lending them fresh at resume. A sharpened brief said "re-derive, don't
transport".

**The chain.** Each PR merged into `experiments/GhostEnd`, all at GhostEnd's relations, none at
Core:

| PR (issue) | proved | left open |
|---|---|---|
| #259 (#258) | `segment_fundamental`; `ewpTS_M_frameR` (6.65 at a resuming table); straight-line borrowers; `spans_two_yields` | general typed borrowers; drop at cancellable yields; nested lends; 6.64/6.66/6.150 lifts |
| #261 (#260) | `Open`/`RBody`; loops (`loop_spans_yields`); drop (`withborR_compat`); `ewpTS_M_antiFrameR` | frames holding `'x`-values; rules with effectful premises |
| #263 (#262) | lend table `TabAt`; tuples (`LOk`); closures by re-derivation (`TV`, `CloL`) | "a pure piece handed a `CloL` closure": not routine; `KernelInvariant` |
| #265 (#264) | `KapRelR` positive; route (b) `vRL`/`cRL` defined | every route meets `URelend` |
| #267 (#266) | key steps of non-routine compat lemmas at `vRL`/`cRL`; **REFUTED** for `vRL` as merged: `thunkF_RL_fails_below_at` (`RLCompat.lean:471`, hypotheses discharged at numerals; arising not checked); fix `vRLg` | nested lend spanning a stop; `Imm` lend spanning a stop |
| #273, #281 (#268) | `'x` in a payload closed; `Imm` lend (`ewpTS_I_frameR`); `nested_relend` (`Nested.lean:164`); `nested₂_relend` | "No unknown remains before the kernel lift": `NestRelend` from typing, `bodyAtD` form, the 6.150 lift |

Each step added a relation or predicate family (`Relend`, `Open`, `RBody*`, `TV`/`CloL`,
`KapRelR`, `vRL`, `vRLg`). The user's later account: "Each agent closed its own lemma by adding a
relation family (vRL, vRLg, vRLs, vRLa, vRLk). I relayed 'it reduces to one more lemma' as
progress" (memory `structure-before-briefs`, 2026-10-03).

**The regress question (#269, 10-02 22:10Z).** The user: "it feels like we're endlessly going
down further and further orders… 'everything is reduced to one lemma' and then that lemma is
reduced to one lemma…". The inventory brief relays a later form: "endless path of 'Everything
is reduced to one lemma'".

**PR #272** (`docs/effects-tr/16-regress.md`) answered it:

- **The common failure** is "a lifetime opened inside the suspended computation that is still
  open at the suspension": the self-referential state machine.
- **The positions are finite.** A single induction (GFP, D16.2) at a relation indexed by the
  stack of open internal lends would subsume them.
- **No recursive domain is needed** given five cut-offs.
- **Verdict:** "(a), with a finite named residue". Choosing between (a) and staying at T1 "is a
  language decision about self-referential suspension, not a proof question".

**Prior art (#270, PR #271, `docs/prior-art-suspension-borrows.md`).** The standard slice is
"No borrow of data owned by the suspended computation may be live at a suspension that reifies
the continuation". This is Rust's E0626 and already SPEC §19's rule. The recommendation: keep
it, and bank GhostEnd "to reopen only for a forcing program".

**User decisions (#268 comments, 10-02 22:36–22:37Z):**

- "this is the final attempt to find the bottom". The target was GFP over D16.1; if it fails,
  the language ships at tier 1.
- **The hard stop:** "My concern is going to be that one of that finite lists itself has a
  regress so we should make that a hard stop" (memory `hard-stop-on-regress`). Tier 2 proceeds
  only on a frozen six-item list (#275–#280). Any new unknown, reduction or construct halts it.
  "Stage 1 of the kernel lift … proceeds regardless."
- #258–#270 were closed at 22:40Z as "Resolved by the research chain".

**Reusable.**

- The lfp-lifting technique for printed frame lemmas (`ewpTS_{M,I}_frameR`,
  `ewpTS_M_antiFrameR`). The audit says: "one technique. Keep it."
- `nested_relend` and `TabAt`.
- The prior-art slice.
- §16's five cut-offs.

---

## 13. Stage-1 kernel lift (#274, branch `lift-stage1`; 2026-10-02)

**Goal.** #274 (10-02 22:39Z): "the safe effect algebra at tier 1". It would lift the research
into `Core/` with T1 kept. The items:

- instances with `ν`;
- rows of `(instance, lifetime)`;
- handler extents `∀'h`;
- `[gen]`;
- the `withswap`/`withtake` split;
- runner finalisers;
- continuations in frames;
- the generalised relation at σ = [].

A comment added derived re-borrowing of places across suspensions.

**Built.** The plan comment (23:07Z) ordered eight PRs. It also found that four decisions were
answered nowhere in the TR or experiments:

- **D1:** where instance variables live without a new `CDerives` index;
- **D2:** the machine's fresh-name supply;
- **D3:** the kernel form of a continuation held in a frame;
- **D4:** `withtake`, "defined nowhere".

PR 1 started with `[gen]`. The only commit, c9b3694 on `lift-stage1` (10-02 19:29 −04:00), is
"WIP (#274, not for merge): [gen] transcription in progress, stopped". It has `Core/AffTy.lean`
and `Core/Gen.lean` (`genE`, `Qgen`, `ewp_gen`). T14.4, T14.6 and the `CDerives` rule were not
written, and the file cites a `[spec §24]` that no SPEC on any branch contains (spec draft
08-correspondence).

**Status.** ATTEMPTED and stopped. The issue is still OPEN. This inventory's brief records the
lift as rejected. I found no written record of who rejected it or why.

What the record does show:

- PRs 3, 5 and 7 were blocked on D1–D4.
- The user directed a "Final run: prove GFP" (#279, 10-03 01:51Z) instead.
- The audit and the draft spec list `Core/Gen.lean` as "rebuild" (spec 08-correspondence:349).

**Reusable.**

- `Core/Gen.lean`'s `ewp_gen` (L14.3), proved on the branch.
- D1–D4 as exact statements of what the TR left undecided. They reappear as OQ-14/OQ-28/OQ-65
  and as spec OQs.

---

## 14. Tier 2: D16.1, the stack step, GFP, arising, borrow callbacks (#279 → #287; 2026-10-02 → 10-03)

**Goal.** #279, from the frozen list: "Write the stacked relation D16.1 and the generalised
fundamental lemma GFP (D16.2) in Lean … so that at σ = [] it is `fundamentalC`."

**Built.**

- **#282 (merged 10-03).** D16.1 is definable by structural recursion on types (`vRLs`, `cRLs`,
  `Stacked.lean`). It equals `vC`/`cC` at `[]` (`gfpAt_nil_iff`). GFP is stated, not proved.
- **User criterion** (10-02 23:54Z): "If the new work is n+1 and we are done, it's fine. If it's
  3 and then 4 and then 5, no."
- **#283 (merged 10-03).** The three remaining lemmas are proved "once, for every stack":
  `stack_step_other`, `stack_step_reborrow` (`StackStep.lean:563`), `stack_step_imm` and
  `relendableS_sep`. Some hypotheses were added (`AllCross`, `hβ`).
- **#284 (branch `gfp`, PR OPEN): "Final run verdict: Blocked".**
  - REFUTED at GhostEnd D16.1: `not_gfp : ¬ GFP` (`experiments/GhostEnd/GhostEnd/Below.lean:282`
    @ `gfp`).
  - The failing cases are `lam`/`allI`, which #266 had classified as routine. Borrow callbacks are
    values read at σ, never at σ·y.
  - An off-list construct is needed, so tier 2 halts by the hard stop.
- **#285 (branch `gfp-arising`, PR OPEN).** "use the existing arising machinery, as the paper
  does" (user, #279 comment 02:36Z).
  - **The witness does not arise.** `wpG_below_not_arises`; `below_excluded`
    (`Arising.lean:446` @ `gfp-arising`).
  - D16.1 restated with a `TabAtS` guard at `U`, `⊸` and `∀` (`vRLa`), and `lam_RLa`/`allI_RLa`
    proved.
  - Open: "#275's borrow-constant row has to read its callback at `σ·y`".
- **#287 (branch `borrow-callbacks`, PR OPEN; issue #286).** The user: "It doesn't feel like a
  design choice; it feels like there is a right answer."
  - Literature survey: `docs/effects-tr/17-borrow-callbacks.md`.
  - Diagnosis: D16.1's world has two components (resource, lend stack), but its clauses
    quantified over resource extensions only. The standard Kripke quantifier is over the product
    order.
  - `callback_ext` (`Extend.lean:131` @ `borrow-callbacks`) is PROVED at `vRLk`.
  - GFP at `vRLk` is not shown.

**Why it stopped.** By the hard-stop rule, tier 2 halted. #284 needed an off-list construct, and
#285 and #287 each added a further relation (`vRLa`, `vRLk`). The audit states this: "By #279's
hard stop, tier 2 has halted (#284, #285 and #287 each brought a new reduction or construct), so
the language ships at tier 1."

**Reusable.**

- `stack_step_*`, as the lfp lift at every stack depth.
- The product-world diagnosis of #287, which the audit made its central input and the spec made
  `W = (ρ, ls, σ)`.
- The arising check of #285, as the method for any future refutation.

---

## 15. The audit (#288, PR #289; 2026-10-03)

**Goal.** "Does what we've built cohere as one proof algebra, use the existing machinery
consistently, and match the established algebra of effects? Or has it become ad-hoc wiring and
proof-grinding?" (#288, user 2026-10-02).

**Built.** `docs/effects-audit.md` on `effects-audit`, PR #289 OPEN. **Verdict: CONSOLIDATE.**

- **Coherent:** the kernel's unary core.
- **Incoherent:**
  - C1, `wpG`'s lexical stop condition;
  - C2, answering and control handlers with no stated relationship;
  - C3, every law off the kernel;
  - C4, pairwise-exclusive borrow row classes;
  - M1/M2, five stacked relations beside `vC`/`cC`.
- **The unifying structure:**
  - one `Sig`, with handlers as models and capabilities as comodels;
  - one `IsModel` lemma;
  - one Kripke world `W = (ρ, ls, σ)` with σ the `TW`'s own `ps`/`rs`;
  - one row-generic borrow per printed constant under `TableOK`.
- Seven decisions Q1–Q7.

The audit says: "None of this is a machine-checked obstruction. It is a reading of the code and
the docs."

**User reaction** (2026-10-03, memory `structure-before-briefs`): "A lot of what its
recommendations are are what i thought i asked for to begin with and i am confused why it wasn't
done that way." Then the sign-off (memory `effect-calculus-spec-first`): "Make sure the agents
are building the actual effects calculus not an approximation of it." "We need a full
specification before we start any kernel work, with any open questions carefully called out and
boxed."

**Reusable.** The coherence map, the ranked incoherences, and the target structure. The user
signed off on the target structure together with the critic's seven corrections.

---

## 16. The spec and plan workflow (#290, PR #461, issues #291–#460; 2026-10-03)

**Goal.** #290 (10-03 05:36Z): a full specification with boxed open questions, then a
dependency-ordered plan, behind a SPEC-DONE gate.

**Built.** A workflow wrote `docs/effects-calculus/` (00–08, 99, `plan.md`) on branch
`effects-calculus-spec` (commit 3cb51da, 10-03 04:53 −04:00). It opened PR #461 and filed
**170 issues, #291–#460** (archive: `scratchpad/plan-issues/`). By title prefix these include:

- 41 "Decide" issues, one per user-decision OQ;
- 34 "Kernel";
- 27 "Probe".

At 09:04Z it closed existing issues as "Superseded by the effect-calculus specification and
plan (#290)". These included #250, #275, #279 and #280. PR #461 itself states: "the validation
pass reported major findings against the spec (S1-S16) and the plan (P1-P12) that are not yet
resolved". The issues were filed anyway, with the residue "boxed at the end of plan.md".

**Why it stopped.** The user, 2026-10-03 (memories `structure-before-briefs`,
`no-issues-for-open-questions`):

- "needed to go through a validation and consolidation stage before any issues were opened";
- "don't open issues for open questions at all";
- "Don't script or allow the creation of any issues until we have a plan/spec written out and
  agreed on";
- "I think maybe we don't go down too far in granularity on the first pass".

The user approved deleting all 170 issues, and they were deleted. The closed issues were
reopened at 11:24Z ("The plan issues this was closed in favour of have been withdrawn"). Commit
d7809ac (10-03 07:24 −04:00) withdrew `plan.md`.

**Status.** The draft spec has FAILED validation. #290's body lists the consolidation order:
check the OQs against existing work, triage decisions, fix the findings, re-validate.

The user also said: "we aren't starting from _zero_ on effects, we got a lot working before we
kind of hit the limits of our first approach" (memory `effect-calculus-spec-first`). This
inventory (`docs/effects-state/`) is the consolidation's input.

**Reusable.**

- The spec's object and id structure.
- The 68 boxed OQs as a list of questions, not answers.
- 08-correspondence's map of every id to code.

---

## Recurring failure patterns

Each pattern below is evidenced by at least two episodes.

### P1. A narrow or shallow build whose gap list forced a restart

A mechanism was built for the first case and shipped with a list of pending cases. The user
judged the list a symptom of a missing structure, and the work was redone.

- **Episode 2:** S1 by elaboration, superseded the same day by "effects are core".
- **Episode 6:** #227's `rec` site and its gap list, parked ("Don't patch it piecemeal") and
  replaced by #232.
- **Episode 7:** #233's first-order callbacks, closed: "It solves the first-order case only."

In the user's words: "a bunch of things falling like magic not something that half implements
what we were looking for".

### P2. Surface spelling or role-by-shape taken as the mechanism

- **Episode 2:** S1b built the spellings `try`/`catch`/`map_err` as a `Fail` special case: "starting
  with surface syntax caused the agent to think the syntax was what we wanted".
- **Episodes 5 and 6:** library roles recognised by shape rather than declared:
  - the exhaustion effect found "by structure" (#227);
  - a heap driver "recognized by its type" (#227);
  - a layer "recognised by its type" (#232).

The audit raises this as Q6, "typed role declarations instead of shape recognition".

### P3. Mid-run changes to an agent's scope

- **Episode 7:** #233 "got its higher-order targets bolted on mid-run" (memory
  `no-midstream-redirects`).
- **Episode 4:** #186's three user decisions arrived while stages 1–3 were running. SPEC §19 was
  revised three times in an hour (#187 comments).
- **Episode 11:** #253 received a "Refinement … sent to the running agent as a correction of the
  brief". #245 received an acceptance test "after the TR agent started". #249's brief was
  adjusted just before launch.

The user: "No we get bad results by changing them midstream" (2026-10-02).

### P4. "Reduces to one more lemma", with a new relation family per step

- **Episode 12:** every GhostEnd PR (#259, #261, #263, #265, #267, #273) closed its item and
  reported a narrower open item. It introduced `Relend`, `Open`, `RBody*`, `TV`/`CloL`,
  `KapRelR`, `vRL` and `vRLg`.
- **Episode 14:** `vRLs`, `vRLa` and `vRLk` followed, each from a different PR.
- **Episode 11:** the same descent from the TR's O3 to L14.4/O5, to O15.1, to naturality.

The user named it on #269. The memory `structure-before-briefs` records the cause: "Nobody held
the global structure, because no written target existed to brief against." The hard-stop rule
(episode 12) was the countermeasure.

### P5. Laws and theorems proved at a world other than the kernel's, then not lifted

- **Episode 2:** the S1 laws are about elaborated terms, superseded when the kernel construct
  arrived.
- **Episode 8:** every algebraic law is proved only at EffModelRel.
- **Episode 11:** the TR proves its results on paper for phase A's calculus. The narrow run's
  cell lemma lives in a separate model, and "the typing … into it is not built".
- **Episodes 12 and 14:** every GhostEnd result is at a GhostEnd relation.

The audit's C3 and M1/M2 are this pattern. Its remedy is the single world `W`.

### P6. A refutation stated over all configurations, with arising not checked, steering the work

- **Episode 11:** `mut_not_natural` was refuted "over all resources", and whether its witness
  arises was "not checked". It still chose the ghost-end route (#258).
- **Episode 14:** `not_gfp` produced a "Blocked" verdict and a hard stop. #285 then showed the
  witness does not arise (`below_excluded`).
- **Episode 12 (also):** #267's `thunkF_RL_fails_below_at` changed the relation to `vRLg`. Arising
  was not checked.

### P7. Carried-over residual items that never got done

- **Episodes 12 and 14:** the lift of [TR] 6.150 to resuming tables appears as untranscribed or
  open in #261, #263, #273, #282, #284 and #285. It was put on the frozen list as #277 and never
  run. The audit: "The 6.150 lift is missing."
- **Episodes 7 and 15:** the renaming lemma (equivariance of `CDerives` under name renaming) was
  stated in #221 and #233 ("not built") and reappears as audit step 6.
- **Episodes 4, 11 and 13:** `withswap` has no unwinding form (SPEC §19, #193), which becomes O8
  in the TR and D4 (`withtake`) in #274.

### P8. Work planned or filed before its target structure was agreed

- **Episode 13:** #274's plan found four undecided kernel questions (D1–D4) and started PR 1
  anyway. It stopped mid-transcription.
- **Episode 16:** 170 issues were filed from a spec whose validation had failed.
- **Episode 12:** the frozen tier-2 issues #275–#280 were filed as work items. They were later
  closed as superseded, then reopened.

The user: "needed to go through a validation and consolidation stage before any issues were
opened". The memory `structure-before-briefs` says: "write the target structure down first and
brief every agent against it."

### P9. Recorded decisions stronger than the user's words

- **Episode 2:** decision 48's "Effect rows never enter the core" was later cited as a constraint
  (#161's doc called row variables "forbidden by decision 19"). The user: "You have a habit for
  turning not now into never."
- **Episode 15 (context):** runners were recorded as "OUT … a dead end" (memory
  `effects-are-core`). On 2026-10-02 this was softened to "Don't cite 'runners are a dead end'
  against it", after the user called the BoLo-as-runner framing "kind of genius".

---

## Sources read

**GitHub issues** (bodies and comments, `gh issue view --json`):
#18, #152–#162, #168, #170, #172, #173, #186, #188, #205, #208 (title), #215, #216, #229, #230,
#235, #236, #239, #241, #243, #245, #246, #249, #250, #251, #253, #258, #260, #262, #264, #266,
#268, #269, #270, #274, #275, #276, #277, #278, #279, #280, #286, #288, #290.

**GitHub PRs** (bodies and comments):
#151, #164, #165, #166, #184, #185, #187, #189, #191, #193, #204, #206, #207, #214, #220, #221,
#227, #231, #232, #233, #234, #237, #238, #240, #242, #244, #247, #248, #252, #254, #255, #257,
#259, #261, #263, #265, #267, #271, #272, #273, #281, #282, #283, #284, #285, #287, #289, #461.

**Deleted plan issues:** the archive `scratchpad/plan-issues/*.json` (#291–#460), titles only.

**Git:**
- `git log origin/main`;
- `origin/main..` for the branches `lift-stage1` (c9b3694), `effect-callbacks`, `loophandle`
  (51772c1), `gfp`, `gfp-arising`, `borrow-callbacks`, `effects-audit`, `effects-calculus-spec`
  and `decision-48-wording`;
- `git grep` for the theorem names cited.

**Repo files** (@ origin/main unless noted):
- `docs/decisions.md` entries 48–61;
- `SPEC.md` section headings §18–§23;
- `Core/EffDefs.lean:20–45`;
- `Core/EffRules.lean:569`;
- `experiments/GhostEnd/README.md` (steps 3b and 3g regions);
- `experiments/Restrat/README.md:90–100`;
- the section headings of `docs/effects-tr/16-regress.md` and `docs/effect-model.md`;
- `docs/effects-audit.md` @ `effects-audit` (grep);
- `docs/effects-calculus/README.md`, `00-structure.md`, `08-correspondence.md`, `03-statics.md`,
  `07-metatheory.md` and `99-open-questions.md` @ `effects-calculus-spec` (grep).

**User memory** (`~/.claude/projects/-Users-johnthompson-repos-borrow-lang/memory/`):
`effects-are-core`, `effect-handling-is-erased`, `no-effect-ish-approximations`,
`hard-stop-on-regress`, `unknowns-first`, `laws-first`, `deep-before-shallow`,
`mechanism-before-syntax`, `structured-recursion-only`, `div-is-an-effect`,
`no-midstream-redirects`, `agents-gate-once`, `current-state-is-not-design`,
`not-now-is-not-never`, `io-is-a-bundle-of-effects`, `errors-are-control-flow-effect`,
`alloc-is-an-effect`, `lead-axis-no-coloring`, `no-function-coloring`, `multishot-only-if-free`,
`structure-before-briefs`, `effect-calculus-spec-first`, `no-issues-for-open-questions`,
`agents-off-issues`, `surface-pipelines`, `total-iteration-from-data`,
`resources-are-of-the-calculus`.

**Not read in full:**
- the Lean bodies of the experiments (only theorem locations were grepped);
- `docs/effects-tr/*.md` beyond headings;
- the full `docs/effects-audit.md` and spec files;
- the 101 KB of research comments on #235 beyond their headings and summaries.
