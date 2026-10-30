# Decisions register for the effect calculus

Part of the effects state-of-play inventory (#290). This file lists every recorded decision that
bears on the effect calculus. For each one it gives the decision, the user's words where they
exist, the strength the user actually used, the scope, and the source. It also flags conflicts
between sources and records that harden the user's wording.

It is an inventory. It does not propose anything, and it does not settle any conflict it flags.

## How to read an entry

Each entry has these fields:

- **Decision**: one line.
- **Words**: the user's exact words and their date, where a record quotes them. A paraphrase is
  marked as one. "No quote" means no source quotes the user.
- **Strength**: one of:
  - **decided**: the user decided it, in words of that strength;
  - **default**: a default, not a prohibition ("not without a good reason");
  - **tentative**: the user called it tentative or open to change;
  - **deferred**: "not now", "later";
  - **provisional (spelling)**: a spelling to be confirmed; per `syntax-choices-not-blocking`,
    spellings are not brought to the user unless they are one-way doors;
  - **superseded by X**;
  - **agent-recorded**: written as a decision by an agent or a design document, with no user
    confirmation found.
- **Scope**: kernel, surface, lowering or process.
- **Source**: file:line at `main` = `8a1c326` (the `effects-state` worktree has the same tree),
  issue or PR comment with its date, or a memory record. "mem:`name`" is
  `~/.claude/projects/-Users-johnthompson-repos-borrow-lang/memory/name.md`.

**Precedence.** Per mem:`current-state-is-not-design` and mem:`defaults-not-prohibitions`, only
entries marked *decided* constrain a design, and even those stay open to the user. How the code
is built today is not a decision. Per mem:`not-now-is-not-never`, any "never", "forbidden",
"excluded" or "out of scope" without a user quote is suspect.

**Author of comments.** Every issue and PR comment on `empath-nirvana/borrow-core` is posted from
the one account `empath-nirvana`. That includes the agents' comments. So a comment counts as the
user's words only where it quotes them, or labels itself "Decision (user)" or "Requirement
(user)". Those labelled comments were written by an agent relaying the user. Where they quote the
user, the quote is given here; otherwise they are paraphrases.

---

## Summary of conflicts and hardenings

These are detailed under each topic below (the IDs in brackets).

1. **Decision 48 still says "Effect rows never enter the core"** (`docs/decisions.md:606-607`).
   - The user: "I never said, btw that row doesn't enter core. You have a habit for turning not
     now into never." (2026-10-02, mem:`not-now-is-not-never`).
   - PR #234, which rewords it, is **open and unmerged** (created 2026-10-02).
   - SPEC §18's motivation still cites decision 48 for the elaboration of answering effects
     (`SPEC.md:2068-2070`). [K1, K2]
2. **"Rows in the core: not needed … Decision 19 forbids a judgment index 'for later'"**
   (`docs/effects-scoping.md:173-176`), and "`CDerives` gains a context of row variables, which
   decision 19 forbids" (`docs/effect-polymorphism.md:280`).
   - Decision 19 (`docs/decisions.md:44-46`) forbids a *defaulted* index that nothing reads ("for
     later").
   - Applying it to row variables or rows is an agent's reading. No user quote extends it there.
     [K2, K9]
3. **Decisions 52 and 53 are not marked superseded** in `docs/decisions.md`.
   - #168 (2026-09-30, "error is a control flow effect full stop") and decision 55 replaced S1b's
     design.
   - The audit says the same (`docs/effects-audit.md:437`, branch `effects-audit`). [E1, E4]
4. **Decision 15, "Shallow handlers are primitive; deep handlers are derived"**
   (`docs/decisions.md:37-38`), was also relayed as a user requirement (#18, 2026-09-27; #52's
   "Decided").
   - SPEC §19's control handler is deep: the driver "reinstalls the deep handler"
     (`SPEC.md:2864`).
   - SPEC §19 *Open* says shallow handlers are "covered by `ν` codata … not a separate construct
     unless a target needs it" (`SPEC.md:2975`).
   - Decision 15 is not marked revised. [C5]
5. **Multi-shot.** Three records state it at three strengths:
   - `docs/effects-scoping.md:100, 287`: "excluded | decision (standing)", "Multi-shot stays
     excluded";
   - mem:`effect-handling-is-erased`: "not erasable; excluded, or an explicit opt-in with a visible
     cost";
   - the user, 2026-10-02: "we also don't need multishot unless we get it for free"
     (mem:`multishot-only-if-free`).

   Meanwhile SPEC §19 has the unrestricted qualifier `multi ctl` built (`SPEC.md:2325`). The
   scoping doc's "excluded (standing)" is a hardening: no user quote says "excluded". [C3]
6. **Runners.**
   - mem:`effects-are-core` says "Runners (Ahman & Bauer) are OUT: the user considers them a dead
     end".
   - #18's comment of 2026-09-30 lists "runners (Ahman & Bauer)" among the candidate calculi.
   - On 2026-10-02 the user called BoLo-as-a-runner "kind of genius", and the memory adds "Don't
     cite 'runners are a dead end' against it".
   - `docs/effects-tr/08-decisions.md:90-96` justifies a decision with Ahman & Bauer's runner
     boundary.

   These are consistent only on the reading "no runners as the user-facing mechanism; the
   internal architecture is open". [K6]
7. **The erasure theorem as acceptance.**
   - mem:`effect-handling-is-erased` and #18 (2026-09-30) set "an erasure theorem" as acceptance.
   - Decision 48 replaced it with laws, counts and reports, because elaboration made it true by
     definition.
   - Once effects are kernel constructs (2026-09-30), that reason no longer holds.
   - No record says whether the erasure theorem is acceptance again. [L1]
8. **Tier 2: halted or not.**
   - The audit (#288, 2026-10-03) says "By #279's hard stop, tier 2 has already halted".
   - The critic's correction carried with the user's sign-off says "Tier 2 did not halt by rule:
     #285 and #287 were continuations the user directed"
     (`docs/effects-calculus/00-structure.md:90-91`, branch `effects-calculus-spec`).
   - Unresolved; it is OQ-2 in the draft spec. [P5]
9. **"Recursion is an effect" survives in older records.**
   - The current position (2026-10-01) is: recursion is the fixed point of a generator; "recursion
     is an effect was more a pretty idea than a hard req."
   - mem:`total-iteration-from-data` still states "recursion is an effect and for is an effect are
     two ways of saying the same thing" (2026-09-30), with fuel drivers setting totality.
   - `docs/rec-effect/README.md:44-70` presents the superseded design as "the design, as decided".
   - The memory record is not marked superseded. [D3, D4]
10. **Div: "an effect" or "not an algebraic effect".** *Corrected by the user, 2026-10-18.*
    - Decision 35 and mem:`div-is-an-effect`: running a loop "is handling the effect", and the
      runtime is "the outermost handler".
    - mem:`no-effect-ish-approximations`: "Div is not an algebraic effect; it stays codata/delay,
      and nobody should pretend it is handled". This sentence was a recorder's, not the user's.
    - The user, 2026-10-18: "The original plan was Div being a handled effect." So the conflict is
      resolved for the first record: div is a handled effect. The second record's sentence is
      drift. [D1]
11. **Traits and providers.**
    - Decision 54 ("Tentative: no traits") lists "invariant-bearing structures … capture their
      provider at construction" and lexical handlers.
    - The user's decision of 2026-10-02 on PR #141 picks option **D**: a provider is a typed
      attribute on the type's declaration, "Traits remain a possible later choice, not ruled out".
    - This later decision is not in `docs/decisions.md`, and PR #141 is open. [N3]
12. **Decision 57's "No row variables in the kernel (Option 2)"** was the user's choice on
    2026-10-01.
    - It came before the 2026-10-02 reset: #233 closed, "laws first", and "whatever we built, it
      isn't an effect algebra".
    - `docs/second-class-and-system-c.md:661` proposes "L1, prompt variables" as the replacement
      for decision 57's apparatus. That is not decided.
    - The draft spec treats Option 2 as the default of OQ-13, not a ban.
    - Whether decision 57 still stands after 2026-10-02 is not recorded. [K9]
13. **`docs/effects-tr/08-decisions.md` reads as decisions, but an agent made them** ("This
    section decides each", line 5). No user confirmation was found. [C6, A5]

---

## 1. Kernel and effects in core

**K1. Effects are core: kernel formers, rules and proofs on a literature-backed foundation.**
- Words: "I want effects to be core to the language, we aren't going to be able to implement them
  correctly with sugar, and we need to build them on a mathematical foundation backed by the
  literature." (2026-09-30)
- Strength: decided. It supersedes decision 48's elaboration premise.
- Scope: kernel.
- Source: mem:`effects-are-core`:11-13; #18 comment 2026-09-30T20:05
  (issuecomment-5918736501); #186 body.
- Note: the S1 elaboration (#164–#166) "stands as a provisional probe" (#18, same comment).

**K2. Decision 48: handlers defined by elaboration; "Effect rows never enter the core".**
- Words: no quote. The user's later correction: "I never said, btw that row doesn't enter core.
  You have a habit for turning not now into never." (2026-10-02)
- Strength: the elaboration premise is **superseded by K1**. "Rows never enter the core" was
  never a user decision; it was the scope of stage S1.
- Scope: kernel.
- Sources:
  - `docs/decisions.md:603-620`, unchanged on `main`;
  - PR #234 (open, 2026-10-02), whose diff adds "Keeping effect rows out of the core was this
    stage's scope, not a standing rule";
  - mem:`not-now-is-not-never`:11-13.
- **Conflict / hardening.** The text on `main` still hardens the user's wording. SPEC §18 cites
  decision 48 (`SPEC.md:2068-2070`). The draft spec lists it as "Hardened text to avoid"
  (`docs/effects-calculus/01-scope.md`, §4, branch `effects-calculus-spec`).

**K3. All or nothing: full user-definable effects, not built-in control constructs.**
- Words: rejecting "capabilities as the only extensible mechanism, plus a fixed set of built-in
  control constructs (exceptions, generators)": "i hate sort of version B, that just ends up with
  us in the 'Exceptions suck and are hard to reason about' territory". Half-implemented
  user-definable effects would be "constant friction". (2026-10-02)
- Strength: decided (a rejection).
- Scope: kernel and surface.
- Source: mem:`effects-are-core`:25-27.
- Note: the memory records "capabilities only, with errors as values (Austral-like)" as
  "discussed as a fallback, not chosen".

**K4. Several effects at once, with nested handlers for different effects.**
- Words: the reconciler chain `timeout |> retry |> log |> kube` must "work, full stop". It is not
  Open and not later. Named instances come from the same mechanism. (2026-09-30)
- Strength: decided.
- Scope: kernel.
- Source: mem:`effects-are-core`:21; #186 comment 2026-09-30T21:33 (issuecomment-5920115600).
  That comment adds "lexical capability labels, per decision 48 and #184/#185, unless there's a
  justified reason for rows plus forwarding" (relayed, not quoted).

**K5. The goal is a full safe effect algebra; kernel-level equations are optional.**
- Words: "I only want to focus on what gets us to a full safe effect algebra." (2026-10-02)
- In scope: unary safety in the kernel for full effects, including stored continuations that hold
  borrows. That means the fundamental property, every-run safety, leak freedom, effect safety and
  T1. Laws are validated on the model (phase B).
- Out of scope unless needed for safety: kernel-level equations, i.e. a binary relation on BoLo's
  carrier, ν/op over moded contexts, η as an equation, and optimiser correctness.
- Strength: decided (scope). The equations are deferred ("optional and don't get pursued unless
  they become necessary for safety"), not refused.
- Scope: kernel.
- Source: mem:`effects-are-core`:37-40.
- **Possible tension.** The 2026-10-03 sign-off (P1) asks for handler laws "stated and proved
  over the KERNEL relation", in the draft spec's paraphrase of it. The draft reads this as: the
  unary half over the kernel is decided, and the binary half is optional
  (`docs/effects-calculus/01-scope.md` §4 U22). The user's own words for the sign-off are only
  those quoted in P1.

**K6. Runners: not the user-facing mechanism. BoLo-world-as-runner: open.**
- Words:
  - "Runners (Ahman & Bauer) are OUT: the user considers them a dead end" (memory paraphrase,
    2026-09-30).
  - 2026-10-02: the framing "a whole BoLo world is one big comodel, a runner, inside a lawful
    local effect calculus" was called "kind of genius… a calculus of everything you can do inside
    of a runner".
  - User concern: "wildly complex to reason about".
- Strength:
  - decided: no runners as the user-facing mechanism;
  - tentative: the architecture is "promising … not yet decided".
- Scope: kernel and model.
- Sources: mem:`effects-are-core`:17, 29-35; #245 comments 2026-10-02T15:02 (issuecomment-5955213071)
  and 15:03 (issuecomment-5955228496). The second sets the criterion "proof cost, not elegance"
  and says "It must not leak into the programming model". That criterion is relayed, not quoted.
- **Conflict.** #18 (2026-09-30T20:05) lists "runners (Ahman & Bauer)" as a candidate calculus.
  The memory written the same day says they are out. `docs/effects-tr/08-decisions.md:90-96`
  uses the runner boundary as a reason for its §8.2 choice. That is consistent only with the
  reading "internal, not user-facing".

**K7. Candidate calculi to choose from before designing.**
- Words: none beyond K1. The memory and #18 list them:
  - Tang–Hillerström–Lindley–Morris (POPL 2024);
  - *Affect* (van Rooij & Krebbers, POPL 2025);
  - Effekt / System Ξ / System C.
- Strength: decided (the method: choose from the literature first). The list itself is an
  agent's.
- Scope: kernel.
- Source: mem:`effects-are-core`:17; #18 comment 2026-09-30T20:05.

**K8. The audit's target structure, signed off.**
- The structure: one `Sig`; handlers as models and capabilities as comodels; kernel handler laws;
  one Kripke world `W`; row-generic borrows. It was signed off with the critic's corrections.
- Words: "Make sure the agents are building the actual effects calculus not an approximation of
  it." "We need a full specification before we start any kernel work, with any open questions
  carefully called out and boxed." (2026-10-03)
- Strength: decided.
- Scope: kernel and process.
- Sources: mem:`effect-calculus-spec-first`:8-19; #290 body (2026-10-03); #288 synthesis comment
  (2026-10-03T03:43).
- Note: the memory says "the critic's seven corrections". The draft spec carries five, numbered
  in its §0.3 (`docs/effects-calculus/00-structure.md:78-99`), and cites "critic 1–6" in
  `99-open-questions.md`. No record found gives seven.

**K9. Decision 57: no row variables in the kernel (Option 2); provided and tunneled rows.**
- Words: no direct quote. Recorded as "the user's decisions, 2026-10-01"; spellings provisional.
- Strength: decided on 2026-10-01. Its standing after K8 and the 2026-10-02 reset is not recorded
  (summary item 12).
- Scope: kernel and surface.
- Sources:
  - `docs/decisions.md:706-714`;
  - `docs/effect-polymorphism.md:832-855`, the user's decisions §11 and an amendment: "rules
    stated over computation types and observations";
  - `docs/second-class-and-system-c.md:661`, which proposes prompt variables as the replacement
    (not decided).
- Sub-items of decision 57, each recorded as decided on 2026-10-01:
  - R3 (site freshness) is checked in the elaborator only;
  - recursion through a site is rejected "for now" (**deferred**);
  - stored callbacks use ports, and "the `dyn` object with a hidden state is deferred";
  - "Operations that take computations (higher-order effects) are out of scope". Recorded as the
    user's decision 6, "out of scope", with no quote. Per mem:`not-now-is-not-never` this should
    be read as "not in this stage" unless a quote says otherwise.
- **Hardening.** `docs/effect-polymorphism.md:280` justifies Option 2 by "decision 19 forbids" a
  row-variable context. See summary item 2.

**K10. Decision 19: no judgment index "for later".**
- Words: no quote. It comes from l_lang lesson L1.
- Strength: decided (process rule). Its text covers defaulted indices that nothing reads.
- Scope: kernel.
- Source: `docs/decisions.md:44-46`; `CLAUDE.md` (*Growth discipline*: "No new index on
  `CDerives`").
- Note: #274 (2026-10-02) cites it against an instance context `Ψ` in `CDerives`. Whether an
  index that every effect rule reads counts as "for later" is not decided anywhere.

**K11. Decision 20: a generalization lands with the deletion of its instances.**
- Strength: decided (process).
- Scope: kernel.
- Source: `docs/decisions.md:47-49`.
- Relevance: the audit's row-generic borrow would turn the six `*U` twins into abbreviations
  (`docs/effects-audit.md`:242, 273, branch `effects-audit`).

**K12. Start from the paper's calculus. Spec first.**
- Strength: decided.
- Scope: kernel and process.
- Source: `docs/decisions.md:5-8` (decisions 1, 2); mem:`borrow-core-spec-first`.

**K13. Few formers.**
- Words: "I want to be quite conservative in making new formers. Every one we add is an ongoing
  proof burden."
- Strength: default (a burden of proof, not a ban).
- Scope: kernel.
- Source: mem:`few-formers`.

**K14. A principled abstraction of which borrowing is one instance.**
- Words: "find a principled, non-ad-hoc abstraction that borrow checking is one example of"
  (paraphrase, 2026-09-26). Test for a reframe: it "unlocks something interesting".
- Strength: decided (goal).
- Scope: kernel.
- Source: mem:`principled-abstraction-goal`.

**K15. One real mechanism: no effect-ish approximations.**
- The mechanism: declared operations, handlers as folds of the free model, and a proved typing
  discipline.
- Words: S1b's special case got "yeah i hate that". Sugar is allowed if it desugars syntactically,
  "the same way that ? desugars in rust to an ordinary return". "the approximation will probably
  come back to bite us". (2026-09-28 / 2026-09-30)
- Strength: decided.
- Scope: kernel and surface.
- Source: mem:`no-effect-ish-approximations`:11-24.
- Note: the same record says "Built-in effects (I/O, alloc) are instances with host-provided
  outermost handlers".

**K16. Sugar never special-cases the kernel.**
- Words: "I don't want sugar to take shortcuts or special case stuff in the kernel".
- Strength: decided.
- Scope: surface and kernel.
- Source: mem:`sugar-never-special-cases-kernel`; decision 33 (`docs/decisions.md:151-157`).
- Note: the record links `[[typed-sugar]]`, which has no memory file. Decision 26 is the
  type-directed-sugar rule (`docs/decisions.md:88-93`; #54 comment 2026-09-27: "no types in the
  sugar" dropped).

**K17. Decision 30: no ambient authority; one capability per effect.**
- Strength: decided. The surface names in decisions 32 and 34 are provisional.
- Scope: kernel and surface.
- Source: `docs/decisions.md:121-130`: "Operations are externs rather than rules, so a capability
  can later be served by a user-defined handler (#18)". "That a function given no capability
  performs no effect is a theorem (`wpTSD_frame_own`)".

**K18. Effects as borrowed capabilities: the 2026-09-25 roadmap experiment.**
- Content: "handlers provide a capability as a borrow; effect safety from borrow soundness;
  divergence/alloc/IO as capabilities; rows are contexts only".
- Strength: superseded by K1 and K8 as the whole design. The experiment itself was done
  (#170, #184, #185).
- Scope: kernel.
- Source: mem:`borrow-core-roadmap`.
- Note: "rows are contexts only" is roadmap wording, not a user quote.

---

## 2. Continuations and multi-shot

**C1. Continuation modes and qualifiers.**
- Content: cancellable by default (`ctl`), plus `linear ctl` (must resume) and `multi ctl`
  (unrestricted). A cancellable continuation's derived drop is its `cancel`.
- Words: the user's spelling guidance of 2026-10-01 (decision 55); no quote on the semantics.
- Strength: provisional (spelling). The qualifier lattice is as built (SPEC §19).
- Scope: kernel.
- Source: `docs/decisions.md:686-688`; `SPEC.md:2309-2366`.
- Open in decision 55: "whether `ctl` is inferred from a clause's `k`, and whether the qualifier
  belongs on the handler".

**C2. Continuations are linear, and abandoned ones are finalised.**
- Words: "continuations are linear, and abandoned ones are finalised", listed among "requirements
  already recorded" (#18, 2026-09-30T15:23, an agent's summary).
- Strength: decided as a requirement (relayed).
- Scope: kernel.
- Source: #18 issuecomment-5914322704.
- **Note.** "Linear" here sits beside a cancellable default (C1, SPEC §19). The kernel reads it as
  the type class: the continuation of `ctl` and of `linear ctl` is linear, and `ctl`'s also has
  a cancel branch.

**C3. Multi-shot only if free.**
- Words: "we also don't need multishot unless we get it for free" and "if we can figure out a way
  it falls out for free sure. Otherwise eh…" (2026-10-02). Also "it's worth pursuing why we can't
  have multishot, but it's not a blocker".
- Strength: default (a priority call, not a ban). Design and prove for must-resume and cancellable; drop
  multi-shot if it breaks a law or adds a rule.
- Scope: kernel and lowering.
- Sources: mem:`multishot-only-if-free`:8-17; #245 comment 2026-10-02T14:48
  (issuecomment-5954971439); #246 body (side question).
- **Conflicts / hardening.**
  - `docs/effects-scoping.md:100`: "resume more than once | not provided … | excluded | decision
    (standing)"; and `:287`: "Multi-shot stays excluded". There is no user quote; this is a
    hardening.
  - mem:`effect-handling-is-erased`:18: "multi-shot → not erasable; excluded, or an explicit
    opt-in with a visible cost". This is an earlier, either/or position.
  - SPEC §19 builds the unrestricted qualifier (`SPEC.md:2325`), and its lowering copies `κ`
    (`SPEC.md` *Lowering*, "An unrestricted `κ` resumed several times"). That is current state,
    not a decision.

**C4. Cancellation is not interceptable (decision C).**
- Words: relayed. During a cancel "handlers inside the cancelled continuation are dead"; a
  finaliser's raise is suppressed; "the canceller always receives 'cancelled'". "Rejected:
  interceptable cancels, i.e. the Java/asyncio 'swallowed cancellation' footgun." (2026-09-30,
  after the machine-checked `prog_stuck`, #191)
- Strength: decided.
- Scope: kernel.
- Sources: #186 comment 2026-09-30T23:00 (issuecomment-5921182937);
  mem:`errors-are-control-flow-effect`:23; `SPEC.md:2493-2530`.
- Open: richer reporting of suppressed errors (K3, #162).

**C5. Decision 15: shallow handlers primitive, deep derived.**
- Words: relayed as "Requirement (user)" in #18 (2026-09-27T13:18): "handlers (a scope lending a
  capability; shallow primitive, deep derived, on the existing codata)". Also #52's body under
  "Decided".
- Strength: decided on 2026-09-27; status since K1 unclear.
- Scope: kernel.
- Source: `docs/decisions.md:37-38`; #18 issuecomment-5856207513; #52 body.
- **Conflict.** SPEC §19's handler is deep (`SPEC.md:2864`), and shallow handlers are "covered by
  `ν` codata … not a separate construct unless a target needs it" (`SPEC.md:2975`). Decision 15
  is not marked revised. Nothing records whether the user revisited it.

**C6. Static destructor placement for a dropped continuation (effects TR §8.1).**
- Content: the elaborator inserts `cancel k` at the weakening point; there is no dynamic
  reachability check.
- Words: none.
- Strength: **agent-recorded** ("This section decides each", `docs/effects-tr/08-decisions.md:5`).
  #245's comment of 2026-10-02 summarises it as "Decisions on phase A's open questions". No user
  confirmation found.
- Scope: kernel.
- Source: `docs/effects-tr/08-decisions.md:11-65`.

**C7. Generative handler names (Ξ's runtime labels) not taken; static names per site.**
- Words: none.
- Strength: agent-recorded as a design choice, with Open status behind T2 (#173). The SPEC says:
  "I have not built this scenario in Lean. It is the reason for the choice, not a claimed
  obstruction".
- Scope: kernel.
- Source: `SPEC.md:2404-2440`.

**C8. Static names and lexical resolution, versus "a control effect goes to whoever runs it".**
- Content: the scoping doc recommends lexical resolution, reading `Async` as codata.
- Strength: agent-recorded recommendation. Its §7.6 says it "should be checked on the operator's
  `timeout` example in S5".
- Scope: kernel and surface.
- Source: `docs/effects-scoping.md` §7.6.

**C9. A relevant continuation qualifier.**
- Strength: Open in SPEC ("stays Open until a target needs it"). No user statement.
- Scope: kernel.
- Source: `SPEC.md:2356-2366`.

**C10. A continuation's contraction is its capture's persistence (`lam_bang_persistent`).**
- This is a proved result (#184/#185), not a decision. It is listed because C3's "only if free"
  is judged against it.
- Source: #186 body; `SPEC.md:2284`.

---

## 3. Divergence, recursion, totality

**D1. Divergence is an effect.**
- Words: "'only main may run forever'. That is very much not what I intended. Div should be an
  effect." (2026-09-28)
- Strength: decided. The markers `total def` / `div def` are provisional (decision 36).
- Scope: kernel and surface.
- Sources: mem:`div-is-an-effect`:11-15; decision 35 (`docs/decisions.md:174-184`);
  `SPEC.md:1190-1200`; #81 (closed).
- **Tension, corrected (2026-10-18).** mem:`no-effect-ish-approximations`:16 said "Div is not an
  algebraic effect; it stays codata/delay, and nobody should pretend it is handled". That was a
  recorder's sentence. The user: "The original plan was Div being a handled effect." Decision 35's
  "running a loop is handling the effect" and the runtime as "the outermost handler" are the plan.
  SPEC §19's "no second fixed point" and `Loop_Σ` as the only reading of div are the state as
  built, not a decision; `docs/pipeline-architecture.md` (#552) designs div as a handled effect.

**D2. Totality is not a goal.**
- Words: "i don't really care about totality in general unless we need it for something specific,
  it's really just an artifact of the borrow calculus that we can do it at all." (2026-10-01)
- Strength: default (keep the existing theorems; don't spend design effort on totality).
- Scope: kernel and surface.
- Source: mem:`div-is-an-effect`:17; decision 24 (`docs/decisions.md:75-76`: "Totality is not a
  goal of recursion").

**D3. Recursion is the fixed point of a generator, called directly.**
- Content: Cook–Palsberg; Bekič for mutual groups. Layers transform the generator. The drivers
  are `bounded` (default, `Exhausted`) and `deep`.
- Words: "recursion is an effect was more a pretty idea than a hard req." (2026-10-01)
- Strength: decided (current). The spellings are provisional.
- Scope: kernel, surface and lowering.
- Sources: mem:`structured-recursion-only`:8-25; decisions 24, 58, 59
  (`docs/decisions.md:65-79, 715-772`); SPEC §20–§21.
- History, each superseded:
  1. 2026-09-27, "no general direct recursion; users are expected to know map/fold" (#48 comment
     2026-09-27T13:03, "Surface decision (user)");
  2. 2026-09-27, "structured recursion only";
  3. 2026-09-30, "recursion is an effect" (`rec` performed, `fix` drives, layers intercept);
  4. 2026-10-01, the current position.
- **Stale records.**
  - `docs/rec-effect/README.md:44-70` says "These points were given by the user" for the
    superseded `rec`/`fix` design. Decision 24's text marks the revision; the README does not.
  - `docs/effects-scoping.md` §7.7 quotes decision 24's first text ("There is no general direct
    recursion on the surface").
- Kept from the user's original intent: "memo should layer on recursion, not drive it".

**D4. Loops and recursion are one mechanism; the driver sets totality.**
- Words: "recursion is an effect and for is an effect are two ways of saying the same thing"
  (2026-09-30).
- Strength: superseded in part by D3 (2026-10-01) and D2. Fuel drivers are not prioritised.
- Scope: surface.
- Source: mem:`total-iteration-from-data`:19.
- **Conflict.** That memory record is not marked superseded.

**D5. Total iteration comes from data; codata is div unless fuelled; finiteness is never
inferred from names.**
- Words: the user endorsed the transducer version as "the mathematically correct one"
  (2026-09-30). Direction: "i don't think we can or should" abstract over push and pull. On
  `for`: "really the purpose of for is to let people write 'normal' code". `for` follows Rust's
  desugaring "unless we have a clever way to make it more general". The user expects to be
  "clever with effects and how we handle early exit" (open).
- Strength:
  - decided: totality from data, never from names; direction is real;
  - default: Rust's pull desugaring.
- Scope: surface.
- Sources: mem:`total-iteration-from-data`:11-23; decision 47 (`docs/decisions.md:555-603`).
- Note: decision 47 also says exits live in the step's result, "not in handlers". Later, decision
  56 made `for` over a generator a handler site. Decision 47 governs counted loops over data.

**D6. Iteration is `Yield`, with no iterator trait; the old generator system goes.**
- Words: recorded as "the user's binding decisions of 2026-10-01 — effects are core, iteration is
  `Yield` with no iterator trait, the old generator system goes". Spellings provisional.
- Strength: decided. It revises decisions 41 and 42.
- Scope: surface and kernel.
- Source: decision 56 (`docs/decisions.md:696-705`); decision 54 (`:676-677`).

**D7. Decision 7: recursion without step-indexing.**
- Content: least fixed points for data, greatest with a mandatory `close` for codata,
  divergence in the type.
- Strength: decided.
- Scope: kernel.
- Source: `docs/decisions.md:19-21`.
- Note: SPEC §19's `ewpTS` is a least fixed point, and an infinite effectful loop is `Loop_Σ`
  codata, "no second fixed point" (`SPEC.md:2709-2712`).

**D8. A totality-guaranteed `bounded_fix` (total correctness).**
- Content: partial correctness was considered and not taken.
- Strength: decided on 2026-10-01 as part of decision 58.
- Scope: kernel.
- Source: `docs/decisions.md:731-733`.
- Note: the draft spec's OQ-63 (a partial-correctness `wp`) reopens this as a question.

---

## 4. Errors

**E1. Errors are a control-flow effect, full stop.**
- Words: "error is a control flow effect full stop", after "i feel like we're trying to build both
  rust's error model and an exception error handling model and I don't want to do that."
  (2026-09-30)
- Content:
  - failing operations raise;
  - no API returns a sum for failure;
  - no `?` and no `try`/`catch`/`map_err` keywords;
  - handling is `with` plus library handlers;
  - absence stays an option;
  - nothing error-specific in the elaborator.
- Strength: decided. It supersedes decision 52.
- Scope: kernel, surface and lowering.
- Sources: mem:`errors-are-control-flow-effect`:8-19; #168 body and comment 2026-09-30.
- **Conflict.** Decision 52 (`docs/decisions.md:649-665`) is not marked superseded. It still
  lists `try`/`catch`/`map_err` spellings and "`Fail` is a computation type, not a capability".
  Decision 55 (`:692`) restates errors as `Fail[E]` in `lib/fail.bc`, which is consistent with E1.

**E2. Kernel shape: an abortive operation (unwind mode), as a general handler class.**
- Words: "endorsed by the user, 2026-09-30, #186/#187" (paraphrase). "When the kernel agent
  proposed keeping `Fail` as a sum, it was corrected."
- Strength: decided.
- Scope: kernel.
- Source: mem:`errors-are-control-flow-effect`:21; `SPEC.md:2335-2350`.
- Note: unwinding crosses borrow scopes without T1.

**E3. Sugar for errors is allowed if it is purely syntactic.**
- Words: "the same way that ? desugars in rust to an ordinary return".
- Strength: default. E1 says "no `?`". The two are reconciled by "sugar later, syntactic only"
  (K15, N4).
- Scope: surface.
- Source: mem:`no-effect-ish-approximations`:20.

**E4. Decision 53: acceptance of #18 by per-class laws on the elaborated terms.**
- Strength: superseded in effect. The audit says its laws cover the withdrawn sum schema
  (`docs/effects-audit.md:436-438`, branch `effects-audit`). SPEC §18 *Laws* says the abort laws
  "are about the sum schema that errors elaborated to before §19" (`SPEC.md:2206-2208`).
- Scope: kernel and process.
- Source: `docs/decisions.md:666-674`.
- **Conflict.** Not marked superseded.

**E5. Errors carrying owned values.**
- Content: "An error holds nothing owned … provisionally: the error should hand the buffer back
  once an abortive payload may be linear".
- Strength: deferred (#215).
- Scope: kernel.
- Source: decision 55 (`docs/decisions.md:692`); `SPEC.md` §18 *Open*.

**E6. Early exit and file handles.**
- Content: "Leaning: 3 [a scoped provider] as the idiom, 1 [an infallible destructor] as the
  default destructor."
- Strength: agent-recorded leaning, "Not settled".
- Scope: surface.
- Source: #18 comment 2026-09-28T22:19 (issuecomment-5879782777).

**E7. Panics and backtraces on the unwind mechanism.**
- Strength: open (#192). No decision recorded.
- Scope: kernel and lowering.

---

## 5. Allocation and I/O

**A1. Allocation is an effect.**
- Content: `box` is the operation, the heap is the outermost linear State handler, and arenas are
  nested handlers.
- Words: "alloc _is_ an effect, we already talked about that" (2026-09-28).
- Strength: decided. Tracking it in function types is unbuilt.
- Scope: kernel and surface.
- Sources: mem:`alloc-is-an-effect`:11-15; #54 comment 2026-09-28 ("heap allocation is explicit,
  as in Rust, spelled `box`"); #18 comment 2026-09-27T17:28 (design thread, agent-written).

**A2. I/O is a bundle of per-effect linear capabilities; no ambient authority outside `main`.**
- Words: bundles and platform packages are "quite pretty" (2026-09-30).
- Strength: decided (the shape). Platform design is on the `platform-design` branch and PR #140,
  open.
- Scope: surface and kernel.
- Sources: mem:`io-is-a-bundle-of-effects`:11-22; decision 30.
- Note: the audit (#235's survey) found "I/O is a lent capability but not an effect: there is no
  row and no user handler" (#235 comment 2026-10-02). That is current state.

**A3. No WASI async.**
- Words: "don't use WASI 0.3's component-model async even if available. Async is ours"
  (2026-09-30).
- Strength: decided.
- Scope: lowering and platform.
- Source: mem:`io-is-a-bundle-of-effects`:24.

**A4. Unsafe operations as an effect (`RawMem`), with handlers as assurance levels.**
- Words: "a handler story for unsafe effects" (2026-09-27).
- Strength: agent-recorded design thread. The user rejected mandatory assurance clauses
  (mem:`trust-not-assurance-ceremony`): "leaking Lean details is not ideal".
- Scope: kernel and surface.
- Source: #18 comment 2026-09-27T15:27 (issuecomment-5857189510); #7 comments 2026-09-27.

**A5. Fallible co-operations fail to the lend, only at weakenable operations (effects TR §8.2).**
- Strength: **agent-recorded**; no user confirmation found.
- Scope: kernel.
- Source: `docs/effects-tr/08-decisions.md:67-122`.

**A6. No GC and no implicit RC; explicit `Rc`/`Arc`/`Mutex` not excluded.**
- Words: "I'm not sure I want to leave no rc/arc/mutex etc as a design goal rather than something
  we're just not prioritizing." (2026-09-30)
- Strength:
  - decided: no GC, no implicit RC;
  - deferred: explicit RC and synchronisation types.
- Scope: lowering and library.
- Source: mem:`no-gc`.

**A7. Interior mutability: open.**
- Words: the user is "ambivalent"; it is "not a settled 'no'" (2026-09-28).
- Strength: tentative (absent today; the reversible path is an opaque-handle library type).
- Scope: kernel and library.
- Sources: mem:`no-interior-mutability`; #119 (interior mutability as an effect, open).
- Note: the record says to flag designs that quietly assume it, e.g. #52's waker "ready flag".

---

## 6. Lowering and runtime

**L1. Effect handling is erased: cost parity with the hand-written program.**
- Words: "Part of 18 needs to be effect handling is erased." (2026-09-30) The refinement,
  relayed: "erased" does not mean "always a direct call". The criterion is cost parity. A handler
  never adds cost of its own.
- Strength: decided (requirement).
- Scope: lowering.
- Sources: mem:`effect-handling-is-erased`:11-26; #18 comments 2026-09-30T12:49 and 12:50.
- **Conflict.** The memory sets the acceptance as "an erasure theorem, plus corpus counts".
  Decision 48 replaced it with laws, counts and reports, because elaboration made erasure true by
  definition. K1 removed that premise. No record says whether an erasure theorem is acceptance
  again. The draft spec carries this as OQ-23.

**L2. Every lowering has a plain LLVM counterpart; handlers lower to stackless state machines.**
- Words: "not want to rely on Wasm features that cannot be replicated in LLVM later" (paraphrase,
  2026-09-27).
- Strength: decided.
- Scope: lowering.
- Sources: decision 25 (`docs/decisions.md:80-87`); mem:`portable-lowerings`; #18 comment
  2026-09-27T13:12.

**L3. Zero-cost target.**
- Content: allocate and indirect only where C or Rust would, measured by corpus counts.
- Strength: decided (goal).
- Scope: lowering.
- Source: mem:`zero-cost-target`.

**L4. The returning/suspending split is polarity.**
- Content: the lowering is decided by shift cancellation, read off the handler's type, with no
  operation-kind annotation.
- Words: relayed as "Refinement (user)" (2026-09-27).
- Strength: decided on 2026-09-27. Today the operation declares `fn` or `ctl` (decision 55). That
  is a declared kind, which the 2026-09-27 refinement said was not needed. Not reconciled in any
  record.
- Scope: lowering and kernel.
- Sources: #18 comment 2026-09-27T13:19 (issuecomment-5856217516); mem:`no-function-coloring`:13.

**L5. Decision 49: no `perform`/`suspend` token.**
- Content: visibility comes from the inferred row, the reports, and the explicit `k` in the
  handler.
- Words: recorded among "the user's decisions" of #151. The scoping doc said "This needs the
  user's confirmation, since it edits a rule" (`docs/effects-scoping.md:1245`).
- Strength: decided (2026-09-30).
- Scope: surface.
- Source: `docs/decisions.md:620-624`; mem:`effect-handling-is-erased`:24.

**L6. Compiler never stale.**
- Content: every feature lands with its lowering and a running corpus program (decision 17).
- Strength: decided (process).
- Scope: lowering and process.
- Sources: mem:`compiler-never-stale`; `docs/decisions.md:40-41`.

**L7. LLVM after #188; system `malloc`/`free`.**
- Words: "unless jemalloc turns out to make more sense for a specific reason" (2026-10-01).
- Strength: decided (ordering) and default (allocator).
- Scope: lowering.
- Source: mem:`borrow-core-roadmap`.

---

## 7. Colouring

**F1. No function colouring is the lead axis.**
- Content: async, errors, generators and other control effects as one mechanism.
- Words: the user chose it "over 'authority/capabilities' and 'machine-checked proof' as the
  lead" (2026-09-28, paraphrase). Method: design down from the programming experience.
- Strength: decided (priority).
- Scope: surface and kernel.
- Source: mem:`lead-axis-no-coloring`:11-17.

**F2. No coloured functions: async and sync, fallible, const, unsafe.**
- Words: a "core goal" (2026-09-27, paraphrase). Extension, relayed as "Requirement (user)": async
  and every other effect are user-definable and live in the std lib, with no privileged built-ins.
- Strength: decided (goal).
- Scope: surface and kernel.
- Sources: mem:`no-function-coloring`:8-13; #18 comments 2026-09-27T13:15 and 13:18.
- Note: "Stackful coroutines are ruled out by the portability decision" (#18, 13:15). That
  follows from L2, not from a separate user statement.

**F3. Higher-order code is served by specialisation at the callback's computation type.**
- Content: no kernel polymorphism over computation types.
- Strength: decided as decision 35's mechanism, on 2026-09-28.
- Scope: surface and kernel.
- Source: `docs/decisions.md:181-184`; #18 comment 2026-09-28T01:31.
- Note: decision 57 (K9) refines this into provided and tunneled rows with copies.

---

## 8. Concurrency

**T1. Threads are required eventually.**
- Words: "we obviously need them", just not now (2026-09-29).
- Strength: deferred (required later). Never call them out of scope; avoid choices that close the
  door.
- Scope: kernel, lowering and process.
- Source: mem:`threads-are-required`.
- Note: the draft spec's OQ-18 (sum versus tensor, threads) records thread implications.

**T2. Async is a library effect with a scheduler written as a handler over state machines.**
- Words: relayed as "Requirement (user)" (2026-09-27). "Goal (user): enough to support a
  tokio-like async scheduler — without GC/RC reliance and without Wasm-only features" (#52 body).
- Strength: decided (goal).
- Scope: library and lowering.
- Sources: #18 comment 2026-09-27T13:18; #52 body; mem:`io-is-a-bundle-of-effects`:24.

**T3. Scoped tasks that borrow from the spawning scope are sound.**
- Strength: listed under "Decided" in #52's body. Its wording is an agent's.
- Scope: kernel.
- Source: #52 body.

**T4. T1 (no lend spans a suspension) is kept at tier 1.**
- Content: self-referential suspension is tier 2, behind the hard stop.
- Strength: see P5.
- Scope: kernel.
- Source: mem:`hard-stop-on-regress`:10-22.

---

## 9. Naming and syntax

**N1. Our names, not Rust's.**
- Words: "As an aside i don't like using the rust names for these things." (2026-10-02)
- Strength: default (preference). Rust names appear only as comparisons.
- Scope: surface and docs.
- Sources: mem:`own-names-not-rust`:8-17; decision 60 (`Clo`); PR #141 comment 2026-10-02.

**N2. Syntax choices are not blocking.**
- Words: "honestly I don't care that much about syntax right now unless we're forced to keep
  something for some reason" (2026-09-29).
- Strength: decided (process). Spellings are provisional unless they are one-way doors.
- Scope: surface and process.
- Source: mem:`syntax-choices-not-blocking`.
- Applies to: decisions 51, 52, 55–61 (all "spellings provisional").

**N3. Tentative: no traits.**
- Words: "I just think we just don't need anything like traits at all … Let's just go with it as a
  decision and see where/if it breaks when we get there." (2026-09-30) "Just record it as
  tentative/open to change later." Traits are "very much up in the air" (2026-10-01).
- Firm dislike: "The chain of nested traits in iter pipelines is a wart i would not like to carry
  forwards." (2026-10-01)
- Strength:
  - tentative (no traits);
  - decided (a pipeline's type stays flat).
- Scope: surface.
- Sources: mem:`no-traits`:8-26; decision 54 (`docs/decisions.md:675-684`); PR #169 comment
  2026-09-30.
- **Later decision not in `docs/decisions.md`.** PR #141 comment 2026-10-02T06:06
  (issuecomment-5946502626), "Decisions (user, 2026-10-02)":
  - providers are option **D**, a typed attribute on the type's own declaration, one per type,
    with no orphan rule;
  - "Traits remain a possible later choice, not ruled out";
  - loops inside recursion and the other recursion/effect seams "are not patched one by one. They
    come from lifting the effect model … into the kernel after phase B".

  PR #141 is open. Decision 54's "lexical handlers for scoped choices" and "data carries its
  provider" are not reconciled with option D in any record.
- Operators perform a `Num[T]` effect with an ambient machine-operation handler. This is part of
  the tentative decision 54. No later record restates it.

**N4. Mechanism before syntax.**
- Words: "i don't want to do any sugar right now because i feel like starting with surface syntax
  caused the agent to think the syntax was what we wanted." (2026-09-30)
- Strength: decided (process; "right now", so sugar is deferred, not refused).
- Scope: process and surface.
- Source: mem:`mechanism-before-syntax`:8-14.

**N5. No surface monads.**
- Words: "ample evidence that nobody understands them". Strength qualified on 2026-10-01: "don't
  want without a good reason".
- Strength: default.
- Scope: surface.
- Sources: mem:`no-surface-monads`; decision 16 (`docs/decisions.md:39`).

**N6. `|>` pipes first and suspends its left side at a computation parameter.**
- Content: one-way door.
- Words: the operator shape `watch(kube) |> filter(..) |> each(e -> reconcile(e) |> retry(3) |>
  timeout(30s))` (2026-10-01). The reading "`|>` applies the handler on the right" is the
  assistant's, marked provisional.
- Strength: decided (decision 50, one-way door).
- Scope: surface.
- Sources: `docs/decisions.md:625-628`; mem:`surface-pipelines`.

**N7. No magic comments.**
- Words: "One thing i don't want is magic comments." (2026-09-30)
- Strength: decided.
- Scope: surface.
- Source: mem:`no-magic-comments`.
- Relevance: PR #141's option D providers are typed attributes, not comments.

**N8. Effect spellings.**
- Content: `effect`/`handler`/`with`/`fn`/`ctl`/`linear ctl`/`multi ctl`, `raise`, `Yield`,
  `Exhausted`, `with deep`, `with L`, `k(v)`.
- Strength: provisional (spelling), "to be settled after rewriting a sample of the corpus".
- Scope: surface.
- Source: decisions 51, 55, 56, 58, 59 (`docs/decisions.md:629-772`).

**N9. Decision 48's syntax.**
- Content: Effekt's semantics with a `with` clause; capabilities implicit and lexical; Koka's cost
  vocabulary.
- Strength: provisional ("Syntax (provisional)").
- Scope: surface.
- Source: `docs/decisions.md:617-619`.

---

## 10. Process

**P1. Effect calculus spec first.**
- Content: a full spec with boxed open questions before any kernel effect work. Every brief names
  the spec ids it implements.
- Words: see K8. Also: "we need a starting brief that every agent shares in their context so they
  aren't starting from zero when we launch a new workflow." "we aren't starting from _zero_ on
  effects, we got a lot working before we kind of hit the limits of our first approach."
  (2026-10-03)
- Strength: decided.
- Scope: process.
- Sources: mem:`effect-calculus-spec-first`:8-24; #290 body.
- Note: the draft spec (`effects-calculus-spec`, PR #461) **failed validation**. #290 lists the
  consolidation steps.

**P2. Laws first.**
- Words: "I think we basically need to find the laws that we have to implement instead of trying
  to wing it." (2026-10-02) Also "whatever we built, it isn't an effect algebra or we wouldn't be
  having these problems" (paraphrase in the record).
- Strength: decided (standing instruction).
- Scope: process and kernel.
- Source: mem:`laws-first`:11-31.

**P3. Deep before shallow.**
- Words: "I just don't want to get in the trap of implementing shallow solutions and thinking we
  can patch them later when a deep solution might be a fundamentally different thing."
  (2026-10-01) The criterion: "what i want is a bunch of things falling like magic not something
  that half implements what we were looking for with no obvious way of progressing."
- Strength: decided (standing instruction).
- Scope: process.
- Source: mem:`deep-before-shallow`:11-32.

**P4. Unknowns first.**
- Words: "I'd like to focus on the hard/unknown parts first if we can, rather than time
  consuming/mechanical parts." (2026-10-02)
- Strength: decided ("if we can").
- Scope: process.
- Source: mem:`unknowns-first`:8-17.

**P5. Hard stop on regress (tier 2).**
- Words: "My concern is going to be that one of that finite lists itself has a regress so we
  should make that a hard stop." Refinement: "If the new work is n+1 and we are done, it's fine.
  If it's 3 and then 4 and then 5, no." (2026-10-02)
- Strength: decided (standing rule). The tier-2 list is frozen. If an item spawns a new unknown,
  tier 2 halts and the language ships at tier 1.
- Scope: process and kernel.
- Sources: mem:`hard-stop-on-regress`:8-28; #279 comment 2026-10-02.
- Related: the user's #269 remark, "it feels like we're endlessly going down further and further
  orders… 'everything is reduced to one lemma' and then that lemma is reduced to one lemma…"; and
  #286's "It doesn't feel like a design choice; it feels like there is a right answer."
  (2026-10-03, on the borrow-callback reading).
- **Conflict.** #288 (2026-10-03) says tier 2 halted by the rule. The critic's correction carried
  with the user's sign-off says it did not, because #285 and #287 were user-directed
  (`docs/effects-calculus/00-structure.md:90-91`, branch `effects-calculus-spec`). OQ-2 and OQ-33
  in the draft spec are open.

**P6. Structure before briefs.**
- Words: "A lot of what its recommendations are are what i thought i asked for to begin with and
  i am confused why it wasn't done that way." (2026-10-03) On plans: "needed to go through a
  validation and consolidation stage before any issues were opened."
- Strength: decided (process). A new relation family, twin constant or side mechanism is a
  stop-and-report.
- Scope: process.
- Source: mem:`structure-before-briefs`:11-25.

**P7. No issues for open questions; no issue creation until the plan is agreed.**
- Words: "don't open issues for open questions at all"; "Don't script or allow the creation of
  any issues until we have a plan/spec written out and agreed on."; "I think maybe we don't go
  down too far in granularity on the first pass." (2026-10-03)
- Strength: decided.
- Scope: process.
- Sources: mem:`no-issues-for-open-questions`:8-19; #290 body. Issues #291–#460 were deleted.

**P8. Agents run off issues (for agreed work).**
- Words: "Make sure we're running these off of GH issues." (2026-10-02)
- Strength: decided. It applies to agreed work, and #290 can be the single tracker.
- Scope: process.
- Source: mem:`agents-off-issues`.

**P9. No midstream redirects.**
- Words: "No we get bad results by changing them midstream." (2026-10-02)
- Strength: decided.
- Scope: process.
- Source: mem:`no-midstream-redirects`.

**P10. Current state is not design.**
- Words: "just because we have done something a certain way, that does not mean it was the result
  of a careful design decision, or that it is locked in." (2026-09-30)
- Strength: decided (standing instruction).
- Scope: process.
- Source: mem:`current-state-is-not-design`:11-18.
- Note: its example was the absence of delimited control and multi-shot. It names "adding
  delimited control or multi-shot to the core" as a live option.

**P11. Defaults, not prohibitions; not now is not never.**
- Words: "a lot of the things you said i don't want are 'don't want without a good reason for
  them'. In particular traits are very much up in the air." (2026-10-01) "I never said, btw that
  row doesn't enter core. You have a habit for turning not now into never." (2026-10-02)
- Strength: decided (standing instruction).
- Scope: process.
- Sources: mem:`defaults-not-prohibitions`; mem:`not-now-is-not-never`.

**P12. Spitballing is not deciding.**
- Words: "I am just spitballing here, you don't need to commit every idea to memory"; "stop taking
  every idea I have and making it a general principle".
- Strength: decided (process).
- Scope: process.
- Source: mem:`spitballing-is-not-deciding`.
- Relevance: K6's architecture and the #245 framing are explorations, not decisions.

**P13. Design, not accretion.**
- Words: "I don't want to get into a pattern I got into last time where I accreted a language
  instead of designing one."
- Strength: decided.
- Scope: process.
- Sources: mem:`design-not-accretion`; mem:`rows-conflated-three-things` (l_lang's rows carried
  data, codata and context; keep them distinct).

**P14. Ordering.**
- Content: #18 after the string work; LLVM (#21) after #188.
- Words: #18 comes next "because it changes so much about syntax and coding patterns"
  (2026-09-30).
- Strength: decided (ordering), now overtaken by P1's spec-first gate for the effect kernel.
- Scope: process.
- Sources: mem:`borrow-core-roadmap`; #18 comment 2026-09-30T15:23.

**P15. North star: a Kubernetes operator.**
- Content: the reconciler chain and controller loop are effect targets.
- Strength: decided (goal).
- Scope: process.
- Sources: mem:`north-star-k8s-operator`; #18 comment 2026-09-30T15:23 (target examples 1–7).

**P16. Agents run the gate once.**
- Strength: decided (process). It is not relevant to design. Listed because it binds every
  implementation brief.
- Source: mem:`agents-gate-once`.

**P17. Paper discipline.**
- Content: the paper is not wrong; §6 quantifies over resources that arise; blockers must be
  machine-checked.
- Strength: decided ("SETTLED") standing rules.
- Scope: process and kernel.
- Sources: `~/repos/borrow_lang/CLAUDE.md`; mem:`the-paper-is-not-wrong`,
  mem:`resources-are-of-the-calculus`, mem:`blockers-must-be-machine-checked`.

---

## 11. Records that hold no effect decision

- **`docs/adjudications.md`** (1459 lines) holds readings of [CONF]/[TR] and conventions of the
  mechanisation. It has **no entry about effects, handlers or continuations**. Entries that
  constrain the world any effect relation must extend:
  - §12.72, "`⊸`/`∀` Kripke over the record list, and `wp` over tagged typed worlds"
    (`docs/adjudications.md:1111`);
  - §12.73, "Why the judgment tracks history" (`:1143`);
  - §C.25, outlives is universal over borrow cells, and `[⊤]P` is the borrow-free restriction
    (`:1166`). That reading is confirmed with Wagner (mem:`wagner-confirms-outlives-semantics`).

  These are readings of the paper, not design decisions.
- **SPEC.md** records mechanisms and their Open items, not user decisions. It quotes no user. Its
  design choices are agent-recorded unless a decision entry backs them: static names (C7),
  deep handlers (C5), and the relevant qualifier left Open (C9).
- **`docs/effects-tr/08-decisions.md`**: agent-made decisions (C6, A5).
- **Draft spec, `docs/effects-calculus/01-scope.md` §4** (branch `effects-calculus-spec`): a
  register of the user's decisions, U1–U24. It agrees with this file where they overlap. The
  draft failed validation, so it is listed here as a cross-check only.

---

## Sources read

**Repo** (`~/repos/borrow-core-effects-state` and `~/repos/borrow-core`, both at `8a1c326`):
- `docs/decisions.md` (all 61 entries);
- `docs/adjudications.md` (index and the §12.72, §12.73, §C.25 entries);
- `SPEC.md` §14 motivation, §18 and §19 (motivation, kinds, names, cancels, divergence, lowering,
  Open), §20 header;
- `docs/effects-tr/08-decisions.md`;
- `docs/effect-polymorphism.md` §5 Option 1 and §11;
- `docs/effects-scoping.md` (header, §1, §7, §8);
- `docs/rec-effect/README.md` §1;
- `docs/effect-model.md` and `docs/second-class-and-system-c.md` (grep for decisions);
- `CLAUDE.md` (*Growth discipline*).

**Branches:**
- `origin/effects-audit`: `docs/effects-audit.md` (grep for decisions and corrections);
- `effects-calculus-spec` (`~/repos/borrow-core-effects-spec`, `8296ab0`):
  `docs/effects-calculus/00-structure.md` §0.3 and §1, `01-scope.md` §4, and
  `99-open-questions.md` (table).

**GitHub:**
- Bodies and comments of issues #1–#290 that still exist, with the effect-related ones read in
  full: #18, #48, #52, #168, #186, #245, #246, #269, #286, #288, #290.
- PRs #133, #140, #141, #169, #233, #234 (with diff), #289 and #461 (bodies and comments).
- The deleted plan issues #291–#460 were not consulted.

**Memory** (`~/.claude/projects/-Users-johnthompson-repos-borrow-lang/memory/`), all
language-design records:
- effects-are-core, effect-handling-is-erased, no-function-coloring, lead-axis-no-coloring;
- div-is-an-effect, errors-are-control-flow-effect, multishot-only-if-free, laws-first;
- deep-before-shallow, no-effect-ish-approximations, threads-are-required, alloc-is-an-effect;
- io-is-a-bundle-of-effects, structured-recursion-only, total-iteration-from-data, no-traits;
- no-interior-mutability, hard-stop-on-regress, unknowns-first, own-names-not-rust;
- no-surface-monads, mechanism-before-syntax, sugar-never-special-cases-kernel;
- current-state-is-not-design, defaults-not-prohibitions, not-now-is-not-never;
- effect-calculus-spec-first, structure-before-briefs, no-issues-for-open-questions;
- zero-cost-target, portable-lowerings, no-gc, compiler-never-stale, trust-not-assurance-ceremony;
- surface-pipelines, syntax-choices-not-blocking, spitballing-is-not-deciding, few-formers;
- language-purpose, design-not-accretion, principled-abstraction-goal, granule-influence;
- rows-conflated-three-things, borrow-core-spec-first, borrow-core-roadmap, no-magic-comments;
- north-star-k8s-operator, paper-mu-tabled, resources-are-of-the-calculus, agents-off-issues;
- no-midstream-redirects, agents-gate-once;
- and the MEMORY.md index.

The paper-mechanisation records (BoCa and ledger) were read only in the index; they hold no
effect decision.
