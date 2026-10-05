# The draft spec's open questions OQ-35 to OQ-68, against what we already have

This file checks each boxed open question OQ-35 to OQ-68 of the draft effect-calculus
specification against the user's recorded decisions, the existing Lean, and earlier documents.
OQ-68 is the highest-numbered question. The draft failed validation (#290, PR #461), so its
questions are treated as questions, not as findings.

It is an inventory. It records what settles, constrains or bears on each question. It does not
choose options.

## How to read this file

**Versions.**

- The questions are quoted from `docs/effects-calculus/99-open-questions.md` @
  `effects-calculus-spec` 8296ab0 (worktree `~/repos/borrow-core-effects-spec`), §2, lines
  453-792.
- Code citations are @ `main` 8a1c326 unless a branch is named. The spec's own code citations for
  these questions were spot-checked against `main` 8a1c326. Every one checked matched:
  `effHandle`, `Row.Unwind`, `OpSig.ent`, `RowLe`, `EffLeaf`, `cC_effOf`, `CTy.effOf`, `kTy`,
  `clauseTy`, `retTy`, `contShare`, `wpTSD`, `ewp_mono`, `opTable_mono`, `head_det_eff`,
  `fundamentalC`, `reclaim`, `adequacyD_obs`, `masks`, `head_rename`, `run_sim`, `freshRun_det`,
  `LinResume`, `ptoMutS`, `ptoImmS`, and on `borrow-callbacks` `guardS`, `below_excluded`,
  `not_gfpAt_below`, `vRLk`, `cRLk`, `callback_ext`, `callback_ext_one`.
- `Core/` is sorry-free. The only match for `sorry` is in `Core/README.md`.

**Worlds.** A result is said to hold at one of these:

- **σ = []**: Core's kernel relation (`vC`/`cC`/`ewpTS`, `fundamentalC`). This is not the planned
  Kripke world `W = (ρ, ls, σ)`.
- **GhostEnd**: the stacked relations `vRLs`/`vRLa`/`vRLk` of `experiments/GhostEnd`. These are
  candidates for `W`, not `W` itself.
- **BoCa**: the paper's carrier in `~/repos/borrow_lang`, or its transcription in borrow-core's
  `Paper/`.
- **sibling**: `EffModel` and `EffModelRel`, which are separate calculi.

**Classes.**

- **DECIDED**: a user decision settles the question.
- **CONSTRAINED**: decisions rule options in or out.
- **EVIDENCED**: proved or refuted Lean results, or recorded findings, bear on it.
- **ANSWERED-ELSEWHERE**: an earlier document or issue already settled it.
- **DUPLICATE**: the same question as another OQ.
- **MOOT**: it depends on an option nobody chose, or on a construct that is not needed.
- **MIS-POSED**: it rests on a misreading of BoLo or of our code.
- **GENUINELY OPEN**: none of the above settles it.

A question can carry two classes. The first is the one that governs.

## The decisions these questions run into

The same handful of records recurs below. Each is quoted once here, with its date and the
strength actually used.

| key | source | words | strength |
|---|---|---|---|
| **D7** | `docs/decisions.md:19` (2026-09-26, git blame) | "Recursion without step-indexing. Inductive types by least fixed points, codata by greatest fixed points with a mandatory `close`, loops by `fixD` over explicit state" | a decisions.md entry, not provisional. The record's wording, not a user quote |
| **D12** | `docs/decisions.md:30` (2026-09-26) | "The checker is derived from `CDerives`. Every step applies one rule; incompleteness is listed once, never fixed by changing the judgment." | entry, not provisional |
| **D15** | `docs/decisions.md:37` (2026-09-26) | "Shallow handlers are primitive; deep handlers are derived. A suspended computation is codata; one observation is a shallow handler, and a deep handler is a fold or a loop." | entry, not provisional |
| **D17** | `docs/decisions.md:40` (2026-09-26) | "A feature is done when it compiles. Spec, core proofs, checker, lowering and a running corpus program, together." | entry, not provisional |
| **D21** | `docs/decisions.md:50` (2026-09-26) | "Inversion lemmas, syntactic substitution over derivations, checker completeness and lowering proofs that invert typing bring per-rule pairwise burden back; take them on only with the cost stated" | entry. A cost rule, not a ban |
| **D35** | `docs/decisions.md:174` (2026-09-27) | "A div function returns a loop, `A ⇒ U(Loop B R)`; … running a loop is handling the effect" | entry |
| **D55** | `docs/decisions.md:685` (2026-10-01) | "`fn` is answering, `ctl` control. An effect has one kind of operation." Also: "Open: whether `ctl` is inferred from a clause's `k`, and whether the qualifier belongs on the handler." | **Provisional**: "the user's spelling guidance of 2026-10-01, to be settled after rewriting a sample of the corpus" |
| **D56** | `docs/decisions.md:696` (2026-10-01) | "Alternative not taken: a state-passing answer type (`W ⊸ F (R ⊗ W)`), which allocates closures per `yield`." | Provisional spellings. The design points are "the user's binding decisions of 2026-10-01" |
| **D57** | `docs/decisions.md:706`; `docs/effect-polymorphism.md` §11 (2026-10-01) | "Site freshness (R3) is checked by the elaborator only. It is an abstraction property, not a safety one: the FP holds either way. It may move into `[handle]` later as a pure restriction." "Operations that take computations (higher-order effects) are out of scope" | "the user's decisions of 2026-10-01", as recorded by an agent. No verbatim user quote is in the file. Read "out of scope" at the weaker strength ("not now"), per memory `not-now-is-not-never` |
| **D58** | `docs/decisions.md:715` (2026-10-01) | "Partial correctness and refunctionalising a heap machine in the backend were considered and not taken." "A `for` over data whose body performs an operation that resumes is a div loop over the source's cursor" | user decisions, spellings provisional |
| **D59** | `docs/decisions.md:744` (2026-10-01) | "A handler whose operations resume has a state, its parameters that are not `!` and the capabilities its clauses use, passed to each clause and at each resume" | user decisions |
| **U22** | memory `effects-are-core` (2026-10-02) | "Out of scope: kernel-level *equations* (a binary relation on BoLo's carrier, ν/op over moded contexts, η as an equation, optimiser correctness). They are optional and don't get pursued unless they become necessary for safety." Also: "I only want to focus on what gets us to a full safe effect algebra." In scope: "unary safety in the kernel … for full effects, including stored continuations holding borrows." | **optional**, not forbidden. The 2026-10-03 sign-off asks for handler laws "stated and proved over the KERNEL relation" (spec 01 U22) |
| **U5** | memory `effects-are-core` (2026-09-30) | nested handlers for different effects (the reconciler chain) "need to work, full stop" | decided |
| **U20** | memory `alloc-is-an-effect` (2026-09-28) | "alloc _is_ an effect, we already talked about that" | decided. "Tracking it in function types … is the not-yet-built part" |
| **U23** | memory `hard-stop-on-regress` (2026-10-02) | "My concern is going to be that one of that finite lists itself has a regress so we should make that a hard stop." "If the new work is n+1 and we are done, it's fine. If it's 3 and then 4 and then 5, no." | standing rule. #285 and #287 were user-directed continuations (spec 00 §0.3 item 2) |
| **THR** | memory `threads-are-required` (2026-09-29) | "we obviously need them", not now; "avoid choices that close the door" | requirement, later |
| **ASYNC** | memory `io-is-a-bundle-of-effects` (2026-09-30) | "Async is ours: a scheduler written as a handler over state machines." | user statement ("No WASI async") |
| **TOT** | memory `div-is-an-effect` (2026-10-01) | "i don't really care about totality in general unless we need it for something specific, it's really just an artifact of the borrow calculus that we can do it at all." The record adds: "Don't prioritise total variants (… total effectful counted loops …)" | preference |
| **LAWS** | memory `laws-first` (2026-10-02) | "I think we basically need to find the laws that we have to implement instead of trying to wing it." The record's list includes "the handler laws (return, op, forwarding, fusion)" and "linear-specific laws (weakening of a continuation as a finaliser, no duplication, the condition for multi-shot)" | standing instruction |
| **STALE** | memory `compiler-never-stale` (no date) | "a spec entry is not done until the feature compiles and a corpus program exercising it runs" | feedback, standing |
| **POL** | memory `no-function-coloring` (2026-09-27) | "the returning/suspending split is POLARITY … lowering is decided by shift cancellation read off the handler's type, not by an extra annotation" | user refinement |
| **SYN** | memory `mechanism-before-syntax` (2026-09-30); `syntax-choices-not-blocking` (2026-09-29) | "i don't want to do any sugar right now"; "honestly I don't care that much about syntax right now unless we're forced to keep something for some reason" | standing instruction |
| **ACTUAL** | memory `effect-calculus-spec-first` (2026-10-03) | "Make sure the agents are building the actual effects calculus not an approximation of it." | decided |
| **ONEW** | memory `structure-before-briefs` (2026-10-03) | "A new relation family, twin constant or side mechanism is a stop-and-report, never a deliverable." | feedback. The record's how-to, not a user quote |

The specification's own decision table (01 §4, U1-U24) quotes most of these. Its quotations were
checked against the memory files above, and they agree.

---

## OQ-35: Are operation types closed in lifetimes?

**Question.** SPEC §19 justifies re-entry of a handler site by "operation types are closed in
lifetimes", but no rule enforces it. Should `Closed E` be a premise of `[sig]`/`[handle]` (a), no
premise (b), or a premise only below the site's extent (c)? It also asks which closedness OQ-31's
cut-off means.

**Class: GENUINELY OPEN (settle by proof); EVIDENCED; partly ANSWERED-ELSEWHERE.**

- **What the code holds.**
  - The sentence is `SPEC.md:2418-2419` and `:2537`. It is a SPEC assertion, not a user quote.
  - `effHandle` (`Core/Fundamental.lean:366-372`) has no closedness premise.
  - `Row.Unwind` (`Core/EffBorrow.lean:133-134`) asks it of a borrow callback's row: `¬ VFree x o.A`
    and `VOutlives Δ a o.A` for every `a`.
  - `EffLeaf` (`Core/Types.lean:1141-1144`) asks `A.Cl 0 ∧ B.Cl 0`. `VTy.Cl` (`Core/Types.lean:375-391`)
    counts type variables only: `.imm _ A => Cl k A` and `.mut _ A => Cl k A` ignore the lifetime,
    and `.thunk _ => True`.
- **PROVED at σ = [].** `fundamentalC` (`Core/Fundamental.lean:434`) covers every `effHandle`
  derivation, including lifetime-open operation types, with no premise. So re-entry at a
  lifetime-open operation type is sound at Core's world today. The open part is only whether it
  stays sound at `W`.
- **The audit flagged the gap.** Audit M13 (`origin/effects-audit:docs/effects-audit.md:454-463`):
  "either add the closure premise to `effHandle` or delete the sentence."
- **Census (partial).** `grep` finds three effect declarations in `lib/`: `Fail[E]`, `Exhausted` and
  `Yield[T]` (`lib/fail.bc:17`, `lib/rec.bc:18`, `lib/yield.bc:13`). None mentions a lifetime or a
  borrow. Instantiating a type parameter at a borrowed type, and whether the elaborator rejects a
  lifetime in an operation type, were not checked.
- **The OQ-31 sub-question is answered elsewhere.** `docs/effects-tr/16-regress.md:297` (§16.5,
  T15's table) states which closedness the step-free cut-off needs: "an operation type mentioning a
  computation of its own row", cut by "operation arguments and answers are closed data". That is
  the no-self-reference reading, which is OQ-61, not closedness in lifetimes. §16.5 marks it "not
  stated separately" in Lean.
- **BoLo.** BoLo has no operations, so [TR] says nothing directly about operation types. What
  bears is `𝒱⟦T⟧δ`'s dependence on `δ` only at `T`'s free lifetimes (`vC_extend_of_not_free`, used
  in `Row.Unwind.tab_extend`, `Core/EffBorrow.lean:150-160`), which is why `OpSig.ent` at the
  handler's `δ` (`Core/EffRules.lean:42-44`) is stable under extensions of `δ`.
- **Decisions.** None settles it. `current-state-is-not-design` (2026-09-30) applies: the absence
  of the premise is not a decision.
- **Needs the user?** Only if the `W`-level probe (`ReentryLifetimeOpen`) fails, or if (a)/(c) are
  wanted for abstraction reasons. The spec's own default (b) is today's code.
- **Real unknown, or a deferrable detail?** A detail. It becomes real only at `W`, after OQ-8, OQ-9
  and OQ-58. Plan finding P10 (withdrawn `plan.md`, `git show d7809ac^:docs/effects-calculus/plan.md`)
  already recorded that "default (b) stands until that probe settles it".

## OQ-36: How the typing judgement identifies equal rows inside types

**Question.** `F_{Σ₁⊕Σ₂} A` and `F_{Σ₂⊕Σ₁} A` are different `CTy` terms, and `[sub]` converts
them only at the top of a judgement. Should rows be canonical (a), related by a type equivalence
(b), or a finite map in the syntax (c)?

**Class: GENUINELY OPEN (settle by proof); EVIDENCED. A deferrable detail.**

- `CTy.effOf` (`Core/Types.lean:155-157`) is a list fold, so permuted rows are different terms.
- `effSub` (`Core/Fundamental.lean:340-342`) takes `RowLe`, a subset of `find` results
  (`Core/EffRules.lean:699`). Its compatibility lemma is `sub_compatC` (`Core/EffRules.lean:774`),
  through `Row.tab_le` (`:728`).
- **PROVED at σ = [].** The relation reads only the table: `cC_effOf` (`Core/EffRules.lean:73-76`)
  rewrites `cC (CTy.effOf S R)` to `ewpTS … (opTable (Row.tab S δ))`. So permuted rows with the same
  table have the same meaning at every depth. What is missing is a typing-level conversion under
  `U`, `⊸`, `&`, `∀`, `ν`.
- No decision bears on it.
- **Needs the user?** No.
- **Real unknown?** No. It is a syntactic engineering choice. The conservativity statement it asks
  for is mechanical once an option is chosen.

## OQ-37: Handler carriers at every computation type

**Question.** `[handle]`'s carrier is `F_Σ R` only. Should handlers target every computation type,
including the state-passing `S ⊸ F_Σ R` and `C & D` (a, K-CARRIER), or `F_Σ R` only, other carriers
by encoding (b)?

**Class: GENUINELY OPEN (settle by proof, then user); CONSTRAINED; EVIDENCED in the sibling world
only.**

- **Code.** `retTy`, `clausesTy` and `kTy` (`Core/EffRules.lean:976-994`) all fix the carrier to
  `CTy.effOf S R`.
- **Sibling evidence.** `experiments/EffModel` (phase A, #235) is "an executable model … effects as
  models (handlers into any computation type)" (`experiments/EffModel/README.md:3-4`). It has
  `#guard` tests, not proofs, in a sibling calculus. `docs/effects-tr/03-dynamics.md:189` (D3.11,
  "every computation type is a model", Plotkin & Pretnar 2013 §2) is PAPER-ONLY in the TR's
  calculus. No result at σ = [] or at `W`.
- **Constraints.**
  - D59: a resuming handler's state is "passed to each clause and at each resume". That is how
    handler state works today (OQ-25's topic). It does not need a non-`F` carrier.
  - D56: the state-passing answer type was "not taken" for generators because it "allocates closures
    per `yield`". A kernel carrier `S ⊸ F_Σ R` is a different thing (the spec calls it
    allocation-free), so D56 does not rule it out. It does record why the encoding route costs.
  - ACTUAL ("the actual effects calculus not an approximation") and LAWS weigh toward (a). Plotkin
    and Pretnar's handlers target any computation type.
  - `experiments/HandlersControl` `no_uniform_comp` (`README.md:36, 79`) shows that no BoLo type
    solves `X = R ⊕ (A ⊗ (B ⊸ X))`. That bears on what (b)'s encodings can express, not on (a).
- **Needs the user?** Yes, after the σ = [] compatibility (`ewp_handle`, `handle_compatC` at
  `S ⊸ F_Σ R` and `C & D`) is known. It is a choice of calculus generality under ACTUAL.
- **Real unknown?** Partly. The σ = [] proof is likely routine (`cC` is defined per computation
  type, `Core/Relation.lean:149-160`). `C_1` at a `ν` carrier is unspecified in the spec itself. The
  first coarse plan can defer it.

## OQ-38: Is site freshness a premise of `[handle]`?

**Question.** `effHandle` makes the name fresh for the outer row but not for the body's context.
Add `n ∉ names(Γ₂) ∪ names(A)` to `[handle]` (a), or keep freshness (R3) in the elaborator (b)?

**Class: DECIDED (b) by D57, with the door open to (a).**

- D57 (2026-10-01): "Site freshness (R3) is checked by the elaborator only. It is an abstraction
  property, not a safety one: the FP holds either way. It may move into `[handle]` later as a pure
  restriction." `docs/effect-polymorphism.md:837-838` repeats it under "Decisions (the user's,
  2026-10-01; decision 57)".
- **Code agrees.** `hnS : ∀ o ∈ S, o.n ≠ n` (`Core/Fundamental.lean:370`) is freshness for the outer
  row only.
- **PROVED at σ = [].** "The FP holds either way" is `fundamentalC` with no freshness premise.
- **Not built.** `AccidentalHandlingTyped`, the configuration that would show accidental handling
  in Lean, does not exist.
- **Needs the user?** No, unless T-NAH or abstraction theorems are wanted at the kernel. That is the
  "may move later" clause, which the user left to a later call. The spec's default (b) cites D57
  correctly.

## OQ-39: Qualifier subsumption in `[sub]`

**Question.** Should `[sub]` admit a row whose operation qualifiers are pointwise below in the
grade order (`aff` below `lin`, `unr` below `aff`) (a), or exact qualifiers only (b)?

**Class: GENUINELY OPEN (settle by proof). A deferrable detail.**

- `RowLe` requires the same `OpSig` (`Core/EffRules.lean:699`), so the kernel has no qualifier
  subsumption.
- `contShare` (`Core/EffDefs.lean:144-150`) varies with the qualifier:
  - `en.q = .unr → ρ = PMap.empty`;
  - `en.q ≠ .lin → cancelOwed …`.

  No lemma relates `opTable` at two qualifiers.
- D55 leaves "whether the qualifier belongs on the handler" open. That is a different question.
- No other decision bears on it. Memory `multishot-only-if-free` (2026-10-02, "we also don't need
  multishot unless we get it for free") says only that `unr` should cost nothing.
- **Needs the user?** Only if the proof shows (a) holds and there is a reason to want it. No program
  in the spec needs it.
- **Real unknown?** No.

## OQ-40: The syntactic row class of a borrow callback

**Question.** K-BOR needs a syntactic premise standing for the semantic `TableOK`. Is the class the
full `Σ.NZ` with R-CLOSEDOP and R-T1 as named restrictions (a), one class per qualifier closed
under `⊕` (b), or an external `TableOK` premise (c)?

**Class: EVIDENCED; mostly DUPLICATE of OQ-56 plus OQ-2. What remains settles by proof.**

- **Today's classes.** `Row.Unwind` (`Core/EffBorrow.lean:133`) admits abortive operations only.
  `LinResume` (`experiments/GhostEnd/GhostEnd/Body.lean:141`) admits linear resuming operations only.
  Audit C4 (`effects-audit.md:330-341`) found them pairwise exclusive, so a `Fail ⊕ Yield` callback
  fits neither.
- **No `TableOK` exists in Lean.** `grep TableOK|BorOK` over `Core/` and `experiments/` finds
  nothing.
- **PROVED at σ = [], at tier 1.** The facts option (a) needs, with R-T1 and R-CLOSEDOP imposed:
  - `Row.Unwind.abort` (`Core/EffBorrow.lean:143-147`);
  - `Row.Unwind.tab_extend` (`:150-160`);
  - `Row.Unwind.out` (`:163-172`).
- **Where the content lives.** The class splits into two named restrictions:
  - "every operation abortive" (R-T1) is OQ-2's subject;
  - "closed and `'x`-free" (R-CLOSEDOP) is OQ-56's.

  Once they are decided, `borOK_tableOK` at tier 1 follows from the three lemmas above. Without
  R-T1 it waits on OQ-9.
- **Needs the user?** No, beyond OQ-2 and OQ-56.
- **Real unknown?** Only without R-T1, where it inherits OQ-9's unknown.

## OQ-41: A continuation captured inside a cancel run

**Question.** If a finaliser may perform a resuming operation (OQ-7 (a)), a captured `K` can hold
`ccatch`/`cfin` frames, and cancelling it may reach the wrong delimiter. Keep R-FINAB (a), or
change the machine (b, c)?

**Class: MOOT unless OQ-7 (a) is chosen.**

- **The case cannot arise today.** `effThen` types the finaliser at `S.abortOnly`
  (`Core/Fundamental.lean:360-365`, `hD`), so a finaliser cannot perform a resuming operation.
- **Decision.** Memory `errors-are-control-flow-effect` (user decision 2026-09-30, after the
  machine-checked `prog_stuck`, #191): "During a cancel, handlers inside the cancelled continuation
  are dead: an error raised by a finaliser while it runs under a cancel becomes a suppressed error,
  unwinding continues, and the canceller always receives 'cancelled'." This fixes the cancel error
  policy (abortive finaliser operations). It does not decide resuming ones.
- OQ-7 is outside this file's range. Its spec default is (b), R-FINAB, decided together with OQ-2.
- **Needs the user?** Only through OQ-7.

## OQ-42: The constructs the lowering rejects

**Question.** The lowering rejects three things that the machine handles:

- a name with both control and abortive operations;
- a cancel with raising finalisers under a re-entered site, where the static mask is inexact;
- handler names of 64 or more (`UInt64` mask).

Extend the lowering (a), or record them as lowering restrictions (b)?

**Class: CONSTRAINED toward (a) by D17 and STALE; ANSWERED-ELSEWHERE as backlog (#208). Not a
calculus question.**

- **The three rejections are in the code.**
  - The mask limit is `masks`, `Backend/Clos/Capture.lean:984-994`, with the message "a cancel whose
    finalisers may raise, under a handler named {n} ≥ 64, is not lowered".
  - SPEC §19 *Lowering*, `SPEC.md:2937-2939`, lists all three.
  - #208 (opened 2026-10-01, open, no comments) item 3 records all three as "Shapes rejected with a
    message … a documented rejection".
- **Constraints.**
  - D17: "A feature is done when it compiles."
  - STALE: "a spec entry is not done until the feature compiles".
  - Memory `effect-handling-is-erased` (2026-09-30, "Part of 18 needs to be effect handling is
    erased") with its cost-parity refinement.

  These make (b) a recorded gap against a decided position, not an acceptable end state. The spec
  says so itself.
- **Needs the user?** No decision is needed for the calculus. The calculus keeps every construct
  under either option. Which gap to close first is backend scheduling (#208).
- **Real unknown?** No. These are lowering engineering.

## OQ-43: Determinism up to renaming at every step, and two-run facts with array steps

**Question.** `head_rename` lacks the capture, `count`, `countTry` and `boundedFix` steps. The
two-run facts hold only for runs without array steps. Extend `head_rename` and leave arrays
unproved (a), prove block renamings (b), or route array laws through a binary FP (c)?

**Class: CONSTRAINED by U22 (binary half optional); EVIDENCED. Deferrable.**

- **PROVED, for runs with no array step and no capture step.** These live in
  `experiments/TwoRun`, a two-run machine-level world over Core, not `W`:
  - `head_rename` (`TwoRun/Rename.lean:359`);
  - `freshRun_det` (`TwoRun/Fresh.lean:255`);
  - `run_sim` (`TwoRun/Sim.lean:253`);
  - `fresh_run_image` (`TwoRun/Sim.lean:274`).

  `experiments/TwoRun/README.md:30` records that extending them to array steps "under a renaming of
  blocks" is not derived.
- **REFUTED.** `not_everyRunFootprint` and `not_everyRunFootprintRen` (`TwoRun/Refute.lean`) refute
  the every-run footprint forms. Their witnesses (`alloc (free 0)`, `staleE`) are concrete programs
  that run, per the README. Whether they type in `CDerives` was not checked here.
- **Who needs this.** It serves T-2RUN, T-SOUND's every-allocator observation and the binary halves
  of allocating laws. U22 (2026-10-02) makes "a binary relation on BoLo's carrier" "optional and
  don't get pursued unless they become necessary for safety".
- **Needs the user?** No.
- **Real unknown?** No for the plan. Option (a)'s `head_rename` extension is mechanical. Option (b)
  is a real unknown, but optional.

## OQ-44: What the open-lend component `σ` holds

**Question.** `TW`'s `ps` records 6.64 frames only, so a 6.65 lend open across a stop has no entry.
Should `σ` hold GhostEnd-form entries (a), should `TW` gain a 6.65 record (b, a kernel change), or
should `σ` be split into `σ_close ++ σ_under` (c)?

**Class: GENUINELY OPEN (settle by proof). A real unknown, in the first-probe cluster with OQ-8,
OQ-9, OQ-57 and OQ-58.**

- **BoLo.** 6.64 Imm Frame ([TR] p. 22, `tr.txt:1158`) and 6.65 Mut Frame ([TR] p. 24,
  `tr.txt:1268`) both open a fresh `Nα` lend and close it in `[α]`. That a 6.65 frame leaves no
  `ps` record is a property of our `TW` (`TW.mutFold`, `TW.mutUnfold`, `Core/World.lean:135-144`),
  not of the paper. 6.65's printed conclusion carries no record list. The record list is the
  borrow_lang typed-world repair, `docs/boca-rules.md` §12.72.
- **EVIDENCED (GhostEnd, not `W`).** GhostEnd already uses option (a)'s shape: `LEnt` entries
  (`Stacked.lean:100`) and `ReLend` (`:159`), with `imm` and `mut` entries. These are PROVED at the
  stacked relation on `main`:
  - `stack_step_imm`, `stack_step_other`, `stack_step_reborrow` (`StackStep.lean`);
  - `openS_nil_ewp` (whole stacks fold to `[]`);
  - `stack2_imm_yield`, `stack3_reborrow_yield` (every hypothesis discharged).

  None of it is at `W` with a relativised stop.
- **Constraint.** ONEW (2026-10-03): a new relation family or side mechanism is a stop-and-report.
  Option (b) changes the kernel's `TW`. Option (c) adds a second list. Both need the
  justification ONEW asks for.
- **Needs the user?** No. The probe (`OpenMutFrameCancel`, `MutLendRecorded`) decides. Option (b) is
  a kernel definition change and would need a SPEC entry.

## OQ-45: Does the arising guard stay in the clauses?

**Question.** Keep `guard_W` (the table `TabAt`) as a guard at `U`, `⊸` and `∀`, discharged at each
elimination (a), or drop it with every quantifier restricted to arising worlds (b)? First, is
`TabAt_W` a `TW` invariant (`tabAt_of_TW`, T-ARISE.0)?

**Class: EVIDENCED; CONSTRAINED by the arising principle. What is left settles by proof.**

- **REFUTED, and the witness does not arise.** `not_gfpAt_below`
  (`borrow-callbacks:experiments/GhostEnd/GhostEnd/Below.lean:196`; also on `gfp`) refutes GFP at the
  unguarded D16.1 at `σ = [x]`, with every hypothesis discharged. Its witness does **not** arise at
  `[x]`:
  - `not_tabAtS_innerView`, `tabAtS_comp`;
  - `wpG_below_not_arises` (`Arising.lean:139`);
  - `tabAtS_start_one` (`:120`);
  - `wpG_tabAtS_one` (`:112`).

  Branch `gfp-arising` d31cbb3, also on `borrow-callbacks`.
- **PROVED (GhostEnd's guarded relation `vRLa`/`cRLa`, not `W`).**
  - `guardS` (`Arising.lean:169`);
  - `lam_RLa`, `allI_RLa`;
  - `gfpAtA_nil` (`:374`): at `σ = []` it is `fundamentalC`;
  - `below_excluded` (`:446`): the refuted configuration is excluded.

  GFP at the guarded relation is not proved in general. Its other rows were not attempted after the
  refutation, under U23 (README step 3j, *Printed lemmas in the run-up*).
- **Not in Lean.** `tabAt_of_TW` (T-ARISE.0) does not exist. The single-entry facts
  `wpG_tabAtS_one` and `tabAt_start` exist. On `main`, `wpG_tabAt` and `wpTS_tabAt` (`Table.lean`)
  are [TR] 6.50 preservation for one lend.
- **The settled principle.** Memory `resources-are-of-the-calculus` (SETTLED): "§6's lemmas quantify
  over resources OF THE LINEAR CALCULUS … resources that arise". Memory `counterexamples-must-arise`
  (user, 2026-09): "our counter examples if they exist should be based on valid programs only."
  The guard is how the stacked relation restricts its quantifiers to arising resources.

  These records are about the BoCa formalisation. The brief applies the principle here ("§6
  quantifies over resources that ARISE"). They support restricting to what arises. They do not
  choose between a guard (a) and a restricted quantifier (b).
- **Needs the user?** No.
- **Real unknown?** Yes. Whether `TabAt_W` is a `TW` invariant at every depth is open. `borrow-callbacks`
  README step 3k's "Not settled here" records the related open item: a borrow constant's row must
  read its callback at `σ·y`.

## OQ-46: The world a stored payload is read at

**Question.** `ptoMutS`/`ptoImmS` store a payload at `ls₀`, the records longer-lived than the cell.
At `W`, should a stored payload (a `U` in a `Mut`, a stored generator, `Aff`, a `ν` cell) be read at
the longer-lived stack entries (a), or stack-free (b)?

**Class: GENUINELY OPEN (settle by proof); EVIDENCED by the record-list precedent; CONSTRAINED in
importance by U22's scope.**

- **The kernel's pattern.** `ptoMutS` (`Core/Relation.lean:43-48`) stores `P ls₀` with
  `x ∈ ls₀ ↔ x ∈ ls ∧ x.2 ⊐ b`. `ptoImmS` (`:52-55`) does the same at `⊓β̄`. Option (a) is the same
  rule lifted from the record list to `σ`.
- **The precedent.** `~/repos/borrow_lang/docs/boca-rules.md` §12.70 adjudicated this rule as the
  typed-world reading of [TR] p. 4 (`Mut_α`'s stored predicate "in the cell's own stratum") and of
  6.65's "α ⊏ γ ⊓ β". [CONF] 415:20: "For a mut cell, its lifetime β must be longer than the
  stratification index α … and so does its predicate P̂".

  §12.70 also records that the list-independent reading (option (b)'s analogue) failed against the
  record list: `not_mutThreadedMono`, `not_vDen_mut_at`, on the BoCa carrier, branch
  `probe/typed-worlds`, "not carried into this tree". That is evidence by analogy only. Nothing is
  proved at `W`.
- **Scope.** U22 (2026-10-02) puts "stored continuations holding borrows" in scope for unary safety,
  so this question is on the safety path, not optional.
- **Needs the user?** No.
- **Real unknown?** Yes. It belongs to stored continuations (OQ-28, `[gen]`). `lift-stage1` c9b3694
  (`Core/Gen.lean`, "WIP … stopped", sorry-free) transcribes `[gen]` at σ = [] under T1, with the
  payload at `Res_{δ(c)}`. It does not reach the question.

## OQ-47: Is reduction in every context contained in `≡`?

**Question.** The binary forms of the reduction-shaped laws need the "replace `M` by `N`" relation
to be a stuttering simulation (T-SI2). Does it hold for every `D` (a), for equality only (b), or
not at all (c)?

**Class: CONSTRAINED by U22 (binary half optional). Deferrable.**

- There is no such relation over the kernel. `run_sim` (`experiments/TwoRun/TwoRun/Sim.lean:253`) is
  a simulation for location renaming, with no logical relation (TwoRun world).
- U22: binary relations are "optional and don't get pursued unless they become necessary for
  safety". The unary halves of these laws do not need T-SI2. The spec's default states the binary
  forms and marks them not proved.
- **Needs the user?** No.
- **Real unknown?** Yes as mathematics, but it is off the safety path.

## OQ-48: Answering/control commutation at an affine operation, on the kernel

**Question.** L-INTER holds in T13.13's special case. P13.14 says it fails at an affine operation
whose clause cancels, but P13.14 was computed by hand in a sibling calculus. Machine-check it in
`CDerives` (a), or withdraw it and state L-INTER at `aff` (b)?

**Class: EVIDENCED (PAPER-ONLY, sibling); CONSTRAINED by U22. Settles by proof.**

- T13.13 and P13.14 are in `docs/effects-tr/13-adjunction.md:319-370`. P13.14 is "Computed here by
  hand from D3.6", in the TR's moded calculus (sibling). So it is PAPER-ONLY, by hand.
- Audit m2 (`effects-audit.md:513`): "Machine-check P13.14 or withdraw it."
- Memory `blockers-must-be-machine-checked` applies. A failure claim is a blocker and needs a Lean
  configuration.
- The two programs differ in an observation (`Obs_A`), which makes this the binary or observational
  half. U22 makes that optional. Building the two programs needs only `adequacyD_obs`
  (`Core/EffPrograms.lean:41`) at σ = [], so the probe is cheap.
- **Needs the user?** No.
- **Real unknown?** No for the plan. It is a cheap probe, off the safety path.

## OQ-49: The composite handler as a kernel term

**Question.** L-HFUSE needs `H₂ ∘ H₁`. Is the re-typed continuation a kernel term, with fusion for
`n₂`-free bodies (a)? Or is fusion stated for tail-resumptive clauses only (b)? Or should there be a
two-name handler (c)?

**Class: GENUINELY OPEN (settle by proof); CONSTRAINED by LAWS. Deferrable.**

- No Lean on handler fusion was found. `grep` over the `experiments/*/README.md` files and
  `docs/effects-tr` finds no composite-handler result.
- `κ` is built by the machine (`kappa`, `Paper/S3_Dynamics/Definitions.lean:438`), so whether a
  continuation of the needed type is writable as a term is an open syntactic question.
- LAWS (2026-10-02) lists "fusion" among the handler laws to implement. So the law has to be
  stated, and stating it needs the composite.
- U22 makes the binary half optional. A unary reading (the composite is typed and safe) does not
  exist yet.
- Option (c) is a new construct. ONEW and memory `few-formers` ("I want to be quite conservative in
  making new formers") weigh against it without a program that needs it.
- **Needs the user?** No.
- **Real unknown?** A modest one: whether the continuation is a term. It does not block safety.

## OQ-50: How the linear use of a continuation is observed

**Question.** "κ used exactly once" (T-LIN) is enforced only by typing. Prove it through syntactic
subject reduction (a), through the TR's one-shot-cell machine change (b), or state only the
resource half (no leak or double release) (c)?

**Class: CONSTRAINED by U22 toward (c) for the safety plan; GENUINELY OPEN for (a)/(b), which need
the user.**

- **Today.** `kTy` (`Core/EffRules.lean:976-982`) types the continuation. `NoOwn` (`Core/EffDefs.lean:38`)
  cannot see a dropped or duplicated `κ` that holds nothing owned.
- **Option (b)'s technique is PAPER-ONLY.** `docs/effects-tr/12-sources.md` §12.3 item 4: "A one-shot
  continuation as a heap cell freed by its use … exactly-once finalisation is linearity (T5.2.3–4)",
  in the TR's calculus (sibling). It is a machine change.
- **Constraints.**
  - U22's in-scope list is safety, including "leak freedom". Option (c) is the safety content.
  - LAWS lists "no duplication" among linear laws, which asks for more than (c).
  - Memory `effect-handling-is-erased`: the "resume once → direct call" lowering class relies on
    linear use. That is a lowering correctness concern, and OQ-23 (outside this file) is whether
    lowering correctness is a theorem.
  - Option (a) runs into D21: "syntactic substitution over derivations … take them on only with the
    cost stated".
- **Needs the user?** Only to want (a) or (b). The spec's default (c) needs no decision.
- **Real unknown?** No for the plan.

## OQ-51: Adequacy observed at a row

**Question.** T-ADEQ is stated at `F 1`. Should adequacy also be stated at `F_Σ 1` for designated
observable operations, such as a `main` that may `raise` (b), or only at `F 1`, with every program
closed by handlers (a)?

**Class: CONSTRAINED toward (a); depends on OQ-30. Deferrable.**

- **Decisions.**
  - D58 (2026-10-01): "A platform with no handler of it around `main` rejects an unhandled
    recursion statically". Programs are closed by a platform handler.
  - Memory `io-is-a-bundle-of-effects` (2026-09-27/30): `main` receives the capability bundle, and
    platforms are packages that provide it.

  Both point to closing every program with explicit or host handlers. That is (a) together with
  OQ-30's host handlers.
- `reclaim` (`Core/Fundamental.lean:534`) is the existing leftover lemma (σ = []).
- **Needs the user?** No, beyond OQ-30.
- **Real unknown?** No.

## OQ-52: Is a syntactic subject-reduction theorem part of the calculus?

**Question.** Type soundness is semantic (T-FP, T-ADEQ). Should a syntactic subject-reduction
theorem for `CDerives` over configurations with `κ` values be part of the calculus?

**Class: CONSTRAINED toward (a) by D21; MOOT unless OQ-50 (a) or a lowering proof needs it.**

- D21 (2026-09-26): "The Fundamental Property never inverts the judgment … Inversion lemmas,
  syntactic substitution over derivations, checker completeness and lowering proofs that invert
  typing bring per-rule pairwise burden back; take them on only with the cost stated". Subject
  reduction is exactly such a theorem. D21 does not forbid it. It requires the cost to be stated
  and taken on deliberately.
- D1 (`docs/decisions.md:5`): BoLo's "semantic model already proves safety, leak freedom and
  termination without step-indexing". Safety does not need subject reduction.
- **Needs the user?** Only if someone proposes (b), with its cost stated, as D21 asks.
- **Real unknown?** No.

## OQ-53: Is the elaborator proved, or each program checked?

**Question.** Per-program certifying check plus per-schema theorems (a), or an elaborator
correctness theorem over `Frontend/` (b)?

**Class: ANSWERED-ELSEWHERE (a), by the standing checker architecture; CONSTRAINED by D21.**

- D12 (2026-09-26): "The checker is derived from `CDerives`."
- SPEC §18 *Baseline* (`SPEC.md:2244-2248`): control effects are "checked by the certifying
  checker's §19 builders. `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD` keep their
  statements and cover every elaborated program."
- D48 and D53 (provisional) moved acceptance to "per-class laws on the elaborated terms", counts
  and reports.
- Memory `trust-not-assurance-ceremony` (2026-09-28): "the checker checks as far as it can and
  reports the smallest subterm it cannot type".
- Option (b) is an elaborator-completeness-style theorem of the kind D21 says to take on "only with
  the cost stated".
- **Needs the user?** No, unless (b) is proposed.
- **Real unknown?** No.

## OQ-54: The lend stack `σ` under a fork

**Question.** Under a fork, does `σ` stay a stack with each thread starting fresh (a), or become a
forest with each frame owned by one branch (b)? The ask now is only that D-W not exclude (b).

**Class: CONSTRAINED by THR (keep the door open); GENUINELY OPEN; deferrable.**

- THR (2026-09-29): threads "we obviously need them", later; "avoid choices that close the door".
  This is what the spec's "D-W must not be stated in a way that excludes (b)" implements.
- **Related issues.**
  - #22 ("Future: fork-join parallelism", open, 2026-09-26).
  - #212 ("Deterministic fork-join parallelism (rayon-like)", open, 2026-10-01). It proposes the
    disjoint parallel rule `{P₁ ∗ P₂} c₁ ∥ c₂ {Q₁ ∗ Q₂}`, which splits resources by `⋆`.
  - Neither has comments or a decision on open frames.
- **GhostEnd evidence, indirect.** `relend_respects_nesting` and `exists_relend_lifetimes`
  (`GhostEnd/Tree.lean`) treat the nesting as a forest, with stack order as a linear extension of
  it (README step 2, *The nesting*). That is a single-thread result.
- **Needs the user?** No now. Possibly when threads are designed.
- **Real unknown?** Not for the first plan.

## OQ-55: The declaration kind at the surface

**Question.** Keep `fn`/`ctl` on the effect declaration (a)? Or should declarations carry only the
signature, with the handler declaring model or comodel (b), or with the kind inferred from the
clauses (c)?

**Class: CONSTRAINED, with two records pulling different ways; deferred by SYN; depends on OQ-1.**

- **For (a).** D55 (2026-10-01, **provisional**, "to be settled after rewriting a sample of the
  corpus"): "`fn` is answering, `ctl` control. An effect has one kind of operation." D55 itself
  leaves open "whether `ctl` is inferred from a clause's `k`, and whether the qualifier belongs on
  the handler". Code: `EffSig.answering`, `Frontend/Elab/Effects.lean:63`.
- **Toward (b)/(c).** POL (2026-09-27): "lowering is decided by shift cancellation read off the
  handler's type, not by an extra annotation". That refers to returning versus suspending, the same
  axis.
- **Deferral.** SYN (2026-09-30): "i don't want to do any sugar right now". `syntax-choices-not-blocking`:
  surface a syntax question "only when a choice would be hard to reverse". The spec calls this
  surface syntax "a one-way door". It is one only once code depends on it.
- **Needs the user?** Yes, eventually, after OQ-1. Not for the calculus.
- **Real unknown?** No. It is a surface decision.

## OQ-56: Operation types that mention the lend's variable or the site's lifetimes, at a borrow callback

**Question.** `Row.Unwind`'s conjuncts make a borrow callback's operation types `'x`-free and
outliving everything (R-CLOSEDOP). Tier-2 programs need otherwise: an async read into a local
buffer passes `Mut 'x Buf`. Keep R-CLOSEDOP (a)? Add lifetime-polymorphic operations instantiated at
the lend (b)? Or allow only lifetimes outside the borrow (c)?

**Class: CONSTRAINED by U23 and OQ-2; EVIDENCED; GENUINELY OPEN as mathematics. Needs the user
through OQ-2.**

- **Code.** `Row.Unwind` (`Core/EffBorrow.lean:133-134`) has `¬ VFree x o.A ∧ ∀ Δ a, VOutlives Δ a o.A`.
  `Row.Unwind.out` (`:163-172`) uses the second conjunct to put every argument in `[α]`.
- **BoLo.** This is 6.65's conclusion: the callback's postcondition is
  `wp(e){[α] ∀v′. ℓ ↦ v′ –⋆ P̂(v′) –⋆ Q̂}` ([TR] p. 24, `tr.txt:1268-1269`). The withbor rows 6.172-6.174
  ([TR] `tr.txt:2469, 2542, 2570`) give the callback the type `∀'a ⊏ ⊓Δ. Imm/Mut 'a T₁ ⊸ ['a] T₂`.

  Whatever leaves the callback must lie in `Res_α`. A stop that hands the lent view to an outside
  handler moves it out of `[α]`. GhostEnd's admissibility condition states the same thing: "at the
  stop, the borrower's share less its view lies in `[α]`" (`experiments/GhostEnd/README.md`, step 1).
- **EVIDENCED (GhostEnd, not `W`).** `'x` in a borrow's **payload** is PROVED (`Payload.lean`:
  `payload_strict`, `PayFree`, `tabAt_wit`; README step 3g). That is `'x` inside the lent cell's
  content, not inside an operation type. No Lean addresses an operation type mentioning `'x`.
  `docs/effects-tr/16-regress.md` §16.6 lists the program shapes R-CLOSEDOP costs, and the
  workarounds: "hoist the owner outside the handler … pass the buffer by ownership … re-borrow after
  each resume".
- **Decisions.**
  - U23 (2026-10-02): tier 2 runs on a frozen list with a hard stop. Lifetime-polymorphic
    operations (b) are a new construct, which the frozen list does not contain.
  - U22 (2026-10-02) puts "stored continuations holding borrows" in scope for unary safety.
  - The spec records that #285 and #287 were user-directed continuations (00 §0.3 item 2).
  - So whether (b) is pursued is OQ-2's (tier) and OQ-33's (hard-stop) decision, both outside this
    file.
- **Needs the user?** Yes, via OQ-2/OQ-33. `LifetimePolyOpTableOK` would inform it.
- **Real unknown?** Yes. It is the tier-2 crux for the lead-axis async program.

## OQ-57: The closing-obligation list `τ` as an index beside `W`

**Question.** A suspended run passes the frames it must close (`τ`) to its table, and that list is
not `σ`. Keep `τ` as an explicit index of `wpG_W`/`ewp_W`, recorded as a defect (a)? Put a
`closer` field on each `σ` entry (b)? Or split `σ` (c)?

**Class: GENUINELY OPEN (settle by proof); CONSTRAINED by the one-world sign-off. A real unknown in
the first-probe cluster.**

- **Constraints.**
  - Memory `effect-calculus-spec-first` (2026-10-03) records the signed-off structure as "one Kripke
    world W".
  - ONEW: a side mechanism is a stop-and-report.

  Spec 00 §0.2 item 1 turns these into "an index beside `W` is a defect to report". Option (a) is
  therefore a recorded defect, not a design, as the spec says.
- **Evidence.** GhostEnd's `OpenS`/`bodyS` carry the lend stack as a parameter
  (`Stacked.lean:167, 174`). None of it states `ClosingInW`.
- **Needs the user?** Only if the probe refutes `ClosingInW`. Then the user must accept an index
  beside `W` against the sign-off.
- **Real unknown?** Yes.

## OQ-58: Is Core the `σ = []` instance at `U` (and at `share`, `KapRel`)?

**Question.** At `σ = []`, the new `U` clause also quantifies over non-empty extensions. Does
today's `vCE` thunk clause imply the new one at every rule that introduces a `U` value (a), or must
Core be redefined and every Core theorem re-proved (b)?

**Class: GENUINELY OPEN (settle by proof). A real unknown, the spec's second first probe.
EVIDENCED in GhostEnd for the candidates that lack the extension quantifier.**

- **PROVED for the GhostEnd relations without an extension quantifier at `U`.**
  - `vRLs_nil` (`main:…/Stacked.lean:502`), `cRLs_nil`, `gfpAt_nil` (README 3h).
  - `vRLa_nil`, `cRLa_nil`, `gfpAtA_nil` (`borrow-callbacks:…/Arising.lean:374`, README 3k).

  At `σ = []` these are the kernel relation, and GFP is `fundamentalC`.
- **Not proved for the extension-quantified candidate.** `vRLk`/`cRLk`
  (`borrow-callbacks:…/Extend.lean:62, 81`) quantify over extensions at `∀` only. They have no
  `σ = []` lemma (`grep` over `Extend.lean` finds none). `callback_ext_one` (`:167`) is the
  one-entry extension fact for a callback.
- **Related refutation.** `not_gfpAt_below` (`Below.lean:196`) is a refutation at a one-entry stack.
  It does not arise (see OQ-45).
- **BoLo.** [TR]'s `𝒱⟦U C⟧` has no world quantifier. The kernel's `∀ ls', Ext ls ls' ρ → …`
  (`Core/Relation.lean:127-128`) is the typed-world repair (`boca-rules.md` §12.72). The extension
  to stacks is ours, so this is a question about our construction, not about the paper.
- **Needs the user?** No. If it fails, option (b) is a kernel definition change under E-W and needs a
  SPEC entry.

## OQ-59: How a handler reaches into the scope of a scoped operation

**Question.** For K-SCOPE (scoped operations, not adopted), does the clause receive the scope
unhandled (a), handled first (b), or are scoped operations elaborated away (c)?

**Class: MOOT. It depends on OQ-12 choosing scoped or higher-order operations. D57 records them as
out of scope, at "not now" strength.**

- D57 item 6 (2026-10-01, recorded by an agent as the user's decision): "Operations that take
  computations are out of scope." `docs/effect-polymorphism.md` §7 (`:676-694`) shows each scoping
  construct (`catch`, `local`, `retry`, `timeout`, `finally`) as "a function over a passed
  computation that installs ordinary handlers". It says an operation taking a computation "needs a
  clause polymorphic in the body's row: rank-2 row polymorphism, Option 1. It is out of scope."
- Per memory `not-now-is-not-never`, "out of scope" is read as "not now". ACTUAL (2026-10-03) does
  not mention higher-order effects, and nothing found revisits D57 item 6.
- OQ-12, the parent, is outside this file. Its spec default (a), R-FO, matches D57.
- **Needs the user?** Only if OQ-12 is reopened. Then this becomes a literature question first
  (Wu, Schrijvers & Hinze 2014; Bach Poulsen & van der Rest, POPL 2023; both cited in
  `docs/effect-polymorphism.md:247`).

## OQ-60: The asynchronous scheduler against the negative-recursion cut-off

**Question.** A deep-handler scheduler's carrier `S ⊸ F_Σ R`, with `S` a queue of continuations at
that carrier, is a negative recursive type that R-NONEGREC excludes. Allow the deep scheduler by
relaxing OQ-31 (a)? Use a scheduler over `Loop_Σ` codata (b)? Or a comodel scheduler with threads
as codata (c)?

**Class: CONSTRAINED: (a) out by D7 unless D7 is revisited; (b)/(c) consistent with ASYNC and D15.
GENUINELY OPEN between (b) and (c). A real unknown on the lead axis.**

- **Against (a).**
  - D7 (2026-09-26): "Recursion without step-indexing".
  - `docs/effects-tr/16-regress.md` §16.5 (T15): "Each cut-off is a language decision. Relaxing any
    one brings step-indexing back."
  - TOT (2026-10-01) weakens one motive for avoiding step-indexing (totality "really just an
    artifact"). It does not revisit D7, and D1 still cites "without step-indexing" as a reason for
    starting from BoLo.
- **For (b) and (c).**
  - ASYNC (2026-09-30): "Async is ours: a scheduler written as a handler over state machines."
  - D15: "A suspended computation is codata; one observation is a shallow handler, and a deep
    handler is a fold or a loop."
  - Memory `portable-lowerings`: "async, generators and effect handlers lower to stackless state
    machines".
- **Evidence.**
  - `experiments/HandlersControl` `no_uniform_comp` (`README.md:36`) is PROVED (sibling). No BoLo
    type solves `X = R ⊕ (A ⊗ (B ⊸ X))`, which is the shape behind (a).
  - `origin/loophandle:docs/handlers-over-div.md` §5 [inspection]: a continuation spanning
    observations "makes the state recursive under `U`".
  - No scheduler has been typed at either (b) or (c).
- **Needs the user?** After the probe (`DeepSchedulerCarrier`, the async program at (b)), to choose
  between (b) and (c). Option (a) needs the user only to revisit D7.
- **Real unknown?** Yes. Async (#52) is the lead-axis program (memory `lead-axis-no-coloring`,
  2026-09-28).

## OQ-61: Operation types that perform their own effect (effect-recursive signatures)

**Question.** `spawn : U(F_{n:Async ⊕ Σ} 1) ↠ 1` names its own row inside its operation type, which
K-SIG forbids and T-DEF cannot interpret. Forbid it (a)? Allow a positive-only recursive signature
binder, interpreted as a least fixed point (b)? Allow negative occurrences too (c)? Or a `self` row
reference (d)?

**Class: CONSTRAINED: (c) out by D7; GENUINELY OPEN among (a), (b) and (d), settled by proof then
the user. A real unknown for async and threads.**

- **This is the cut-off that §16.5 means.** `docs/effects-tr/16-regress.md:297`: "an operation type
  mentioning a computation of its own row | operation arguments and answers are closed data … | not
  stated separately". So the step-free argument relies on (a) today, unproved in Lean.
- **Validation found it.** Finding S1 (withdrawn `plan.md`, `git show d7809ac^:docs/effects-calculus/plan.md:489`):
  "Under K-SIG the lead-axis async program is ill-formed."
- **Option (b)'s ingredients are PROVED at σ = [].** `ewp_mono` in the table (`Core/EffWp.lean:795`)
  and `opTable_mono` (`:951`) are the monotonicity facts a least fixed point needs.
  `SelfRowPositiveLFP` is not stated.
- **Decisions.**
  - D7 excludes (c), which needs negative recursion.
  - THR: threads later, keep the door open. Option (a) closes "a spawned thread spawns through the
    same name". The spec records that cost.
  - Memory `few-formers` (no date): "Every one we add is an ongoing proof burden". It bears on (b)'s
    recursive binder and on (d).
- **Needs the user?** Yes, after the probe.
- **Real unknown?** Yes. It decides whether tokio-style task spawning (#52) types.

## OQ-62: Folds and counted loops at a row

**Question.** The kernel's folds and counted loops have pure algebras. Type them at an effect row
(b, K-FOLDΣ)? Leave them pure (a)? Or allow abortive rows first (c)?

**Class: CONSTRAINED: (a) acceptable as a default by TOT and D58; (c)'s abortive case is the open
theory issue #178. Deferrable.**

- **Code.** `foldImm`/`foldOwn`/`foldReuse` (`Core/Fundamental.lean:311-327`) and
  `countFold`/`countTry` (`:183-191`) have pure algebras and steps.
- **Decisions and issues.**
  - D58 (2026-10-01): "A `for` over data whose body performs an operation that resumes is a div loop
    over the source's cursor". Effectful iteration is already expressible, as div.
  - D52 (provisional): "K4 is open: a `raise` in a kernel fold's algebra is rejected where the
    algebra is passed."
  - #178 (open, 2026-09-30, no comments): early exit from a kernel fold (K4). Its known partial
    results are `foldOwn_compatX`/`foldImm_compatX` (`experiments/CBPVMu`), at σ = [].
  - TOT (2026-10-01): "i don't really care about totality in general unless we need it for something
    specific". The record adds "Don't prioritise total variants (… total effectful counted
    loops …)". Total effectful folds are the total variant of what D58 already provides as div.
  - Memory `total-iteration-from-data` (2026-09-30): a total `for` is a fold over finite data. That
    is the reason the fold constants exist.
- **Validation found it.** Findings S4 and S14 (withdrawn `plan.md:492`, and the S14 row) found the
  spec had marked folds "unchanged".
- **Needs the user?** No now. Option (b) would be a kernel change wanted only if a total effectful
  fold is needed for something specific (TOT).
- **Real unknown?** No for the plan. `foldImm[Σ]` at a resuming row inherits OQ-9 and OQ-56.

## OQ-63: A partial-correctness `wp` beside `ewp_W`

**Question.** OQ-15's option (b), div as a row entry, needs a partial-correctness `ewpP_W`, a second
wp family. Write it as a recorded defect (a)? Use one mode-indexed definition (b)? Or have no
partial relation, with div as codata only (c)?

**Class: MOOT under OQ-15 (a), which the standing design is.**

- **The standing design for div is codata.**
  - D35 (2026-09-27): "A div function returns a loop, `A ⇒ U(Loop B R)`".
  - Memory `div-is-an-effect` (2026-09-28): "Core reading: a div function's result is the
    delay/`Loop` computation type."
  - D58 (2026-10-01), for `bounded_fix`: "Partial correctness and refunctionalising a heap machine in
    the backend were considered and not taken."
- The spec's own default makes `ewpP_W` "in force only under OQ-15 (b)".
- OQ-15 is outside this file.
- **Needs the user?** Only if OQ-15 (b) is chosen.

## OQ-64: The effect-dependent laws of rows

**Question.** State L-DISCARD, L-COPY and L-COMMUTE, graded by row and qualifier, with side
conditions derived from `opTable` (a), or transcribed from Kammar and Plotkin (POPL 2012) once read
(b)? Or state only L-DISCARD (c)?

**Class: CONSTRAINED by U22 (optimiser laws optional); literature-settleable. Deferrable.**

- U22 (2026-10-02) lists "optimiser correctness" among the kernel-level equations that are
  "optional". These three laws justify dead-call elimination and reordering, which is optimiser
  content. LAWS's list (algebraicity, handler laws, theory laws, composition, linear laws) does not
  name effect-dependent laws.
- Validation finding S11 (withdrawn `plan.md`) asked for them to be added. The spec added them, with
  the citation marked [R] because the primary source was not retrieved.
- No Lean exists.
- **Needs the user?** No.
- **Real unknown?** No for the plan. Reading Kammar and Plotkin settles the side conditions.

## OQ-65: An operation form with an explicit cancel continuation

**Question.** L-ALG's binary form fails to cover finaliser frames because no term carries the
finaliser on cancel. State algebraicity at plain, other-handler and borrow frames only (a)? Or add a
derived `op(V; y.M | D)` form, which needs a finaliser at the operation's row, that is OQ-7 (a) (b)?

**Class: MOOT unless OQ-7 (a). Binary half in any case (U22).**

- Option (b) is defined from `[then]` at a resuming row. That needs a finaliser that performs a
  resuming operation, which R-FINAB (OQ-7's default) excludes. See OQ-41 for the code (`effThen`'s
  `hD` at `S.abortOnly`).
- The question is about L-ALG's binary form, which U22 makes optional.
- **Needs the user?** Only through OQ-7.

## OQ-66: Is cancel an instance of Ahman and Bauer's signal?

**Question.** Classify cancel as a runner's own signal, with `D_K` as finalisation (a), or leave it
unclassified, with L-SIGNAL standing on its own derivation (b)?

**Class: MOOT for the plan (no law depends on it); literature-settleable.**

- The spec's own text: "Default if unresolved: (b): no law depends on the classification."
- Validation finding S8 (withdrawn `plan.md`) corrected an earlier misreading of Ahman and Bauer
  (arXiv 1910.11629 §3.2). The OQ-66 text as it stands quotes the corrected reading: a runner's own
  signal skips the continuation and runs `F`'s `kill` case.
- **Decisions.** U21 in spec 01 quotes memory `effects-are-core` (2026-10-02). Runners are out "as
  the user-facing effect mechanism", but "Don't cite 'runners are a dead end'" against the
  BoLo-as-runner architecture. Neither bears on a classification.
- U10 (cancellation not interceptable, 2026-09-30) is the behaviour any classification must match.
- **Needs the user?** No.

## OQ-67: The proof obligation of a handler that spans observations of a div computation

**Question.** K-HDIV, a handler around a div computation whose continuation spans observations,
is specified. Its compatibility is not proved. Under OQ-15 (a) it needs `HndLoopSpanCompat`; under
(b), `handle_compatC` at `ewpP_W`.

**Class: CONSTRAINED: the construct is required by U5, and its lift was parked by the user on
2026-10-01. GENUINELY OPEN as a proof. A real unknown, but deferrable in the first plan.**

- **The construct is required.** U5 (2026-09-30): nested handlers for different effects "need to
  work, full stop".
- **The lift was parked.** `origin/loophandle` 51772c1 (2026-10-01), `docs/handlers-over-div.md`:
  "**Parked** by the user before any Lean or probe was written: handlers around loops are not a
  priority, since the operator's shape (a generator pipeline with a handler per iteration) already
  works." This is an agent's paraphrase. No verbatim user quote was found. The spec's R-HDIV
  (per-observation handling unrestricted, the spanning form's lift deferred) matches it.
- **Evidence, inspection only.** `handle_loop` is built from existing rules: `unfoldN`, `nuOut`,
  `effHandle`, `effLet` (`handlers-over-div.md` §1, "[inspection]"). Its open-problems note matches
  the spec's: a continuation spanning observations stored in a state-passing carrier is recursive
  under `U` (T15; `no_uniform_comp`).
- D59 *Not built*: "a recursion whose body loops, whose `Exhausted` would be performed inside a
  loop, where a handler around a div computation is not provided".
- **Needs the user?** No new decision. The spanning form waits on its proof. If U5's "full stop" is
  meant to cover a whole-loop timeout now, confirming that against the 2026-10-01 parking would be
  the user's call. The two records do not conflict as written: per-observation handling meets U5's
  reconciler chain.
- **Real unknown?** Yes, for the spanning form. It depends on OQ-28 and OQ-46 (stored continuation
  bounds).

## OQ-68: The proof obligations of allocation as an effect

**Question.** K-ALLOC (allocation as an effect, with a host outermost handler and arenas as nested
handlers) is specified. Unproved:

- the host handler as a model;
- an arena's frame across `new`;
- T-ADEQ with the allocator as the host handler.

**Class: DECIDED (the construct, U20); the obligations are GENUINELY OPEN, settled by proof, and
deferrable. The presentation is OQ-30 (outside this file).**

- **Decided.**
  - U20: memory `alloc-is-an-effect` (2026-09-28), "alloc _is_ an effect, we already talked about
    that". "`box` is the explicit operation … the heap is the outermost linear State handler, and
    arenas are nested handlers. Tracking it in function types … is the not-yet-built part."
  - D30 (`docs/decisions.md:121-130`): I/O by capability.
- **PROVED at σ = [], as kernel constants, not as handler clauses.**
  - `alloc_compatX` (`Core/Compatibility.lean:579`) and `free_compatX` (`:539`) are [TR] 6.165 and
    6.166 at the typed world, recorded as `proved` in `Paper/INDEX.md:188`.
  - On the BoCa carrier: `Fig16.LogRel.alloc_compat` and `free_compat` (`~/repos/borrow_lang/docs/paper-inventory.md`,
    rows 6.165 and 6.166, `[as printed]`).
  - The host handler's `IsModel` at `opTable ⟦Alloc[T]⟧` is not stated. The arena configuration is
    not built.
- **Related open issues.** #77 ("allocS blocks are contiguous only on some runs", open) and #94
  ("arena and array helpers", open) bear on arenas. Neither records a decision.
- **Needs the user?** No for the obligations. OQ-30 (the presentation) is the user's.
- **Real unknown?** The host-handler half is close to mechanical. It rests on 6.165 and 6.166, which
  are proved. The arena frame at a resuming table is a real unknown that depends on OQ-9/T-FRAME.

---

## Patterns across OQ-35 to OQ-68

These are observations about the classification, not proposals.

1. **Most of the range is off the safety path or conditional.**
   - The binary or observational half, optional by U22: OQ-43, OQ-47, OQ-48, OQ-64, and OQ-65 in
     part.
   - Conditional on an option nobody chose: OQ-41 and OQ-65 (OQ-7 (a)), OQ-59 (OQ-12 (b)), OQ-63
     (OQ-15 (b)), and OQ-52 (OQ-50 (a)).
2. **The real unknowns concentrate in two places.**
   - Building `W`: OQ-44, OQ-45, OQ-57, OQ-58 (with OQ-8 and OQ-9, outside this file), and OQ-46.
   - The lead-axis async program: OQ-56, OQ-60, OQ-61, and OQ-67's spanning form.

   All settle by proof first. OQ-56, OQ-60 and OQ-61 then need the user.
3. **Decisions the spec's boxes did not cite.**
   - D7 (no step-indexing), which removes OQ-60 (a) and OQ-61 (c).
   - D21 (cost rule for inversion-style theorems), which bears on OQ-50 (a), OQ-52 and OQ-53 (b).
   - D58's "Partial correctness … considered and not taken", which bears on OQ-63.
   - The 2026-10-01 parking of handlers around loops, which bears on OQ-67.
   - §16.5's identification of the step-free cut-off with the no-self-row rule, which answers
     OQ-35's last sentence and links it to OQ-61.
4. **Tensions between records.** These are reported, not resolved.
   - **D55 against POL.** D55 (provisional, 2026-10-01) puts the kind on the declaration. POL
     (2026-09-27) reads lowering off the handler's type (OQ-55).
   - **TOT against D7.** TOT weakens one motive for D7 but does not revisit it (OQ-60).
   - **U5 against the parking.** U5's "full stop" and the 2026-10-01 parking of whole-loop
     handlers are compatible as written (OQ-67).

## Summary table

| OQ | class | one-line basis | needs user? |
|---|---|---|---|
| 35 | GENUINELY OPEN; EVIDENCED | PROVED at σ = [] (`fundamentalC` covers lifetime-open `effHandle`); unenforced SPEC sentence (audit M13); §16.5 says the step-free cut-off is no-self-row (OQ-61) | only if the `W` probe fails |
| 36 | GENUINELY OPEN (detail) | `cC_effOf` reads only the table, so meaning is permutation-invariant; only a typing conversion is missing | no |
| 37 | GENUINELY OPEN; CONSTRAINED | carrier fixed at `F_Σ R`; phase A's any-carrier is sibling `#guard`s only; ACTUAL and LAWS lean to (a); D59/D56 do not exclude it | yes, after the σ = [] proof |
| 38 | DECIDED (b) | D57 (2026-10-01): R3 "checked by the elaborator only … may move into `[handle]` later" | no |
| 39 | GENUINELY OPEN (detail) | `RowLe` needs equal `OpSig`; no qualifier lemma; no program needs it | no |
| 40 | EVIDENCED; DUPLICATE of OQ-2 + OQ-56 | at R-T1 + R-CLOSEDOP the class is `Row.Unwind`, whose table facts are PROVED; no `TableOK` in Lean | no (via OQ-2, OQ-56) |
| 41 | MOOT | arises only under OQ-7 (a); finalisers are typed at `S.abortOnly` today | via OQ-7 |
| 42 | CONSTRAINED; ANSWERED-ELSEWHERE (#208) | D17 and STALE make (b) a recorded gap; backend backlog, not calculus | no |
| 43 | CONSTRAINED (U22) | TwoRun renaming PROVED without array or capture steps; binary half optional | no |
| 44 | GENUINELY OPEN (real) | GhostEnd's `LEnt`/`ReLend` shape PROVED at the stacked relation, not `W`; (b)/(c) are new mechanisms (ONEW) | no |
| 45 | EVIDENCED; CONSTRAINED | `not_gfpAt_below` REFUTED, witness does not arise; guarded `vRLa` rows PROVED; `tabAt_of_TW` absent; arising principle SETTLED | no |
| 46 | GENUINELY OPEN (real) | (a) is the kernel's `ls₀` rule lifted, adjudicated in borrow_lang §12.70; stored borrows in scope (U22) | no |
| 47 | CONSTRAINED (U22) | no step-inclusion relation over the kernel; binary half optional | no |
| 48 | EVIDENCED (PAPER-ONLY, sibling); CONSTRAINED | P13.14 by hand (TR 13); audit m2; cheap `CDerives` probe; observational half | no |
| 49 | GENUINELY OPEN (modest) | no fusion Lean; LAWS lists fusion; (c) a new construct against `few-formers` | no |
| 50 | CONSTRAINED toward (c) | U22's safety scope; (a) hits D21; (b) is a machine change from the TR (PAPER-ONLY) | only to want (a)/(b) |
| 51 | CONSTRAINED toward (a) | D58 (platform handler around `main`), I/O bundle; depends on OQ-30 | no (via OQ-30) |
| 52 | CONSTRAINED; MOOT | D21: take on only with cost stated; needed only for OQ-50 (a) | only if proposed |
| 53 | ANSWERED-ELSEWHERE (a) | D12 + SPEC §18 Baseline certifying checker; (b) under D21 | no |
| 54 | CONSTRAINED (THR); deferrable | keep D-W open to a forest; #22/#212 undecided | no (later) |
| 55 | CONSTRAINED; deferred | D55 provisional (declaration kind) against POL (handler-type polarity); SYN defers surface | yes, later, after OQ-1 |
| 56 | CONSTRAINED (U23, OQ-2); GENUINELY OPEN (real) | 6.65's `[α]` postcondition is why `Row.Unwind` closes op types; `'x`-in-payload PROVED but not op types | yes, via OQ-2/OQ-33 |
| 57 | GENUINELY OPEN (real); CONSTRAINED | one-world sign-off (2026-10-03) makes an index beside `W` a defect | only if `ClosingInW` fails |
| 58 | GENUINELY OPEN (real) | `vRLs_nil`/`vRLa_nil` PROVED; extension-quantified `vRLk` has no `nil` lemma | no |
| 59 | MOOT | depends on OQ-12 (b); D57 item 6 "out of scope" (read as not now) | only if OQ-12 reopens |
| 60 | CONSTRAINED; GENUINELY OPEN (real) | D7 excludes (a); ASYNC and D15 fit (b)/(c); no scheduler typed | yes, after the probe |
| 61 | CONSTRAINED; GENUINELY OPEN (real) | D7 excludes (c); §16.5 relies on (a) unproved; `ewp_mono`/`opTable_mono` support (b); finding S1 | yes, after the probe |
| 62 | CONSTRAINED; deferrable | D58 makes effectful loops div; TOT deprioritises total effectful loops; K4 is #178 | no |
| 63 | MOOT | div is codata (D35, `div-is-an-effect`); D58 did not take partial correctness | via OQ-15 |
| 64 | CONSTRAINED (U22) | optimiser laws optional; Kammar and Plotkin unread | no |
| 65 | MOOT | needs OQ-7 (a); binary half | via OQ-7 |
| 66 | MOOT | no law depends on it (spec's own text); S8's misreading corrected | no |
| 67 | CONSTRAINED; GENUINELY OPEN (real, deferrable) | U5 requires the construct; parked by the user 2026-10-01 (agent paraphrase); inspection-only spike | no new decision |
| 68 | DECIDED (construct); obligations OPEN | U20; [TR] 6.165/6.166 PROVED at σ = [] and on BoCa; host `IsModel` and arena frame unproved | no (OQ-30 is the user's) |

## Sources read

**Draft spec** (`~/repos/borrow-core-effects-spec`, `effects-calculus-spec` 8296ab0):

- `docs/effects-calculus/99-open-questions.md`, in full for §1's register and OQ-35 to OQ-68;
- `01-scope.md` §4 (U1-U24) and §5;
- `00-structure.md` headings;
- the withdrawn `plan.md` (`git show d7809ac^:docs/effects-calculus/plan.md`), its residual
  validation findings S1-S16 and P1-P12.

**borrow-core `main` 8a1c326:**

- `docs/decisions.md`, entries 1, 7, 12, 15, 17, 21, 30, 35 and 48-61;
- `SPEC.md:2405-2560, 2240-2250, 2937-2945`;
- `docs/effect-polymorphism.md` §7, §11;
- `docs/effects-tr/12-sources.md` §12.3;
- `docs/effects-tr/13-adjunction.md:319-375`;
- `docs/effects-tr/16-regress.md` §16 summary, §16.5, §16.6;
- `Core/Fundamental.lean` (`effThen`, `effHandle`, `effSub`, `alloc`, `fundamentalC`, `reclaim`);
- `Core/EffBorrow.lean:128-175`;
- `Core/EffRules.lean` (`OpSig.ent`, `RowLe`, `cC_effOf`, `kTy`, `clauseTy`, `retTy`,
  `ewp_handle`'s hypotheses);
- `Core/EffDefs.lean:36, 144-150`;
- `Core/Types.lean:155-157, 375-391, 1136-1145`;
- `Core/Relation.lean:38-58, 120-165`;
- `Core/Compatibility.lean:537-580`;
- `Core/EffWp.lean:795, 951`, `Core/Steps.lean:596`, `Core/Demonic.lean:223`;
- `Backend/Clos/Capture.lean:980-996`;
- `experiments/GhostEnd/README.md` (steps 0-3i) and `GhostEnd/Body.lean:136-146`;
- `experiments/TwoRun/README.md` and its theorem lines;
- `experiments/EffModel/README.md`, `experiments/HandlersControl/README.md` (grep);
- `lib/fail.bc`, `lib/rec.bc`, `lib/yield.bc`;
- `Paper/INDEX.md:188`.

**Branches:**

- `origin/gfp` daf56c0 and `origin/gfp-arising` d31cbb3 (diff stats);
- `origin/borrow-callbacks` 5cfe062: GhostEnd README steps 3j-3l, `Arising.lean`, `Below.lean`,
  `Extend.lean`, `Stacked.lean` declaration lines;
- `origin/lift-stage1` c9b3694: `Core/Gen.lean` header;
- `origin/loophandle` 51772c1: `docs/handlers-over-div.md`;
- `origin/effects-audit`: `docs/effects-audit.md` C4, M1, M8, M13, M14, m2;
- `~/repos/borrow-core-effect-callbacks` (log only).

**Paper and BoCa:**

- [TR] `3764117-supplement.pdf`, extracted text: Definitions 4.8/4.9 (`𝒱⟦Imm⟧`, `𝒱⟦Mut⟧`), 6.60,
  6.62, 6.64, 6.65 (statement and the start of its proof), 6.66, 6.147, 6.150, 6.172-6.174;
- `~/repos/borrow_lang/docs/paper-inventory.md`, rows 6.64-6.66, 6.150, 6.165, 6.166;
- `~/repos/borrow_lang/docs/boca-rules.md` §12.70.

**GitHub:**

- #290 (body), PR #461 (body);
- #178, #208, #22, #212 (bodies; no comments);
- PR #233 (body and closing comment);
- the issue list (titles) outside #291-#460.

**Memory files:**

- `effect-calculus-spec-first`, `effects-are-core`, `div-is-an-effect`, `alloc-is-an-effect`;
- `threads-are-required`, `multishot-only-if-free`, `hard-stop-on-regress`;
- `compiler-never-stale`, `effect-handling-is-erased`, `total-iteration-from-data`;
- `structured-recursion-only`, `errors-are-control-flow-effect`, `no-issues-for-open-questions`;
- `structure-before-briefs`, `few-formers`, `syntax-choices-not-blocking`;
- `current-state-is-not-design`, `no-function-coloring`, `lead-axis-no-coloring`;
- `mechanism-before-syntax`, `trust-not-assurance-ceremony`, `zero-cost-target`;
- `portable-lowerings`, `defaults-not-prohibitions`, `not-now-is-not-never`;
- `io-is-a-bundle-of-effects`, `no-traits`, `resources-are-of-the-calculus`;
- `counterexamples-must-arise`, `arising-tests-are-directional`, `laws-first`.
