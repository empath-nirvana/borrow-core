# 05a · The draft spec's open questions OQ-1 to OQ-34, against what we already have

This file takes the draft effect-calculus specification's register of open questions
(`docs/effects-calculus/99-open-questions.md` @ `effects-calculus-spec` 8296ab0), questions OQ-1
to OQ-34, and checks each one against the user's recorded decisions, earlier documents and issues,
and the Lean results that already exist. The draft failed validation (#290). Its register is a
list of questions here, not a source of truth.

It is an inventory. It proposes no mechanism.

## State read

| ref | commit |
|---|---|
| `main` (`~/repos/borrow-core`) | 8a1c326 |
| `effects-calculus-spec` | 8296ab0 |
| `effects-audit` | 6db9b86 |
| `gfp` / `gfp-arising` / `borrow-callbacks` | daf56c0 / d31cbb3 / 5cfe062 |
| `lift-stage1` | c9b3694 (WIP, "not for merge") |
| `loophandle` | 51772c1 |
| `effect-callbacks` (PR #233, closed unmerged) | c321bd2 |

No Lean was built for this file. Every status below is read off declarations, their docstrings and
the READMEs. "PROVED" means a declaration exists whose README and banner say it is sorry-free. I
grepped for `sorry` in the files I cite, and found none.

## Classes

- **DECIDED**: a recorded user decision settles it. The decision is quoted with its date and
  strength.
- **CONSTRAINED**: decisions rule some options in or out without choosing one.
- **EVIDENCED**: Lean results or recorded findings bear on it.
- **ANSWERED-ELSEWHERE**: an earlier document or issue already settled it.
- **DUPLICATE**: the same question as another OQ.
- **MOOT**: it depends on an option nobody chose, or on a construct nothing needs.
- **MIS-POSED**: it rests on a misreading of BoLo, of our code, of a decision or of a source.
- **GENUINELY OPEN**: none of the above settles it.

An entry may carry two classes, for example "EVIDENCED + GENUINELY OPEN".

## Worlds

A result is tagged with the world it lives at. Results at one world do not transfer to another.

- **[Core σ=[]]**: Core's kernel relation (`vC`/`cC`, `ewpTS`/`wpG` with today's stop condition,
  `Core/EffDefs.lean:27-40`). It is not the planned Kripke world `W`.
- **[GhostEnd]**: the stacked or re-lendable relations `vRL`, `vRLg`, `vRLs`, `vRLa`, `vRLk` in
  `experiments/GhostEnd`. Some GhostEnd theorems are stated at Core's `cC` and are tagged
  [Core σ=[]] (GhostEnd experiment).
- **[EffModelRel]**: the sibling calculus of phase B, `experiments/EffModelRel`. It has no BoLo
  resources, no machine and unmoded contexts.
- **[paper]**: the BoLo paper layer (`DerivesWf`, `Paper/`). It has no effects in the kernel.
  `experiments/HandlersAsBorrows` and `experiments/HandlersControl` live here.
- **[W]**: the planned world. **No result in this file lives at [W].**

---

## Cross-cutting findings

These recur across several entries, so they are stated once here.

**F1. The draft treats "an effect visible in a function's type" as colouring. The user's
records do not.** OQ-1 and OQ-30 argue that putting an effect in a row "colours" the function,
and that this is the user's call under U7. The user's records say otherwise:

- `io-is-a-bundle-of-effects` (2026-09-30): "the user wants effects visible in types without
  function coloring" and "A function's type shows its effects."
- Decision 35 (`docs/decisions.md:174-184`) puts div in the type (`A ⇒ U(Loop B R)`). It says
  there is "no function coloring" because "a higher-order function serves total and div
  callbacks alike by specialization… the mechanism later control effects… reuse".
- `no-function-coloring` (2026-09-27): "the color exists only in compiled output, never in types
  the programmer writes"; "the returning/suspending split is POLARITY".

Read this way, colouring means having to duplicate higher-order code. An inferred row with
specialisation is not colouring. Both OQs therefore lose the part of their case that says a
proof cannot decide them.

**F2. Option (b) of OQ-9, capture rebasing, already has Lean at today's stop condition.**
`experiments/GhostEnd` (on `main`) is the ghost-end route. At a stop it ends the lend, as 6.65's
exit does at a return, and it re-lends at a fresh lifetime on resume. The fresh lifetime is
chosen by 6.65's own (H4), once per resumption. Because the lend is closed at the stop, the stop
condition `ps' ↔ ps` is met unchanged. So these results are stated at Core's `ewpTS`/`cC`:

- `withbor_spans_yields_cC` (`experiments/GhostEnd/GhostEnd/Program.lean:188`);
- `spans_two_affine_yields` (`Drop.lean:318`, the cancel path for a 6.65 lend);
- `imm_spans_yield` (`ImmLend.lean:252`, a 6.64 lend, resume path);
- `withborR_compat` (`Drop.lean:108`, the unwinding borrow at a resuming row).

Each is PROVED at [Core σ=[]] for particular borrowers or programs. The general theorem over every
typed program (GFP, D16.2) is not proved:

- as first stated it is REFUTED at `σ = [x]` (`not_gfp`, `Below.lean:282` @ `gfp`), by a witness
  that does NOT arise (`wpG_below_not_arises`, `Arising.lean:139` @ `gfp-arising`);
- the guarded restatement `GFPA` is stated but not proved (`Arising.lean:238` @ `gfp-arising`).

The draft registers OQ-9 as "the first unknown" and probes option (a), a relativised stop. It
does not record that (b)'s route exists at today's stop.

**F3. Mis-citations.** OQ-20 and OQ-27 cite "#279, external input" for `withtake` and for η at
cancellable operations. Both items are in a comment on **#251** (2026-10-02T16:10Z). #279 is the
D16.1 issue and contains neither. OQ-14 cites "T2, #173" for generative instances. #173 is "an
outlives rule for thunks `U C`" (theory index T2, `docs/theory-index.md:657`). It is the confinement
that generative instances would need, and it is also option (b) of OQ-28. The draft does not
cross-link OQ-14 and OQ-28 through #173.

**F4. The recorded cancel-error decision and the built SPEC disagree.** This bears on OQ-21.

- The user decision recorded on #186 (2026-09-30T23:00Z) reads: "A finaliser's raise under a
  cancel becomes a suppressed error, and unwinding continues to the canceller, which always
  receives 'cancelled'." The memory record `errors-are-control-flow-effect` says the same.
- SPEC §19 *Cancels* (`SPEC.md:2509-2515`) was committed later, in 7de358e
  (2026-09-30 20:21 -0400, i.e. 2026-10-01T00:21Z). It says: "An error raised by a finaliser
  during a cancel is re-raised at the canceller… the first is re-raised, and the rest are
  suppressed". PR #191 calls this "decision C".
- I found no record that the user approved the change from "always cancelled" to "re-raise the
  first".

**F5. Many questions disappear if tier 1 comes first.** The user's record already puts tier 1
first: "Stage 1 of the kernel lift (the safe effect algebra at tier 1) doesn't depend on this list
and proceeds regardless" (`hard-stop-on-regress.md:22`, 2026-10-02). With tier 1 first, OQ-3,
OQ-7's resuming half, OQ-8, OQ-9, OQ-10 and OQ-29 do not bear on the first lift. `docs/effects-tr/16-regress.md`
§16.6 (i) lists what tier 1 still has to prove:

- T15.4-T15.6 and `[gen]`;
- §14.2 case (E);
- O2, the in-place half of T9.2;
- O8.

---

## The questions

### OQ-1. One signature, two implementations: how answering and control handlers relate

*Question.* Is an answering handler (a capability, `withswap`) a derived form of `[handle]` with
a tail-resumptive clause (a), or do both stay primitive under one protocol (b)? The draft says (c),
a recorded split, is excluded.

*Class.* **CONSTRAINED + EVIDENCED + MIS-POSED (in its framing).**

*Decisions.*

- The sign-off (2026-10-03, memory record `effect-calculus-spec-first`) adopts the audit's
  structure, "Sig, models/comodels". So handlers are models and capabilities are comodels of one
  `Sig`, which excludes (c).
- `effects-are-core` (2026-10-02) records the user's rejection of built-in control constructs:
  "i hate sort of version B". It also records the user's view that half-implemented user-definable
  effects would be "constant friction". Effects are all or nothing.
- `no-function-coloring` (2026-09-27) says the kernel's "one thing it must know is each
  operation's kind — returning (tail-resumptive → direct call) vs suspending". It refines this to
  "the returning/suspending split is POLARITY". So the user's own framing makes "answering" a kind
  of operation within one mechanism.
- Decision 55 (`docs/decisions.md:686`, provisional, 2026-10-01): "`fn` is answering, `ctl`
  control. An effect has one kind of operation."

*Evidence.*

- An answering handler is `withbor` form (2): `translate_typed`
  (`experiments/HandlersAsBorrows/HandlersAsBorrows/Translate.lean:190`), `effect_safety`
  (`Safety.lean:55`) and `handle_is_shift` (`Safety.lean:115`). These are PROVED at [paper], for a
  pure, tail-resumptive, single-operation fragment.
- `handle_fold` (`Core/Handlers.lean:211`) and `ewp_handle` (`Core/EffRules.lean:615`) are at
  [Core σ=[]]. Nothing relates them.
- TR §8.2 (`docs/effects-tr/08-decisions.md:67-117`) puts capabilities as comodels in phase B's
  Lean, at [EffModelRel].

*Framing.* The draft says a proof "cannot choose which colouring the language adopts". By F1, the
user does not count rows as colouring, so that clause does not apply.

What is left:

- whether `AnsweringIsTailHandler` holds, which is settleable by proof;
- whether answering operations appear in rows, which is a visibility question. The user's records
  ("A function's type shows its effects") already lean toward visibility.

*Needs the user?* Proof first. User confirmation is light. This is a real structural unknown and
it is on the kernel path.

### OQ-2. Tier 1 or tier 2 first

*Question.* Does the first kernel lift implement tier 1 under R-T1 (a), target tier 2 (b), or
stay at tier 1 permanently (c)?

*Class.* **CORRECTED by the user (2026-10-18): div is a handled effect.** Not "DECIDED (a)".

*The correction.* The user, 2026-10-18: "The original plan was Div being a handled effect." The
user's own words on record are "Div should be an effect" (2026-09-28) and that the runtime driving
`main` is the outermost handler. The sentence "Div is not an algebraic effect; it stays
codata/delay, and nobody should pretend it is handled" was a recorder's, not the user's. Neither
(a) as recorded nor (b) is the plan: div is an effect whose operation loops perform, handled by
the runtime's driver, `div_fuel` and the reification of a loop value. Its model and lowering are
`docs/pipeline-architecture.md` (#552), starting with a proof spike. What is listed below was
drift, kept as the record of how the reading arose.

*Decisions.*

- `hard-stop-on-regress` (2026-10-02, a rule recorded from the user's words): "Stage 1 of the
  kernel lift (the safe effect algebra at tier 1) doesn't depend on this list and proceeds
  regardless." Tier 2 runs only on the frozen list, under the hard stop.
- `effects-are-core`, "Goal, sharpened" (2026-10-02): "In scope: unary safety in the kernel …
  for full effects, including stored continuations holding borrows." So tier 2 is in scope, which
  excludes (c).
- The sign-off's correction (00 §0.3 item 2) is carried as user-signed by
  `effect-calculus-spec-first`. It says #285 and #287 were continuations the user directed, so
  tier 2 did not halt by rule.

The residual is how the hard stop applies from here. That is OQ-33.

*Evidence.* See F2, F5 and OQ-9.

*Needs the user?* No for the order, which is recorded. Yes for OQ-33.

### OQ-3. Does a handler site open a lifetime?

*Question.* Does every handler site open a stratum (a)? Or is "a handler between two lenders" a
named restriction (b)? Or do only answering handlers open one (c)?

*Class.* **EVIDENCED + GENUINELY OPEN.** Settleable by proof. It applies to tier 2 only.

*Evidence.*

- Answering handlers open a lifetime: `handle_is_shift` [paper].
- `effHandle` opens none (`Core/Fundamental.lean:367-372`).
- GhostEnd's own route needs a handler extent. Its README, step 1 (`experiments/GhostEnd/README.md:112-118`
  on `main`), says: "This needs the handler body to start in `Res_h`. That is a typing invariant,
  and the kernel does not establish it today, because handlers open no lifetime. It would be
  established in `[handle]`'s compatibility lemma (`handle_compatC`) once the handler takes an
  extent `∀'h`." The supporting lemmas are `wpG_box`, which is [TR] Lemma 6.147 at `wpG`, and
  `frozen_above_extent`. So the route that has Lean behind it presupposes (a).
- The stacked line assumes that every stop crosses every entry (`AllCross`,
  `experiments/GhostEnd/GhostEnd/StackStep.lean:182`). It is discharged only at constant-`true`
  crossing (`StackStep.lean:1280`).
- #278 (open; a frozen tier-2 item under the hard stop) asks for `effHandle`'s inner stop "with a
  handler frame passing the lender's stops".

*Needs the user?* Only if (b) would exclude a program the user wants. Under tier 1 first (F5) it
does not bear on the first lift and can be deferred.

### OQ-4. Is a binary relation over Core's world in scope?

*Question.* Is there one binary relation `≈` over `W` (a)? Or binary laws via TwoRun's
determinism route, with (a) for the rest (b)? Or is it out of scope (c)?

*Class.* **DECIDED.**

*Decision.* `effects-are-core`, "Goal, sharpened" (user, 2026-10-02): "Out of scope: kernel-level
*equations* (a binary relation on BoLo's carrier, ν/op over moded contexts, η as an equation,
optimiser correctness). They are optional and don't get pursued unless they become necessary for
safety." The strength is "optional … unless they become necessary for safety". That is not now,
not never. The sign-off (2026-10-03) asks for the handler laws over the kernel relation. Their
unary halves need no binary relation.

So (a), and the "(a) for the rest" part of (b), are not pursued unless a safety need appears. The
draft's own default, "every law stated; binary half marked not proved", matches the decision. The
draft quotes the decision in the box and still files the question as a user decision.

*Evidence.* At [Core σ=[]], restricted to runs with no array step: `freshRun_det`
(`experiments/TwoRun/TwoRun/Fresh.lean:255`) and `run_sim`/`fresh_run_image` (`Sim.lean`), both
PROVED. The binary laws exist only at [EffModelRel].

*Needs the user?* No.

### OQ-5. Standing of EffModelRel

*Question.* Keep EffModelRel as evidence with a banner (a), or archive it (b)?

*Class.* **CONSTRAINED, toward (a).**

*Decisions.* `effects-are-core`, "Goal, sharpened" (2026-10-02): "Laws: validated on the model
(phase B, #247/#255)." That gives EffModelRel a named role, and archiving it would remove that
role. The sign-off (2026-10-03) moves the required laws to the kernel relation, which is why the
banner is needed.

*Evidence.* The binary FP, soundness, H-laws, tensor and ν laws are PROVED at [EffModelRel]
(`experiments/EffModelRel/README.md`; TR status table, `docs/effects-tr/README.md`). Nothing
transports to `CDerives`.

*Needs the user?* Only to confirm. It is housekeeping and not a design unknown.

### OQ-6. Typed role declarations or shape recognition

*Question.* Should the elaborator identify iteration, exhaustion, heap drivers and layers by
typed role declarations (a), or by shape with ambiguity rejected (b)?

*Class.* **GENUINELY OPEN (surface).** Deferrable.

*Decisions.*

- Decisions 56 and 58 (2026-10-01; spellings provisional) record shape recognition as built: "The
  elaborator knows an iteration effect by its structure" (`docs/decisions.md:698`); "the
  exhaustion effect is found by its structure" (`:734`).
- `current-state-is-not-design` (2026-09-30): built is not decided.
- `syntax-choices-not-blocking` (2026-09-29): surface a syntax question "only when a choice would be
  hard to reverse". The audit calls this one a one-way door.
- `no-magic-comments` (2026-09-30) excludes comment directives. It does not exclude typed role
  declarations.
- `mechanism-before-syntax` (2026-09-30): no sugar until the mechanism is used.

*Evidence.* `Env.iterEff` and `Env.exhEff?` (`Frontend/Elab/Effects.lean:229, 240`).

*Needs the user?* Yes, eventually: it is a one-way door. It is not on the kernel path, so it can be
deferred.

### OQ-7. Finalisers at a non-abortive table

*Question.* Should finalisers, the unwinding borrow forms and the effectful `Clo` close be stated
and lifted at every `TableOK` table (a), or kept abortive-only (b)?

*Class.* **EVIDENCED + CONSTRAINED + GENUINELY OPEN.** Settleable by proof.

*Evidence.*

- The draft's premise is that "the unwinding forms exist only at abortive callback rows". That is
  true of the kernel, but no longer of our Lean. `withborR_compat` (`experiments/GhostEnd/GhostEnd/Drop.lean:108`)
  lifts the unwinding borrow `withborU d` to a callback row whose operations resume, with finaliser
  `d : Ref T ⊸ 1`. Its finaliser table is still abort-only (`hA : Ta.AbortOnly`). The lemma is
  PROVED at [Core σ=[]] (GhostEnd experiment, ghost-end route). `spans_two_affine_yields`
  (`Drop.lean:318`) discharges every hypothesis on one program.
- `GhostEnd/Frames.lean` has 6.64's `hQ`, 6.66 and 6.150's view copy at resuming tables
  (`opTable_extR`, `ewpTS_M_antiFrameR`, `ptoImm_dup`).
- TR T9.2's in-place half is PAPER-ONLY. Its open step is O2.

*Decisions.* `effects-are-core` (2026-10-02) says effects are all or nothing ("constant friction").
That argues against (b) as a permanent restriction, but not against (b) as the tier-1 default.

*Needs the user?* After T-FRAME at a resuming table, only if (a) fails. The abortive half is
tier 1. The resuming half is tier 2 (F5), so it can be deferred.

### OQ-8. Where the future-world quantifier sits; the representation of entries; `σ.WF`

*Question.* Which of six candidate clause sets places the Kripke future-world quantifier? Do stack
entries carry variables? Is `σ.WF` a freshness condition?

*Class.* **EVIDENCED + GENUINELY OPEN.** Settleable by proof. It applies to tier 2 only.

*Decisions.* The sign-off (2026-10-03) carried critic correction 3: "The placement of the
future-world quantifier is OQ-8, to be settled by Lean, not prose" (00 §0.3 item 3). So it is
settle-by-proof by user-signed instruction.

*Evidence.* All at [GhostEnd]:

- `vRLs_nil`/`cRLs_nil`/`gfpAt_nil` (`Stacked.lean:613` on `main`), PROVED;
- `not_gfp` (`Below.lean:282` @ `gfp`), REFUTED, by a witness that does NOT arise
  (`wpG_below_not_arises`, `Arising.lean:139` @ `gfp-arising`);
- `vRLa_nil`/`gfpAtA_nil` (`Arising.lean:374`), PROVED;
- `lam_RLa`/`allI_RLa` (`:478`, `:815`), PROVED;
- `GFPA` (`:238`), stated, OPEN;
- `vRLk`/`cRLk` (`Extend.lean:62, 81` @ `borrow-callbacks`) are (b0). `callback_ext`/`callback_ext_one`
  (`:131, :167`) are PROVED. There is no `vRLk_nil`, as the audit notes.
- #279 was closed in favour of the deleted plan issues and then reopened (2026-10-03T11:24Z).

*Needs the user?* No. Under tier 1 first, "the relation stays the `σ = []` kernel" is the draft's
own default, so it can be deferred.

### OQ-9. Open 6.64 frames handed to a continuation that is cancelled, dropped or resumed between lenders

*Question.* When a stop leaves lends open, how are they closed on every path the continuation can
take? The options are carried frames (a), capture rebasing (b), or R-T1 (c).

*Class.* **EVIDENCED + GENUINELY OPEN.** Settleable by proof. It applies to tier 2 only.

*BoLo reading.* [TR] Theorems 6.64 (Imm Frame), 6.65 (Mut Frame) and 6.66 (Anti Frame) are stated
over `wp`, a run to a value (`3764117-supplement.pdf`, §6.3, text lines 1158-1385 of `pdftotext`).
BoLo has no stops, so "a lend open at a stop" has no printed counterpart. Every lift to a stop is
ours.

The ghost-end route uses the printed proofs at each unfolding:

- `wpG_I_frameX` / `wpG_M_frameX` at the exit;
- (H4)'s fresh `α ⊏ β` at each re-entry.

That re-entry choice is the printed freshness, applied once per resumption.

*Evidence* (F2).

- Option (b) has PROVED instances at [Core σ=[]], with today's stop:
  - resume of a 6.64 lend (`imm_spans_yield`);
  - resume of a 6.65 lend (`withbor_spans_yields_cC`);
  - drop or cancel of a 6.65 lend at a cancellable yield (`spans_two_affine_yields`,
    `withborR_compat`).

  The general borrower is reduced to `RelendOfTyped` (`Open.lean:45`), which is OPEN. GFP is
  refuted as first stated, by a witness that does not arise; `GFPA` is OPEN.
- The draft's first probe, cancel over a 6.64 frame, is not among the built instances. Neither is
  "resumed by a handler between two lenders". That case is OQ-3 and `AllCross`.
- TR §14.3 / §15 (capture rebasing; T14.5, T14.6) are PAPER-ONLY.
- The same-lifetime refold route is REFUTED. `refoldKripke_false` and `refold_fails_at_consumer_frame`
  (`experiments/LoopBorrow`) show this at a list that arises.
- Option (a) has no Lean.

*Needs the user?* No. It is a real unknown for tier 2 and can be deferred under tier 1 first.

### OQ-10. The form of the relativised stop

*Question.* What does the table receive at a stop: extra frames (a), or `ls'` only, with frames
re-derived (b)?

*Class.* **DUPLICATE of OQ-9.** Its (a) and (b) are OQ-9's (a) and (b) restated at the stop
clause.

*Evidence.* Under OQ-9 (b) the stop needs no change. The GhostEnd results in F2 are stated at
today's `Core/EffDefs.lean:40` clause. So a decision for (b) makes OQ-10 moot.

*Needs the user?* No.

### OQ-11. Are laws stated over `W`, or at `σ = []`?

*Question.* Over `W` (a), at `σ = []` with a survival lemma (b), or at `σ = []` only, marked (c)?

*Class.* **ANSWERED-ELSEWHERE.**

*Basis.* Critic correction 5 is signed off with the structure (2026-10-03, `effect-calculus-spec-first`;
00 §0.3 item 5): "Laws, graded algebraicity, `Sig` and renaming are stated over `W`, or shown to
live at `σ = []` and survive the re-index. Nothing is stated over today's `cC` alone." That is
the rule. What is left is per-law proof work, not a question.

*Needs the user?* No.

### OQ-12. Operations that take computations (higher-order and scoped effects)

*Question.* Does decision 57's exclusion stand (a)? Or are they brought in as parameterised
algebraic theories (b), latent effects (c) or hefty algebras (d)?

*Class.* **DECIDED (a)**, at the strength recorded.

*Decision.* Decision 57 (`docs/decisions.md:713`, "the user's decisions of 2026-10-01"):
"Operations that take computations (higher-order effects) are out of scope: scoping constructs are
functions over passed computations that install ordinary handlers." `docs/effect-polymorphism.md`
§11 item 6 has the same.

The words "out of scope" are the recording agent's, not a user quote. Per `not-now-is-not-never`,
read them as "not now". `docs/effect-polymorphism.md` §7 shows each scoping construct (`catch`,
`local`, `retry`, `timeout`, `finally`) as a function over a computation.

*Evidence.* None in Lean. PR #233's closing comment (2026-10-02) names higher-order *callbacks*
as the unmet goal ("callbacks taking callbacks, stored or returned callbacks, policies as values,
effectful codata"), not operations that take computations. That is OQ-13's ground.

*Needs the user?* No, unless they reopen it.

### OQ-13. Effect polymorphism: a meta-index or an object of the calculus

*Question.* Do rows stay a meta-index with per-row derivations (a)? Add a meta-level substitution
lemma (a')? Or add row and instance abstraction to the kernel (b)?

*Class.* **CONSTRAINED + EVIDENCED + GENUINELY OPEN.** It needs the user.

*Decisions.*

- Decision 57 (2026-10-01): "No row variables in the kernel (Option 2)" (`docs/decisions.md:707`).
  Its "Still open" list includes "whether to build the renaming lemma" (`docs/effect-polymorphism.md`
  §11). The draft's 01 §4 correctly reads it as a default, not a ban.
- Decision 8 ("Monomorphization, no type `∀` in the core") and decision 19 ("No judgment index
  'for later'") point the same way.
- On the other side:
  - U5, "need to work, full stop" (2026-09-30), requires the reconciler chain, whose `timeout` and
    `retry` are generic over rows.
  - `laws-first` (2026-10-02): "whatever we built, it isn't an effect algebra or we wouldn't be
    having these problems".
  - `deep-before-shallow` (2026-10-01): "what i want is a bunch of things falling like magic not
    something that half implements".

*Evidence.*

- **ATTEMPTED-FAILED.** PR #233 (`effect-callbacks` c321bd2) built decision 57's ports for
  effectful callbacks. It was closed unmerged on 2026-10-02 with the comment: "It solves the
  first-order case only, and the higher-order cases (callbacks taking callbacks, stored or returned
  callbacks, policies as values, effectful codata) were left pending behind workarounds. The goal
  was the general form." The comment was posted from the user's account. These are exactly the
  cases that the draft's default R-NOROWVAR excludes.
- The TR's calculus has row abstraction (TR D1.5-D1.7, `docs/effects-tr/01-syntax.md`) at
  [EffModelRel].

*Needs the user?* Yes. It is a real unknown. A first-order kernel is a fragment of (b), so the
first kernel lift can proceed under (a). The choice is needed before higher-order callback work.

### OQ-14. Static names or generative instances

*Question.* Static names per site (a), or generative instances with a scope-confined `κ` (b)?

*Class.* **CONSTRAINED, default (a).** MIS-cited (F3). Deferrable.

*Decisions.* Decision 57 item (`docs/decisions.md:711`, 2026-10-01): "Recursion through a site
whose callback tunnels that site is rejected for now… #173 (generative labels) is raised only if
the pattern bites." Decision 59 (`:744`ff, "Not built") lists "recursion through a site
(decision 57's parser: a site per level, L2, #173)". The strength is "for now" and "only if the
pattern bites".

*Evidence.*

- Staton's ν laws are PROVED at [EffModelRel] (T7.12-T7.14).
- ν/op is REFUTED at a multi-shot operation (`nu_op_fails_multishot`,
  `experiments/EffModelRel/EffModelRel/Examples.lean:223`) [EffModelRel].
- The scope confinement that (b) needs is #173 / T2, the outlives rule at `U C`. It is open, and
  `thunk_not_outlives` (`experiments/CoeffectsStrict/CoeffectsStrict/Context.lean:111`) is PROVED.

*Needs the user?* Only if the pattern bites.

### OQ-15. The kernel reading of divergence

*Question.* Codata, `U(Loop B R)` with handlers per observation (a), or div as a row entry read by
partial correctness (b)?

*Class.* **DECIDED (a).**

*Decisions.*

- Decision 35 (`docs/decisions.md:174`, not marked provisional): "A div function returns a loop,
  `A ⇒ U(Loop B R)`".
- `div-is-an-effect`: "Core reading: a div function's result is the delay/`Loop` computation type."
- `no-effect-ish-approximations` (2026-09-28): "Div is not an algebraic effect; it stays
  codata/delay, and nobody should pretend it is handled."
- Decision 58 (2026-10-01): "Partial correctness and refunctionalising a heap machine in the
  backend were considered and not taken" (`docs/decisions.md:731`, for `bounded_fix`).

The user's own quoted words are only "Div should be an effect". The codata reading is the
recorders' phrasing, but it has been repeated in three records and never corrected.

The handler around a div computation was parked by the user. `docs/handlers-over-div.md`
@ `loophandle` 51772c1 says: "Parked by the user before any Lean or probe was written: handlers
around loops are not a priority, since the operator's shape (a generator pipeline with a handler
per iteration) already works." Its general form uses only existing rules [inspection].

*Needs the user?* No: the user has corrected the reading (above). Whether the spanning handler
(K-HDIV) is lifted is OQ-67, outside this file. That depends on how the 10-01 parking sits with U5 "full stop" (09-30).

### OQ-16. Is multi-shot free?

*Question.* Keep `unr` with no law depending on it (a), or drop it (b)?

*Class.* **DECIDED (the criterion).** The fact is settleable by census.

*Decision.* `multishot-only-if-free` (2026-10-02): "we also don't need multishot unless we get it
for free"; "it's worth pursuing why we can't have multishot, but it's not a blocker". The strength
is a priority call, not a ban. `effect-handling-is-erased` (2026-09-30): multi-shot is "not
erasable; excluded, or an explicit opt-in with a visible cost".

*Evidence.*

- `nu_op_fails_multishot` is REFUTED at [EffModelRel]. In that sibling calculus it is a
  closed-program `CtxEq`.
- The kernel carries `unr` in `kTy` (`Core/EffRules.lean:976-980`), `contShare`
  (`Core/EffDefs.lean:144`) and `S.Unr → Ctx.Banged Γ₂` (`Core/Fundamental.lean:354, 361`).
- TR §10.3 is a phase-A counterexample at a relevant qualifier.

*Needs the user?* No. The census is off the critical path, as the record says.

### OQ-17. The relevant qualifier

*Question.* Not provided (a), or a graded `!` with grade `[1,∞]` (b)?

*Class.* **MOOT.**

*Basis.* No program needs it. The draft's own trigger is "when a program needs it". Decision 55's
qualifiers are `ctl`, `linear ctl` and `multi ctl`, with no relevant one. Its only appearance is
phase A's `Again` counterexample (TR §10.3), which was fixed by scaling, not by adding the
qualifier.

*Needs the user?* No.

### OQ-18. Sum, tensor, and threads

*Question.* Rows as sums, disjoint capabilities as tensor, cancel uninterceptable (a), or another
combination (b)? And how do thread boundaries combine rows?

*Class.* **CONSTRAINED + ANSWERED-ELSEWHERE (in part).**

*Basis.*

- "Rows as sums" is in the signed-off structure (2026-10-03).
- Cancel is uninterceptable by user decision (#186 comment, 2026-09-30; `errors-are-control-flow-effect`).
- Threads: `threads-are-required` (2026-09-29): "we obviously need them", "just not now"; "avoid
  choices that close the door".

*Evidence.* The tensor law is PROVED only at [EffModelRel] (T7.8).

*Needs the user?* Not now. The literature check for thread boundaries is deferrable.

### OQ-19. The meaning of "comodel" for a capability

*Question.* State-access semantics only (a), or runners with finalisation (b)?

*Class.* **DECIDED (a).**

*Decision.* `effects-are-core` (2026-09-30): "Runners (Ahman & Bauer) are OUT: the user considers
them a dead end; don't pursue them unless something leads there." The 2026-10-02 revisit keeps
them out "as the user-facing effect mechanism", while the BoLo-world-as-runner architecture stays
"not yet decided" (OQ-34). The strength is "out unless something leads there".

*Note.* The TR already gives failing co-operations a runner-like exit without a runner construct:
"fail to the lend" (TR §8.2, `docs/effects-tr/08-decisions.md:82`, an agent-recorded TR decision).
It is implemented in phase B (`coRes`, `Syntax.lean:172`; `runL_rel`, `Compat.lean:578`)
[EffModelRel].

*Needs the user?* No.

### OQ-20. A co-operation whose callee performs

*Question.* Pure `withswap` only (a), a `withtake`-shaped constant (b), or an effectful `withswap`
under `TableOK` (c)?

*Class.* **MIS-POSED (in part) + ANSWERED-ELSEWHERE (the fallible case) + GENUINELY OPEN (the
effectful case).**

*Basis.*

- The draft motivates this question by the reconciler's fallible `Kube`, but omits TR §8.2. TR
  §8.2 already decided the fallible case: option (b), "a co-operation answers
  `(B_o ⊗ S) ⊕ (E_o ⊗ S)`… On failure… the lend answers the capability with `inr e`", only at
  operations that admit weakening. It is PROVED at [EffModelRel] (`runL_rel`, `lent_state_survives`).
  TR §8.2 leaves only option (d), "a co-operation perform[ing] control operations of the context",
  as open: "the dual of T1 (§9.3)… not taken up".
- The `withtake` source is mis-cited (F3): it is #251's comment of 2026-10-02T16:10Z, not #279.

*Needs the user?* The fallible case needs no new decision beyond carrying TR §8.2 to the kernel,
which is a proof. The effectful-callee case is settleable by proof first. It is tier-2-like and can
be deferred.

### OQ-21. What a finaliser may perform, and the cancel error policy

*Question.* Keep as built (a), or restrict destructors to answering operations (b)?

*Class.* **MIS-POSED.** Its option (a), "as built", conflicts with the recorded decision (F4).

*Decision.* The user decision recorded on #186 (2026-09-30T23:00Z): "Cancellation is not
interceptable… A finaliser's raise under a cancel becomes a suppressed error, and unwinding
continues to the canceller, which always receives 'cancelled'." The kernel (SPEC §19,
`SPEC.md:2509-2515`; `Core/EffCancel.lean` `prog₃`) re-raises the first error of a name outside
the region at the canceller.

Option (b) comes from #245's brief of 2026-10-02 ("Destructors may perform only answering
operations; handler-level finalisers may perform anything in the outer row… decide them
deliberately"). That is an agent consolidation, not a user decision.

*Needs the user?* Yes. They need to settle the discrepancy between the record and the build. This
is not a proof question.

### OQ-22. Equations in a signature

*Question.* Optional equations in `Sig`, with L-HCORR an obligation (a), or free theories only
(b)?

*Class.* **CONSTRAINED, toward (a) as the form.**

*Decisions.*

- `laws-first` (2026-10-02) asks for "theory-specific laws (exceptions, state and linearly used
  state, nondeterminism, generators)". That needs equations to be writable, which excludes (b).
- U22 (2026-10-02) makes their kernel binary proofs "optional … unless necessary for safety".

The draft's default, "the form; no kernel theory carries equations until needed", satisfies both.

*Needs the user?* No.

### OQ-23. Is lowering correctness a theorem?

*Question.* Per-class laws plus corpus counts and reports (a), or a compiler-correctness theorem
for the effect lowering (b)?

*Class.* **CONSTRAINED + GENUINELY OPEN.** It needs the user and can be deferred.

*Decisions.*

- `effect-handling-is-erased` (2026-09-30), at first: "Acceptance: an erasure theorem, plus corpus
  counts."
- Decision 48 then revised it to per-class laws, counts and reports, "in place of 'an erasure
  theorem', which elaboration makes true by definition" (`docs/decisions.md:608-610`).
- `effects-are-core` (2026-09-30) supersedes decision 48's elaboration. That removes the premise
  ("true by definition") on which the revision rested.
- `language-purpose` (2026-09-24): "verified foundations in wasm"; "Verified path: core → Wasm".
- The criterion, cost parity, is decided (U6).

*Needs the user?* Yes. The premise of the current acceptance is gone, and only the user can say
whether to restore the theorem. It is not on the kernel path.

### OQ-24. An abortive payload that owns a resource

*Question.* A `NoOwn` payload (a), or a linear payload delivered after the unwound region's
finalisers have run (b)?

*Class.* **CONSTRAINED toward (b) + GENUINELY OPEN (proof).** Deferrable.

*Decisions.*

- Decision 55 (2026-10-01, provisional): "`from_utf8` raises the index and drops the buffer,
  provisionally: the error should hand the buffer back once an abortive payload may be linear
  (#215)" (`docs/decisions.md:691`).
- `errors-are-control-flow-effect` (2026-09-30) excludes a value-level error path. That rules out
  returning the buffer through a sum.
- #215 (open) states (b) as "a hypothesis to verify, not settled".

*Evidence.* None in Lean.

*Needs the user?* No, beyond the recorded intent. It is a proof obligation, and close to mechanical
by #215's analysis (not verified).

### OQ-25. Handler state

*Question.* State passing (a), or comodel state in a `Mut` cell lent to the body (b)?

*Class.* **DECIDED (a) as current; (b) is tier-2 only.**

*Decisions.* Decision 59 (`docs/decisions.md:761-765`, "the user's decisions of 2026-10-01 after
the second-class spike"): "A handler whose operations resume has a state, its parameters that are
not `!` and the capabilities its clauses use, passed to each clause and at each resume."

Option (b) appears in #245's 2026-10-02 brief: "All handler state is comodel state… This is the
route to … T1 as a theorem". That is an agent brief, tied to tier 2 and TR §15 (PAPER-ONLY,
T14.5).

*Needs the user?* No for tier 1. Only if tier 2 pursues (b).

### OQ-26. Shallow handlers

*Question.* `ν` only (a), or a shallow handler construct (b)?

*Class.* **ANSWERED-ELSEWHERE (a) + MOOT (b).**

*Basis.* Decision 15 (`docs/decisions.md:37`): "Shallow handlers are primitive; deep handlers are
derived. A suspended computation is codata; one observation is a shallow handler". That is
option (a)'s reading.

`compiler-never-stale` prefers designs "whose lowering is known up front (e.g. shallow handlers as
state machines…)". (b) is triggered only "when a program needs it", and none does.

*Needs the user?* No.

### OQ-27. η with cancel at a cancellable operation

*Question.* Is the cancel-forwarding term `let r = op x in resume k r` typable, so that L-ETA is a
law to prove?

*Class.* **MOOT (the law) + detail (the term).** Mis-cited (F3).

*Basis.*

- U22 (2026-10-02) names "η as an equation" among the optional kernel equations. So L-ETA's
  binary law is not pursued unless needed for safety.
- Whether the forwarding term types is a statics question, settleable by trying the term in
  `CDerives`. The draft itself ties it to OQ-7 (04 §7.6).
- Source: #251's comment (2026-10-02T16:10Z), not #279.

*Needs the user?* No.

### OQ-28. How a stored continuation is bounded

*Question.* `[gen]` as a rule with `κ` at `[@c] U(Clo^c A B)` (a), or an outlives rule at `U C`,
so that `[gen]` is derived (b)?

*Class.* **EVIDENCED + ATTEMPTED + GENUINELY OPEN (proof).** Its option (b) is #173 / T2 (F3).

*Evidence.*

- `box_lolli_outlives_iff` (`experiments/HandlersControl/HandlersControl/Outlives.lean:35`) is
  PROVED at [paper].
- `thunk_not_outlives` (CoeffectsStrict) is PROVED. `U C` has no outlives rule.
- TR T14.4 and T14.6 are PAPER-ONLY.
- **ATTEMPTED, stopped.** `lift-stage1` c9b3694 (`Core/Gen.lean`, "WIP (#274, not for merge)").
  Its commit message: "genE, Qgen (D14.4), L14.3 (ewp_gen) build; T14.4, T14.6 and the `CDerives`
  rule not written. Not imported by Core.lean." There is no `sorry`. It would be [Core σ=[]]
  under T1.
- `docs/effects-tr/16-regress.md` §16.6 (i) lists `[gen]` among what tier 1 still has to prove.

*Needs the user?* No. It is a tier-1 item. The one non-mechanical step named is T14.4's
coinduction (`clo_coind`).

### OQ-29. An operation that answers a borrow into the handler's state

*Question.* Not provided (a), or K-BORANS: an answer `Imm 'h T` at the handler's extent (b)?

*Class.* **CONSTRAINED (it needs OQ-3 (a) and the 6.150 lift) + GENUINELY OPEN.** Deferrable.

*Basis.*

- Decision 48's staging put projections at S4 (#160, open). Theory index T21 says the derived type
  of the projection form "has not been established". Decision 48's elaboration premise is
  superseded.
- [TR] Theorem 6.150 (↺ rule) is printed over `wp` (`3764117-supplement.pdf`, text line 2087). Its
  lift to a resuming table is on the frozen tier-2 list (`hard-stop-on-regress`). The view-copy
  part is in `GhostEnd/Frames.lean` (`ptoImm_dup`).

*Needs the user?* After a proof. Tier 2, so it can be deferred.

### OQ-30. Allocation and I/O in the calculus: which presentation

*Question.* Allocation as operations of `Alloc[T]` in rows (b), or as a capability that colours no
function type (b')?

*Class.* **CONSTRAINED toward (b) + MIS-POSED (in its framing).**

*Decisions.*

- `alloc-is-an-effect` (2026-09-28; the user's correction "alloc _is_ an effect, we already talked
  about that"): "The heap is the outermost linear State handler, and arenas are nested handlers.
  Tracking it in function types (inferred like div, with an assertion like `total`) is the
  not-yet-built part." That is a row-style presentation, inferred like div, which is (b).
- The draft's default (b') is justified by U7 colouring. By F1, an inferred effect in the type is
  not colouring in the user's sense: decision 35 says so for div, which (b) mirrors.
- `no-traits` (2026-10-01, tentative) treats `Num[T]` operators the same way: "an ambient,
  outermost platform handler… like alloc".

*Needs the user?* Light confirmation. The record already describes (b). The proof obligations are
OQ-68, outside this file.

### OQ-31. The cut-offs that keep the relation step-free

*Question.* Keep all five cut-offs of TR §16.5 (a), or relax one with step-indexing (b)?

*Class.* **DECIDED (a).**

*Decision.*

- Decision 7 (`docs/decisions.md:19`, not provisional): "Recursion without step-indexing."
- Decision 1: the paper's model "proves safety, leak freedom and termination without
  step-indexing".
- The draft's 00 §0.2 item 2 ("No step-indexing") carries it.

*Evidence.*

- `no_negative_domain` (`experiments/EffModelRel/EffModelRel/Obstruction.lean`) [EffModelRel].
- `no_uniform_comp` (`HandlersControl/Behind.lean:53`) [paper].
- `no_nonstrict_stratum` (`experiments/Outlives`).
- TR §16.5's fifth row ("the relation stored in the world") is "prose only" (`docs/effects-tr/16-regress.md` §16.5, table).

*Needs the user?* No. The cost falls on the deep-handler scheduler (OQ-60, outside this file).

### OQ-32. The TR's moded calculus and the kernel

*Question.* For each TR rule fix, record which kernel rule refuses the TR's counterexample (a), or
lift modes into the statics (b).

*Class.* **GENUINELY OPEN, a detail.** Settleable by reading and by configurations. The premise is
partly mis-posed.

*Basis.* The three fixes (TR §10.1-§10.3) repair phase A's checker in `experiments/EffModel`, not
`CDerives`. For two of them the kernel already has the corresponding rule [read, not checked
against a configuration]:

- §10.1: the lend consumes and answers its capability. That is BoLo's `withbor` shape, which the
  kernel's borrows already have.
- §10.3: the return clause run twice under a contractible operation. The kernel asks
  `S.Unr → Ctx.Banged Γ₂` (`Core/Fundamental.lean:354, 361`) and `contShare`'s `ρ = ∅` at `unr`
  (`Core/EffDefs.lean:144`).

The draft's "`CDerives` has no modes" overlooks those qualifiers. §10.2 (the frame-owned `Res`) has
no kernel counterpart named yet.

*Needs the user?* No.

### OQ-33. How the hard-stop rule applies under this specification

*Question.* Does the hard stop apply to the milestone that lifts R-T1 (a)? Is it superseded by the
register (b)? Under either, the "once for every depth" refinement stands (c).

*Class.* **CONSTRAINED + GENUINELY OPEN.** It needs the user.

*Decisions.*

- `hard-stop-on-regress` (2026-10-02): "My concern is going to be that one of that finite lists
  itself has a regress so we should make that a hard stop"; refinement: "If the new work is n+1
  and we are done, it's fine. If it's 3 and then 4 and then 5, no." Option (c) is the refinement
  and is already recorded.
- The signed-off critic correction (00 §0.3 item 2) says tier 2 did not halt by rule.
- `structure-before-briefs` (2026-10-03): "A new relation family, twin constant or side mechanism
  is a stop-and-report, never a deliverable."
- `no-issues-for-open-questions` (2026-10-03): open questions stay boxed and are never issues.

So (b)'s "the user decides at each one" is consistent with the 10-03 records. Whether the original
"tier 2 halts, ship tier 1" trigger still operates is not recorded.

*Needs the user?* Yes. This is a process decision.

### OQ-34. Is the BoLo world itself a comodel (the heap-runner architecture)?

*Question.* Not adopted as structure (a), or adopted as the reading of K-HOST and allocation (b)?

*Class.* **ANSWERED-ELSEWHERE.** The user explicitly left it open.

*Basis.* `effects-are-core` (2026-10-02) records the user calling it "kind of genius… a calculus
of everything you can do inside of a runner", "promising, not yet decided"; "Don't cite 'runners
are a dead end' against it." The draft's (a), "neither depended on nor excluded", records that
status exactly. The PLDI 2022 boundary paper is named in the record, not read.

*Needs the user?* No decision is needed now. It is the user's open idea, not a blocker.

---

## Summary

| OQ | class | one-line basis | needs user? |
|---|---|---|---|
| 1 | CONSTRAINED + EVIDENCED + MIS-POSED (framing) | the sign-off excludes (c); the user frames answering/suspending as one mechanism's op kind; HandlersAsBorrows [paper]; "colouring" misread (F1) | proof first; light confirmation |
| 2 | DECIDED (a) | "Stage 1 … at tier 1 … proceeds regardless" (10-02); tier 2 in scope ("including stored continuations holding borrows") | no (the residual is OQ-33) |
| 3 | EVIDENCED + OPEN | GhostEnd's route needs a handler extent (README step 1); `AllCross` discharged only at `true`; #278 | no; tier 2, defer |
| 4 | DECIDED | U22: kernel equations "optional … unless … necessary for safety" (10-02) | no |
| 5 | CONSTRAINED → (a) | "Laws: validated on the model (phase B)" (10-02) | confirm only |
| 6 | OPEN (surface) | shape recognition as built (decisions 56, 58); a one-way door | yes, later |
| 7 | EVIDENCED + CONSTRAINED + OPEN | `withborR_compat` lifts the unwinding borrow to a resuming row [Core σ=[]]; O2 paper-only | after proof; resuming half is tier 2 |
| 8 | EVIDENCED + OPEN | `not_gfp` (non-arising witness), `GFPA` open, `vRLk` with no `_nil`; critic 3 says Lean, not prose | no; tier 2, defer |
| 9 | EVIDENCED + OPEN | option (b) PROVED on instances at today's stop (F2); general `RelendOfTyped`/`GFPA` open; option (a) no Lean | no; tier 2, defer |
| 10 | DUPLICATE (OQ-9) | options mirror OQ-9; under (b) the stop is unchanged | no |
| 11 | ANSWERED-ELSEWHERE | signed-off critic correction 5 (00 §0.3 item 5) | no |
| 12 | DECIDED (a) | decision 57: higher-order ops "out of scope" (10-01; read as not now) | no |
| 13 | CONSTRAINED + EVIDENCED + OPEN | decision 57 Option 2 vs PR #233 closed for leaving higher-order callbacks pending (10-02); laws-first | yes; may follow the first lift |
| 14 | CONSTRAINED (a) | "rejected for now… only if the pattern bites" (decision 57); #173 mis-cited (F3) | only if the pattern bites |
| 15 | DECIDED (a) | decision 35; "Div … stays codata/delay"; handlers-over-div parked by the user | no |
| 16 | DECIDED (criterion) | "don't need multishot unless we get it for free" (10-02); census is a side question | no |
| 17 | MOOT | no program needs a relevant `κ`; no qualifier in decision 55 | no |
| 18 | CONSTRAINED + ANSWERED (part) | rows as sums signed off; cancel uninterceptable; threads "later" | no, not now |
| 19 | DECIDED (a) | "Runners… are OUT" as user-facing (09-30, 10-02) | no |
| 20 | MIS-POSED (part) + ANSWERED (fallible) + OPEN (effectful) | TR §8.2 "fail to the lend" omitted; proved at [EffModelRel]; `withtake` from #251 not #279 | no; proof first, defer |
| 21 | MIS-POSED | "as built" contradicts the #186 decision "always receives 'cancelled'" (F4) | yes: settle the discrepancy |
| 22 | CONSTRAINED → (a) form | laws-first wants theory laws; U22 makes binary proofs optional | no |
| 23 | CONSTRAINED + OPEN | decision 48's acceptance rested on elaboration, superseded; "verified path: core → Wasm" | yes; defer |
| 24 | CONSTRAINED → (b) + OPEN (proof) | decision 55 "should hand the buffer back… (#215)"; no value-level error path | no; proof |
| 25 | DECIDED (a) | decision 59: state "passed to each clause and at each resume" (10-01) | no (tier 1) |
| 26 | ANSWERED-ELSEWHERE + MOOT | decision 15: "one observation is a shallow handler" | no |
| 27 | MOOT (law) + detail | U22 names "η as an equation" optional; the term is a typing check; #251 not #279 | no |
| 28 | EVIDENCED + ATTEMPTED + OPEN | `lift-stage1` `[gen]` WIP stopped (T14.4/T14.6 unwritten); (b) is #173 | no; tier-1 proof |
| 29 | CONSTRAINED + OPEN | needs OQ-3 (a) and the 6.150 lift (frozen tier-2 list); #160 | after proof; defer |
| 30 | CONSTRAINED → (b) + MIS-POSED (framing) | "Tracking it in function types (inferred like div…)"; F1 | light confirmation |
| 31 | DECIDED (a) | decision 7 "Recursion without step-indexing"; decision 1 | no |
| 32 | OPEN (detail) | fixes target phase A's checker; kernel qualifiers already refuse §10.1/§10.3 [read] | no |
| 33 | CONSTRAINED + OPEN | hard stop + refinement (10-02); structure-before-briefs (10-03); critic 2 | yes |
| 34 | ANSWERED-ELSEWHERE | user: "promising, not yet decided"; (a) records that | no |

**Questions that need the user now:** OQ-13, OQ-21 and OQ-33. OQ-6 and OQ-23 need the user later,
since neither is on the kernel path. OQ-1, OQ-5 and OQ-30 need at most a confirmation.

**Real unknowns settleable by proof:** OQ-1 (tier 1), OQ-28 (tier 1), OQ-9/OQ-8/OQ-3 (tier 2;
can be deferred if tier 1 comes first), and OQ-7's resuming half.

**What this file did not do.**

- It did not check the draft's spec sections (02-08) beyond the lines the OQs cite.
- It did not read the PLDI 2022, Affect, Lindley et al. or hefty-algebra sources.
- It did not build any Lean.

OQ-35 to OQ-68 are outside this file. Some entries above refer to OQ-58, OQ-60, OQ-67 and OQ-68
only to say where a residue goes.

## Sources read

- `~/repos/borrow-core-effects-spec/docs/effects-calculus/99-open-questions.md` (all of OQ-1 to
  OQ-35); `00-structure.md` §0.2-§0.3; `01-scope.md` §4-§5.
- `docs/effects-audit.md` @ `effects-audit` (§1 header, §7).
- `docs/decisions.md` entries 1-61 (in particular 7, 8, 15, 19, 35, 48, 55-59).
- `SPEC.md` §19 *Cancels* (`:2493-2520`).
- `docs/effects-tr/README.md`, `08-decisions.md`, `10-findings.md`, `16-regress.md` §16.5-§16.6;
  section headers of `09-factoring.md` and `14-stored-continuations.md`.
- `docs/effect-polymorphism.md` §7, §11; `docs/theory-index.md` T2 (`:657, :700-718`);
  `docs/handlers-over-div.md` @ `loophandle`.
- `Core/EffDefs.lean:25-45, 130-170`; `Core/EffBorrow.lean:128-136`; `Core/Fundamental.lean:350-375`;
  `Core/EffRules.lean:975-985`; `Frontend/Elab/Effects.lean:229, 240`.
- `experiments/GhostEnd/README.md` (main and `borrow-callbacks`); `GhostEnd/{Program,Drop,ImmLend,StackStep,Stacked}.lean`;
  `Below.lean` @ `gfp`; `Arising.lean` @ `gfp-arising`; `Extend.lean` @ `borrow-callbacks`.
- `Core/Gen.lean` @ `lift-stage1` and its commit message.
- `experiments/HandlersAsBorrows/README.md`; `experiments/HandlersControl/README.md`;
  `experiments/TwoRun/README.md`; `experiments/EffModelRel/README.md`; `experiments/README.md`
  (LoopBorrow row).
- [TR] `3764117-supplement.pdf`: statements of Lemma 6.62, Theorems 6.64, 6.65, 6.66 and 6.150,
  and Lemma 6.147 (`pdftotext` lines 1143-1385, 2055, 2087).
- GitHub:
  - #290 (body);
  - #288 (body and synthesis comment);
  - PR #289 (body);
  - PR #233 (closing comment);
  - #186 (decision comment of 2026-09-30T23:00Z);
  - PR #191 (body);
  - #173, #160, #215, #278 and #279 (bodies and recent comments);
  - #251 (comments of 2026-10-02);
  - #245 (comments of 2026-10-02);
  - titles of #235, #247 and #255.
- Memory records:
  - `effects-are-core`, `effect-calculus-spec-first`, `hard-stop-on-regress`;
  - `multishot-only-if-free`, `no-function-coloring`, `lead-axis-no-coloring`;
  - `effect-handling-is-erased`, `alloc-is-an-effect`, `div-is-an-effect`;
  - `threads-are-required`, `laws-first`, `no-effect-ish-approximations`;
  - `structured-recursion-only`, `no-surface-monads`, `io-is-a-bundle-of-effects`;
  - `errors-are-control-flow-effect`, `mechanism-before-syntax`, `syntax-choices-not-blocking`;
  - `no-magic-comments`, `trust-not-assurance-ceremony`, `portable-lowerings`;
  - `compiler-never-stale`, `zero-cost-target`, `no-traits`;
  - `no-issues-for-open-questions`, `structure-before-briefs`, `unknowns-first`;
  - `deep-before-shallow`, `not-now-is-not-never`, `current-state-is-not-design`;
  - `own-names-not-rust`, `defaults-not-prohibitions`, `language-purpose`.
