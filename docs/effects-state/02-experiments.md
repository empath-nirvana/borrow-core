# Effects experiments: goals, results, status

Part of the effects state-of-play inventory (#290). This file records what each experiment that
touches effects, handlers, continuations or suspension set out to do, what it proved, what it
refuted and what it left open. It also records the world each result lives at and how the
result relates to the kernel (`Core/`).

It is an inventory, not a plan.

**Baseline.**
- borrow-core `main` = `origin/main` = `8a1c326` (2026-10-02). Line numbers are at `8a1c326`
  unless a branch commit is named.
- Status words follow the brief: PROVED, REFUTED, PAPER-ONLY, ATTEMPTED-FAILED,
  REJECTED / ABANDONED, OPEN.
- "Stated" means a `def … : Prop` goal that elaborates and has no proof.

**Hygiene, checked by grep.**
- No file under `experiments/` on `main` contains `sorry`, `axiom` or `admit` except inside
  comments.
- Every unproved step is a named `Prop` goal. These goals are listed under OPEN.
- Nothing was built for this inventory. Build status is taken from the READMEs, except where
  noted under FrameTheorems and TwoRun.

## 0. Worlds, and why they matter

A result proved at one of these worlds is not a result at another. None of the results below is
at the planned Kripke world W.

| tag | world | where defined |
|---|---|---|
| **K** | The kernel at the empty lend stack (σ = []): `wpG`, `ewpTS` at `opTable`, `wpTS`, `TW`, `vC`/`cC`, `CDerives`, `fundamentalC`, `adequacyC`. `wpG` requires every stop to have closed the 6.64 frames and reborrow records it opened, and that is where T1 comes from. | `Core/EffDefs.lean:27` (`wpG`), `:73` (`ewpTS`), `:157` (`opTable`); `Core/World.lean:186` (`wpTS`) |
| **K-pure** | K without effect rows: plain `wpTS`/`CDerives` from before SPEC §19. | `Core/World.lean` |
| **G1** | GhostEnd's single-lend objects, built over K without changing it: `Relend`, `Open`, `OpenD`, `RBody`/`RBodyT`/`RBodyC`, `TV`, `CloL`, `TabAt`, `NestRelend`, `opTableO`. | `experiments/GhostEnd` |
| **vRL / vRLg** | GhostEnd's single-lend re-lendable relation, and its table-guarded form. | `RLCompat.lean:221`, `:508` |
| **vRLs** | D16.1, the lend-stack-indexed relation. `vRLs_nil` shows it equals K at σ = []. | `Stacked.lean:237` |
| **vRLa** | D16.1 guarded at `U`, `⊸` and `∀`. | `Arising.lean:173` @ `d31cbb3` (branch) |
| **vRLk** | vRLa with the `∀` clause read at every extension of the stack. | `Extend.lean:62` @ `5cfe062` (branch) |
| **PAPER** | The BoLo paper layer: `DerivesWf` + `!`, `SemX`, with angelic adequacy (some run reaches the value). | `Paper/`, `Support/` |
| **PAPER-carrier** | The paper's resource carrier, `vDen` / paper `wp`. | `Support/` |
| **SIB** | The sibling calculus of #235: intrinsically typed, denoted into finite trees, with no resources and no machine. Its binary relation's contexts are unmoded. | `experiments/EffModelRel` |
| **TW-old** | The typed worlds of CBPVWorld, CBPVMu, Relaxed and FrameEnd, which Core was assembled from. | those experiments |

`origin/effects-audit` (`6db9b86`, PR #289, open, unmerged) has a table of the same settings
(`docs/effects-audit.md:118–129` @ `6db9b86`). It labels K "the one relation of record",
EffModelRel "S2–S4 … none [relation to the kernel]", and GhostEnd "S6 … wraps K's `vC`; equal at
σ = [] only by `propext` (and not shown for `vRLk`)". It also says: "Every algebraic law in the
project is proved in S2. All of the GhostEnd and stacked Lean is in S6. Only K carries a
fundamental property over `CDerives`." These are the audit's findings. Nobody has decided on
them.

---

## 1. GhostEnd (`experiments/GhostEnd`)

### 1.1 Overview

**Issues and PRs.** All on 2026-10-02 or 2026-10-03.

| issue | title (abridged) | state | PR(s) |
|---|---|---|---|
| #258 | Ghost-end lemma: end internal Mut borrows at freeze, re-lend fresh at resume (closes O15.1 with naturality) | closed | #259 merged |
| #260 | Ghost-end, general case: typed borrowers, drop at affine yields, 6.64/6.66/6.150 at resuming tables, nested lends | closed | #261 merged |
| #262 | values carrying a lend across a suspension | closed | #263 merged |
| #264 | KernelInvariant from TW preservation; bridge vs re-lendable-by-construction relation | closed | #265 merged |
| #266 | Feasibility: fundamental lemma at vRL/cRL (route b) | closed | #267 merged |
| #268 | Last unknowns before the lift: `'x` in a payload; Imm lends spanning a stop; nested lends spanning a stop | closed | #273, #281 merged |
| #279 | Tier 2: D16.1 in Lean, with GFP | open (closed in favour of #290's plan, then reopened when that plan was withdrawn) | #282, #283 merged; #284, #285 open |
| #286 | Theory: borrow callbacks | open | #287 open |
| #275, #276, #277, #278, #280 | the frozen tier-2 list | open | none |

**Goal.** #258's motivation is Restrat's `mut_not_natural`: "the repair found is a condition on
the cell: it was ended at freeze and is re-lent afresh at resume". #258 set five targets:
1. admissibility;
2. freeze and resume;
3. O15.1, a lend spanning a suspension;
4. `wp` naturality restricted to the frozen state;
5. whether `mut_not_natural`'s witness arises.

**Method.** The method chosen (README:3–8) is "re-derive, don't transport … No `wp` naturality is
used, and neither is any naturality from `Restrat`." Target 4 was therefore not pursued.

**World.**
- Every file on `main` states its results at K's own definitions (`ewpTS` at a resuming
  `opTable`, `wpG`, `vC`, `cC`, `CDerives`), plus new least-fixed-point predicates (G1) over
  them.
- The headline results are semantic facts in K's `cC`, not typing rules: `withbor_spans_yields_cC`
  and `withbor_of_rbody`.
- README:547 says the resuming `withbor` is "O15.1's rule, not yet in `CDerives`".

**Relation to the kernel.**
- Nothing in `Core/`, `SPEC.md`, `docs/decisions.md` or `docs/adjudications.md` references
  GhostEnd. The only mention is the non-default library entry in `lakefile.toml:174–176`.
- GhostEnd imports Core and Restrat (`Witness.lean`).
- `docs/effects-tr/16-regress.md` §16.8 says restriction (i) (T1: no internal lend spans a
  suspension) "is already the kernel's rule" and "deletes `experiments/GhostEnd` from the lift".
- #274 (kernel lift, stage 1, open) keeps T1. It names GhostEnd as a source, but its kernel
  changes 1–8 use none of GhostEnd's relations.
- The effects audit recommends (`docs/effects-audit.md:262–282` @ `6db9b86`):
  - **promote** `ewpTS_M_frameR`, `ewpTS_I_frameR`, `ewpTS_M_antiFrameR`, `OpenS`/`bodyS`/
    `stopS`/`ghostS`, `stack_step_*`, `RelendableS/N`, `wpG_tabAt`, the `Payload.lean` facts and
    `TabAtS`;
  - **retire** `vRL`/`vRLg`/`vRLs`/`vRLa`/`vRLk` and steps 2–3f (`Open`, `RBody*`, `FrameThaws(D)`,
    `StopSafe`, `TV/TVG`, `KernelInvariant`, `O151AsStated`, `CloL`, `KapRelR`, `URelend`,
    `RelendableG`);
  - "**do not merge under a `not_` name**" `not_gfp`.

  This is a recommendation on an open PR, not a decision.

**User decision governing this line.** Recorded in memory `hard-stop-on-regress.md`, 2026-10-02:
- "My concern is going to be that one of that finite lists itself has a regress so we should make
  that a hard stop."
- Refinement, the same day: "If the new work is n+1 and we are done, it's fine. If it's 3 and then
  4 and then 5, no."

The memory file then sets these rules:
- The tier-2 list (#275–#280) is frozen.
- A new unknown halts tier 2, and "the language ships at tier 1: T1 kept … GhostEnd banked".
- "Stage 1 of the kernel lift … doesn't depend on this list and proceeds regardless."

### 1.2 Per file on `main` (all in `experiments/GhostEnd/GhostEnd/`)

Unless stated otherwise, each file has no refutation and no consumer in `Core/`.

**Segment.lean** (#258, PR #259)
- Goal: "the fundamental lemma for a stack segment with a hole".
- PROVED: `segment_fundamental` :30, a restatement proved from `fundamentalC` (README:74).
- World: K.

**Relend.lean** (#258)
- Goal: [TR] 6.65 at a resuming table, re-applied at each resumption.
- PROVED: `ewpTS_M_frameR` :117, by induction on the least fixed point `Relend` :57. Also
  `relend_fold` :91, `relend_unfold` :97 and `relend_step` :104.
- World: K + G1.
- The audit marks `ewpTS_M_frameR` "promote".

**Freeze.lean** (#258)
- PROVED: `noOwn_ptoMutS` :42, `freeze_at` :50, `wpG_box` :57 (6.147 at `wpG`) and
  `frozen_above_extent` :67.
- OPEN: the hypothesis that the handler body starts in `Res_h`. The kernel "does not establish it
  today, because handlers open no lifetime" (README:110–113). #274 item 3 proposes extent
  lifetimes to supply it.
- World: K (`wpG`).

**Chain.lean** (#258)
- Goal: a straight-line borrower is re-lendable.
- PROVED: `mutView` :58, `frame_outlives` :96, `relend_fin` :113, `relend_yield` :148,
  `relend_chainΓ` :176 and `relend_chain` :201.
- OPEN: borrowers that are not straight-line. Later files take them up.
- World: K + G1.

**Tree.lean** (#258)
- PROVED: `relend_respects_nesting` :32 and `exists_relend_lifetimes` :38.
- OPEN here: nested lends open together at a stop. Nested.lean addresses them later.
- World: lifetime arithmetic over K's `SRec` lists.

**Program.lean** (#258)
- PROVED: `withbor_relend` :119, `withbor_spans_yields` :166 and `withbor_spans_yields_cC` :188.
  The last places `withbor ℓ (Λ.λm. yield…; N_f)` in `𝒞⟦F_Σ(Ref T ⊗ B)⟧` for a linear, resuming
  `yield` answered at `1`.
- World: K's `cC` at an effect row. This is semantic membership, not a `CDerives` rule.

**Instance.lean** (#258)
- PROVED: `spans_two_yields` :41 and `spans_two_yields_sem` :62, with every hypothesis
  discharged. README:163 says the configuration "is not vacuous and it arises".
- World: K.

**Handle.lean** (#258)
- PROVED: `withbor_spans_yields_sem` :27 and `handle_spans_yields` :72. A lend spanning yields is
  handed to K's `handle_compatC` unchanged.
- OPEN here: the drop half at an affine yield. Drop.lean addresses it.
- World: K.

**Open.lean** (#258, #260)
- PROVED: `withbor_of_relendOfTyped` :57, which holds given `RelendOfTyped`. `Row.Resume` :40
  defines the rows covered.
- OPEN:
  - `RelendOfTyped` :45 is stated and "**Not derived.**"
  - `O151AsStated` :76 is O15.1 as §15 states it, "not attempted (#260, item 5 skipped)"
    (README:286).
- World: K `CDerives` → `cC`.

**Witness.lean** (#258)
- PROVED: `moved_payload` :36, `relent_holds` :81 and `gap_accepted` :86. The re-lent cell is in
  `𝒱⟦Mut 'a (Imm 'b 1)⟧_{e∘δ}`, so the ghost-end repair accepts Restrat's gap.
- OPEN: README:791 says "Whether `ρ₀` with these numerals arises in a run is not checked. The
  shape arises."
- World: Restrat's relabelled carrier over K.

**Body.lean** (#260, PR #261)
- PROVED: `bodyAt` :51, `Open` :63 (least fixed point), `open_ind` :102, `relend_of_open` :121,
  `opTable_frame` :147, `bodyAt_bind` :178, `open_bind` :216 and `open_yield` :256. The hypothesis
  is `LinResume` :141.
- The brief's determinism measure was declined, not attempted. README:184–193 reads it as needing
  route 1's `RefoldKripke`, which LoopBorrow refutes at an arising frame. The README says: "That
  the determinism route needs this step is my reading, not machine-checked."
- World: K + G1.

**Typed.lean** (#260)
- PROVED: the `RBody` rules (:180) for `[ret]` :312, `[perform]` :321, `[let]` :388/:439,
  `case` :452 and `seq` :487. Also `StopSafe` :166, `FrameThaws` :361, `stopSafe_thaws` :374,
  `relend_of_rbody` :541 and `withbor_of_rbody` :550.
- OPEN: no `RBody` case for `[lam]`, `[app]`, `[force]`, `∀E` at a row, `[then]`, `[handle]` or
  the borrow constants. Frames holding an `'x`-typed value other than `m` are not covered. The
  README says: "I have not verified that any obstruction is real."
- World: K + G1.

**General.lean** (#260)
- PROVED: `relendOfTyped_of_rbodyOfTyped` :62, with an added hypothesis that `@bδ` is defined.
- OPEN: `RBodyOfTyped` :53 is stated and "Not derived".
- World: K + G1.

**Branch.lean** (#260)
- PROVED: `branch_spans_yields` :177, a borrower branching around its yields, with every
  hypothesis discharged.
- World: K via `RBody`.

**Loop.lean** (#260)
- PROVED: `open_boundedFix` :33, `loop_open` :104 and `loop_spans_yields` :153, at every budget.
  The iteration is argued directly because `RBody` has no call rule (README:224–226).
- World: K + G1.

**Drop.lean** (#260)
- Goal: drop at an affine yield.
- PROVED: `opTableO` :49, `ewp_then_owner` :70, `withborR_compat` :108,
  `withborR_spans_yields_cC` :195, `withborR_spans_yields_sem` :230, `handleR_spans_yields` :284
  and `spans_two_affine_yields` :318.
- OPEN: "`RBody` at an affine row … is not done" (README:258).
- World: K at an affine row, under K's `[handle]`.

**Frames.lean** (#260)
- PROVED: `opTable_extR` :32, `ewpPostR_ext` :46, `ewpTS_M_antiFrameR` :89 (6.66 at a resuming
  table) and `ptoImm_dup` :110.
- OPEN: 6.150 lifted to resuming tables. The README calls it "Mechanical; the lift itself is not
  written". It is tracked as #277.
- World: K.

**Table.lean** (#262, PR #263)
- PROVED: the lend table `TabAt` :39, `tabAt_updV` :80, `wpG_tabAt` :87 (every run keeps it, from
  6.50), `wpTS_tabAt` :97 and `vC_mut_vary` :131.
- OPEN: the table for an `Imm` lend.
- World: K.

**Descend.lean** (#262)
- PROVED: `dropC` :37, `dropC_disj` :72, `stopAtD` :107, `OpenD` :125, `relend_of_openD` :174,
  `bodyAtD_bind` :218 and `openD_bind` :259. Stops report the cell they drop, and each lend is
  below the last.
- World: K + G1.

**Values.lean** (#262)
- PROVED: `LOk` :48, `fzV_freeze` :158, `fzV_thaw` :205, `fzG_freeze` :280, `fzG_thaw` :312,
  `FrameThawsD` :365, `lok_thaws` :381 and `stopSafe_lok` :403. Data carrying the lend is frozen
  and thawed by type.
- World: K's `vC` at `δ[x↦α]`.

**TypedD.lean** (#262)
- PROVED: `RBodyT` :35 and its rules :63–:205, `withbor_of_rbodyT` :267 and
  `relendOfTyped_of_rbodyTOfTyped` :294.
- OPEN: `RBodyTOfTyped` :285 is stated.
- World: K + G1.

**Tuple.lean** (#262)
- PROVED: `tuple_spans_yield` :93, a lend moved into a pair across a yield, with every hypothesis
  discharged.
- World: G1, concluding at K's `withbor`.

**Closures.lean** (#262)
- PROVED: `TV`/`TVG` :53/:84, `tv_sound` :100 (which re-derives a closure through
  `fundamentalC`), `tv_freeze` :251 and `tv_thaw` :307.
- World: G1 over K.
- README step 3f lists these as deleted under the generalised relation.

**ClosureBody.lean** (#262)
- PROVED: the `RBodyC` rules (`rbodyC_ret` :133, `_thunk` :147, `_perform` :155, `_let` :195) and
  `withbor_of_rbodyC` :270.
- OPEN:
  - `∀E` at a row, `[then]`, `[handle]` and the borrow constants were not attempted.
  - A pure piece handed a `CloL` closure: "I have not derived this case and have not verified that
    any obstruction is real."
- World: G1.

**Capture.lean** (#262)
- PROVED: `closure_spans_yield` :76, a closure capturing the lend, held across a yield.
- World: G1.

**Callee.lean** (#262)
- PROVED: `CloL` :45, `cloL_call` :64, `cloL_of_rbodyC` :79 and `callee_spans_yields` :241.
- The README explains in prose why K's route does not reach the stop: the `ewpTS` wand does not
  expose the split. That explanation has no Lean refutation behind it.
- `CloL` was later identified as vRL's `U` clause (`cloL_of_vRL`, Bridge.lean:243).
- World: G1.

**Kernel.lean** (#262)
- PROVED: `capture_hides_lend` :87. A `U(F 1)` closure whose type is free of `'x` holds the lend's
  cell, so the table must be stated over resources, not types.
- PROVED: `rbodyC_retTV` :55, given `KernelInvariant`.
- OPEN: `KernelInvariant` :47 is stated. "Not derived; no obstruction verified."
- World: G1 over K.

**Bridge.lean** (#264, PR #265)
- PROVED:
  - `record_shape_thunk` :101 and `tw_heap_any` :105. These are facts about K's `TW` showing that
    it does not supply `KernelInvariant`.
  - `KapRelR` :114, `kapRelR_mono` :121, `URelend` :133 and `frameThawsD_thunk_iff` :156. At a `U`
    slot of K the thaw is exactly `URelend`.
  - `uThaw_free` :184, `uThaw_tv` :197, and `vRL`/`cRL` :221/:231 (structurally recursive).
- OPEN: `URelend` at K. Its fresh-lend case reduces to Restrat's `WpNatural`, which is also open.
- World: K and vRL.

**RLCompat.lean** (#266, PR #267)
- PROVED:
  - `Relendable` :77 and `relendable_sep` :117;
  - `uRelendRL` :179, `URelend` at vRL with no hypothesis;
  - `thunkF_RL` :200 and `bind_RL` :313 (with `LinResume`);
  - `vRLg`/`cRLg` :508/:518 and `thunkF_RLg_below` :602.
- REFUTED: `thunkF_RL_fails_below` :435, instantiated at numerals in :471. Our single-lend vRL
  cannot carry a closure over an inner borrow's view.
  - Arising is argued in prose only. The resource is one that 6.65's `fresh` premise quantifies
    over, reached inside an inner `withbor` callback.
  - No Lean run reaching it is built.
  - `vRLg` admits the configuration.
- OPEN:
  - The full fundamental lemma at vRL.
  - Not derived: `effThen`, `effHandle`'s inner-stop clause, `unfoldN` and the `*U` constants.
- Recorded verdict: "go, for the generalised relation; no-go for `vRL`/`cRL` as merged."
- World: vRL, vRLg.

**Payload.lean** (#268, PR #273)
- PROVED: `payload_strict` :50 and `payload_strict_down` :59 (from 6.60 and 6.65's H4),
  `payFree_handed` :153, `lend_in_scope_below` :178 and `tabAt_wit` :189.
- World: K + `TabAt`.

**ImmLend.lean** (#268)
- PROVED:
  - Set subtraction and union for `imm` cells: `imm_ghostEnd_split` :50, `imm_ghostEnd_empty` :64,
    `imm_relend_union` :70 and `relent_copies` :86.
  - `ewpTS_I_frameR` :175, 6.64 at a resuming table, with the added hypothesis `hTL`.
  - `imm_spans_yield` :252.
- OPEN: the `Imm` table through nested references is "not built".
- World: G1 at a resuming table.

**Nested.lean** (#268; PRs #273 and #281)
- PROVED:
  - `nested_relend` :164, the reborrow commutation lemma. It refolds under the outer lend's new
    witness.
  - `nested₂_relend` :352, an inner lend of a different place.
  - `nested_spans_yield` :244 and `nested₂_spans_yield` :461.
- OPEN: #275 (reading `NestRelend` off typing) and #276 (the outer borrower continuing after a
  reborrow).
- World: G1 at two-entry stacks.

**Stacked.lean** (#279, PR #282)
- PROVED:
  - D16.1 as the mutual block `vRLs`/`cRLs`/`effRetS` :237/:252/:268, under
    `termination_by structural`. This puts §16.5's "no recursive domain" into Lean for D16.1.
  - Equality with K at σ = []: `vRLs_nil` :501, `cRLs_nil` :540 and `gfpAt_nil` :613, which is just
    `fundamentalC`.
  - The `withbor` rows at a one-entry stack: `withbor_reborrow_spans` :926,
    `withbor_other_spans` :941 and `withbor_reborrow_spans_yield` :1092.
- OPEN: GFP (D16.2) is stated as `GFPAt` :305 and `GFP` :312. It is not proved at any non-empty
  stack.
- World: vRLs.

**StackStep.lean** (#279, PR #283)
- PROVED, once for every stack (the user's n → n+1 form): `stack_step_other` :392,
  `stack_step_reborrow` :563, `stack_step_imm` :1003 (6.64 at every stack), `relendableS_sep` :816,
  `fold_other` :1190 and `stack3_reborrow_yield` :1272. The added hypothesis is `AllCross` :182.
- OPEN: GFP's induction, #275, #276, and stops at an intermediate depth (#278).
- World: vRLs.

### 1.3 Unmerged branches on GhostEnd

The three branches stack linearly. Each is 0 commits behind `main`.

| branch | head | ahead of main | PR | state |
|---|---|---|---|---|
| `origin/gfp` | `daf56c0` | 1 | #284 | open |
| `origin/gfp-arising` | `d31cbb3` | 2 | #285 | open |
| `origin/borrow-callbacks` | `5cfe062` | 3 | #287 | open |

Line numbers are at `5cfe062`. `Below.lean` is identical on all three branches.

**Below.lean** (`origin/gfp`, PR #284)
- REFUTED: `not_gfpAt_below` :196 and `not_gfp` :282, via `no_flat_mut_of_part` :67 and
  `tw_innerView` :120.
  - Configuration: the stack is `[x]`; the term is `Λ. λn. return (thunk (return n))` at
    `∀'y ⊏ ⊓Δ. Mut 'y 1 ⊸ F(U(F(Mut 'y 1)))`; the argument is an inner view `k ↦ M_3` below the
    stack.
  - The failing rows are `lam` and `allI`, because D16.1's `⊸` and `∀` clauses are not guarded by
    the table.
- What is refuted is our GFP statement (D16.2 over D16.1), which was drafted in
  `docs/effects-tr` §16. It is not a printed lemma.
- **The counterexample does not arise.** Arising.lean proves this.
- The branch records "blocked … Per the hard stop, tier 2 halts." The remaining rows were not
  attempted.
- The audit says not to merge it under a `not_` name.

**Arising.lean** (`origin/gfp-arising`, PR #285)
- The user ordered this follow-up: "use the **existing arising machinery**, as the paper does.
  This is not a restructure."
- PROVED, that the witness does not arise: `wpG_tabAtS_one` :112 (via 6.50),
  `not_tabAtS_innerView` :130 and `wpG_below_not_arises` :139.
- PROVED, D16.1 guarded at `U`, `⊸` and `∀` (vRLa): `vRLa`/`cRLa` :173/:189, `GFPAtA` :234,
  `gfpAtA_nil` :374, `below_excluded` :446, `lam_RLa` :478, and `allI_RLa` :815 (with added
  hypotheses `hσx` and `hσT`).
- OPEN: GFP at vRLa for any non-empty stack. With the guard at `⊸`, #275's borrow-constant row must
  read its callback at σ·y. "I have not derived it and have not verified that any obstruction is
  real."

**Extend.lean + `docs/effects-tr/17-borrow-callbacks.md`** (`origin/borrow-callbacks`, #286,
PR #287)
- §17 is PAPER-ONLY: a literature survey. Every Kripke model surveyed quantifies binders over
  future worlds, and BoLo's own `withbor` is a constant (6.172–6.174). Some primary sources are
  marked unverified.
- PROVED:
  - `vRLk`/`cRLk`/`effRetK` :62/:81/:100, still structural.
  - `all_elimK` :110: elimination is not weakened.
  - `callback_ext` :131: a callback read at σ and applied to a fresh lend's view is in the relation
    at σ·y.
  - `callback_ext_one` :167, with every hypothesis discharged at one entry.
- OPEN:
  - Conversion to `OpenS`/`cbQ`.
  - GFP at vRLk, whose `allI` row needs the context to be monotone along stack extension.
  - Whether `U` and `⊸` take the same quantifier.
  - The audit notes that vRLk has no `vRLk_nil`, so it may be strictly stronger than K at [].

---

## 2. Restrat (`experiments/Restrat`)

**Issue and PR.** #253 (open); PR #257, merged 2026-10-02.

**Goal.** L14.4/O5 of `docs/effects-tr` §14: re-stratification as naturality, together with an
audit of lifetime arithmetic.

**PROVED.**
- The `run_meta` audit (`Audit.lean`) finds that no definition in `Paper`, `Support` or `Core`
  computes a lifetime. `↓` occurs only as a witness or as a non-strict hypothesis
  (`inStratum_down_iff` Audit.lean:134).
- `shift_down` Injection.lean:113 and `shift_down_cut` :121.
- `relRU_of_inStratum` Fixed.lean:83.
- Naturality, operation by operation, of `●`, `○`, `⨀`, ex/ag, `⦇ρ⦈`, `✓`, `↭`, `reb_α`, `⋆`,
  `[α]`, the points-to forms and `И`.
- `restrat_segment` Segment.lean:73.

**REFUTED.**
- `mut_not_natural` MutCounterexample.lean:148 and `not_vDenNatural` Open.lean:30:
  `𝒱⟦Mut 'a (Imm 'b 1)⟧` is not natural under `n ↦ n+1`.
- **Arising: not checked.** The README says: "The refutation is of naturality stated over all
  resources."
- `frame_outside_image` Open.lean:43 is a fact about the proof method.
- The audit proposes restating the refutation as "over all valid resources".

**OPEN.**
- `WpNatural` Open.lean:37. "I have not derived `WpNatural`, and I have not verified that any
  obstruction to it is real."
- Transport of a segment's running state.

**World.** PAPER-carrier, plus `Core.SemC` for the segment corollary.

**Kernel.** Not used. GhostEnd imports it. The audit recommends retiring everything except
`Audit.lean` and the counterexample cell.

---

## 3. EffModel and EffModelRel (#235)

**Issue.** #235 (open, 2026-10-02), "Phase A: executable model of effects as a linear effect
algebra". Its goal: "a standalone executable model of the effects design, checking that it has the
properties we want before any kernel surgery. Phase B … follows only if A passes."

**PRs.** #237 (EffModel, merged 2026-10-02), #247 (EffModelRel, merged 2026-10-02), #255 (the
narrow run for #249, merged 2026-10-02).

**Design doc.** `docs/effect-model.md`: §0–§7 cover phase A, §8 phase B, §9 the narrow run.

**World.** SIB. It is standalone, uses no Mathlib, and nothing imports it (`lakefile.toml:154–161`
only). It is not BoLo and not K.

### EffModel (phase A)

The model has three parts:
- an untyped AST with a checker, `typecheck` (Typing.lean:574), and a syntactic T1 test
  `Tm.tailOnly` (:277);
- a CK machine `run` (Eval.lean:372), run at fuel 20000;
- 15 `#guard`s in `Tests.lean`: 21 laws over 952 contexts, 10 programs and 11 refusals.

**Status.** EffModel has no theorems, so none of the status words applies. Its results are tested
properties, and EffModelRel's theorems supersede them as evidence.

### EffModelRel (phase B and the narrow run)

**What it is.**
- An intrinsically typed calculus with an instance context Ψ and a value context Γ. Rows `Rw` of
  `(instance, lifetime)` pairs came in with #255. It has bounded `bfix` and a positive stream type.
- A denotation into finite trees (`ret`/`op`/`ab`/`nu`/`act`) with no step index.
- Binary worlds `W` (World.lean:39): a partial bijection of names, each side marked free / matched
  / pending / garbage.
- `TreeRel` (Rel.lean:41), `VR`/`CRU` (:216/:229) and `LR` (:295).
- `CtxEq` quantifies over **unmoded** contexts.
- The unary side is a separate moded judgement `VM`/`CM` (`ModedJ.lean`) with `Own` tokens.
- `Cell.lean` is a separate stratified cell model. No typing maps the calculus into it.

**PROVED.**
- Binary FP and soundness: `fundamental` Fundamental.lean:278 and `soundness : LR M N → CtxEq M N`
  Adequacy.lean:258.
- Algebraicity: `alg_bind` Laws.lean:67 through `alg_dtor` :114 (the destructor form).
- Handler laws: `h_ret` :148, `h_op` :164, `h_fwd` :202 and `h_fwd_ab` :227.
- Absorption: `absorb_pure` Tensor.lean:204 and `absorb_writer` Examples.lean:115. The failures
  under other nestings are proved as `¬CtxEq` at Examples.lean:136–155.
- `writers_commute` Writers.lean:116 (closed in #255).
- `tensor` Tensor.lean:91 (disjoint lent capabilities with `PureCo`).
- `idem_nu` Laws.lean:242, `new_nu` :246, `nu_nu` :262 and `no_accidental_handling` :362.
- Unary:
  - `VS.indep` Unary.lean:118;
  - `VM.fp`/`CM.fp` UnaryFP.lean:175/:215;
  - `safety` :518 and `safety_obs` :588, which give resource safety and effect safety with lends.
    `safety` was `resource_safety` before #255.
- Fixes to the TR's rules: `movedLend_*`, `resEscape_*` and `retTwice_*` (Findings.lean:43–89).
- Ownership: `fwd_id` (η, semantically) Ownership.lean:112 and `hnd_sim` (hiding as
  parametricity) :253.
- Cell model: `adequacy` Cell.lean:940 and `cell_safety` :1225. T1 in the cell model is
  `borProg_safe` CellExamples.lean:87.

**REFUTED** (all are `¬CtxEq` results in SIB):
- `nu_op_fails_multishot` Examples.lean:223. Staton's ν/op fails at an unrestricted operation.
  - Arising: the context is an intrinsically typed term and resumes a `unr` continuation twice,
    which the calculus allows. No proof shows it passes `CM`, but nothing in its shape excludes
    it. Read it as **arises** for multi-shot operations, as far as checked.
  - The user's response, 2026-10-02 (memory `multishot-only-if-free.md`): "we also don't need
    multishot unless we get it for free". The strength is "not needed unless free", not a ban.
  - #246 (open) investigates why, as a side question.
- `nu_op_fails_linear` Ownership.lean:72. It does **not arise**: it resumes a linear continuation
  twice, which only unmoded `CtxEq` admits.
- `eta_fails_linear` :181, `etaAff_obs` :207 and `etaAff_not_moded` :242. Neither witness arises in
  moded programs.
- Tripwires about the method:
  - `no_negative_domain` Obstruction.lean:35. This is TR T15: `μX. U(X → F bool)` has no set
    denotation in this method, which "does not say the type is unsound".
  - `no_place_store` Cell.lean:1239/1250.

**OPEN.**
- `O1` (Ownership.lean:93) is stated: ν/op over moded contexts at an operation without
  contraction. The source says "no obstruction verified".
- T1 in the calculus itself: relaxed T1 and the tail-resumption lemma. T1 is proved only in the
  unconnected cell model.
- η with cancellation.
- The lift onto BoLo's carrier (O2/O3), not attempted.
- TR T6.6 (machine–tree agreement), not attempted.

**Stale docs.**
- `experiments/README.md`'s EffModelRel row still says "Open: T1, effect safety". That predates
  #255, which proved `safety`.
- `docs/effect-model.md` §8.3/§8.8 also predate #255.

**Kernel.** Not used. `Core/`, `SPEC.md` and `docs/decisions.md` do not mention EffModel or
EffModelRel.

**Standing.** Recorded in memory `effects-are-core.md`, 2026-10-02:
- The user: "I only want to focus on what gets us to a full safe effect algebra."
- The memory then records that laws are "validated on the model (phase B, #247/#255)".
- Kernel-level equations are out of scope, "optional and don't get pursued unless they become
  necessary for safety".

So the binary laws stand as validation at SIB only. The audit
(`docs/effects-audit.md:275` @ `6db9b86`) recommends "keep as evidence, marked 'model of a sibling
calculus'", and leaves "keep with a banner, or archive" open (OQ 5).

---

## 4. Handler spikes at the paper layer: HandlersAsBorrows, HandlersControl, Shifts

### HandlersAsBorrows (#170; PR #184, merged 2026-09-30)

**Goal.** "Is a lexically scoped effect handler (Effekt's System Ξ …) an instance of borrowing in
BoLo?" The README's answer: "For answering handlers, yes, and it is proved."

**World.** PAPER (`DerivesWf` + `!`, `SemX`, angelic adequacy).

**PROVED.**
- `translate_typed` Translate.lean:190: `handle` becomes `withbor` form 2, and an operation becomes
  `withswap`.
- `effect_safety` Safety.lean:55 and `effect_safety_open` :71.
- `capability_not_outlives` :87 and the escape refusals :94–:108.
- `handle_is_shift` :115.
- `d_sepProg` Separating.lean:134 and `sepProg_eval` :150: this separates the system from Ξ, not
  from System C.
- `sharedUnit_safe` Examples.lean:112 and `sharedPair_eval` :120.

**REFUTED** (typing refusals, so arising does not apply):
- `twoBlocks_refused` Sharing.lean:196 (with `not_sharedCapture` :205).
- System C's aliased stateful capability has no derivation. The README says this "concerns the
  encoding and not a printed result".

**OPEN.** Block parameters, `box`/`unbox` (T2, #173), effectful clauses, value-capturing clauses,
and control.

**Kernel.**
- Not imported.
- SPEC §19's motivation cites the spike (`SPEC.md:2276`).
- Core's §18 elaboration makes the same choice (an operation is `withswap`) independently over
  CBPV. The experiment is a parallel statement at PAPER, not used by Core.

### HandlersControl (#170 follow-up; PR #185, merged 2026-09-30)

**Goal.** "state behind control, reentry, capture, and the closure outlives rule".

**World.** PAPER.

**PROVED.**
- `d_progU` Behind.lean:190, `progU_runs` :198 and `progP_eval` :204: state behind control at
  bounded depth.
- `d_memoProg` Reentry.lean:262 and `memoPair_eval` :277.
- `lam_bang_persistent` Capture.lean:42.
- `box_lolli_outlives_iff` Outlives.lean:35 and `crossProg` :65.

**REFUTED** (arising does not apply):
- `no_uniform_comp` Behind.lean:53 (a type equation).
- `spanFwd_refused` Reentry.lean:308 and `not_borrowSpansForward` :317.
- `multiShot_ref_refused` / `multiShot_imm_refused` Capture.lean:76/:80 and `forget_not_lolli`
  :150.

**OPEN.**
- K-a (native capture), "stated with its obligations, not built".
- K-b (`μX` with X under `⊸`, T15).
- K-c (destructors for continuations).
- The InvalML-style "in use" elaboration: "not derived … no obstruction verified".

**Kernel.**
- K-a is superseded by SPEC §19 / Entry 18: #186, PR #191 merged 2026-10-01, `Core/EffRules.lean`
  `effHandle`, `Core/EffDefs.lean:73` `ewpTS`.
- `SPEC.md:2276–2287` quotes `no_uniform_comp`, `not_borrowSpansForward` and
  `lam_bang_persistent` as Entry 18's motivation.
- The code itself is not imported.

### Shifts (ported from borrow_lang `3fd565b`, 2026-09-24)

**PROVED.** All by `rfl`: `withbor1_shift`, `withbor2_shift`, `withbor3_shift`,
`withload_shift` (Shifts.lean:22–31), `shift_modes` :36 and `ret_iff_not_C` :45.

**ATTEMPTED-FAILED.** `withborMI_compat` (lending a `Mut` as an `Imm`, `axWithborMITy`, :50). "It
does not compose as stated … I have not derived `withborMI_compat` and have not verified that any
obstruction is real." This is tracked as #174.

**World.** PAPER syntax.

**Kernel.** Used only through HandlersAsBorrows (`handle_is_shift`).

---

## 5. Experiments at K with effect rows: SecondClass

**Issues and PR.** #229, #216 and #161, all open. PR #231 merged 2026-10-01. Design doc:
`docs/second-class-and-system-c.md`.

**World.** K: `CDerives` with rows (`CTy.effOf`, `effHandle`, `effLet`), sound by `fundamentalC`.
There is no lend stack.

**PROVED.**
- `boundedFixEnv_compatX` Restated.lean:56, `boundedFixRec_compatX` :79 and
  `boundedFixEnvRec_compatX` :85.
- `recLog_derives` RecLog.lean:126 and `recLog_sem` :147.
- `d_handleAbortCapture` AbortClause.lean:69, `_pure` :89 and `handleAbortCapture_sem` :101:
  #216, abortive clauses capturing any context, as a derived rule.
- `handleAt_compatC` Prompts.lean:75: handling at a run-time name is sound given freshness
  (`fresh_exists` :105).
- Probes p1–p8 (`probes/*.bc`), checked and run compiled.

**REFUTED.** None.

**OPEN** (Prompts.lean docstring): "a machine step that chooses the name"; "a type that holds a
prompt whose name is not known statically".

**Kernel.**
- The `boundedFix` lemmas are instances of Core's `boundedFix_compatX`: SPEC.md:3186–3188 calls
  them "instances of it".
- `d_handleAbortCapture` lives only here. The audit (`effects-audit.md:477` @ `6db9b86`) recommends
  moving it into Core.
- #274 item 1 cites `handleAt_compatC` as the basis for ν instances.
- Decision 59 (`docs/decisions.md:744`) records "the user's decisions of 2026-10-01 after the
  second-class spike … spellings provisional".

---

## 6. Coeffects and CoeffectsStrict

### Coeffects (PR #100, merged 2026-09-29; Wagner's suggestion)

**Status.** The README's banner reads "Superseded in part by CoeffectsStrict (#101) … The `needs`
elaboration prototype here remains valid."

**World.** K-pure.

**PROVED.**
- `d_seqD` Demand.lean:163: sequential contraction of a demand is the reborrow.
- `d_parI` Imm.lean:57.
- `KDem.plain` / `KDem.elab` / `KDem.sem` Judgment.lean:52/:61/:72.
- `provide_wf` :79 and `reprovide_wf` :92.
- `main_every_run` Programs.lean:134 and `main_eval` :152.

**REFUTED.** None.

**OPEN.** Parallel contraction of a `Mut` demand: not derived.

**Verdict (README).** A borrow block is "a handler that has no operations and resumes once in tail
position", an identity of scope shape, not a duality.

**Recommendation (README).** "Adopt as an elaboration layer, not in the kernel." No entry in
`docs/decisions.md` adopts `needs`/`provides`.

**Kernel.** Not used.

### CoeffectsStrict (PR #101, merged 2026-09-29)

**World.** K-pure. The laws are stated as reductions on runs.

**PROVED.**
- Folds: `fold_beta` Fold.lean:76 and `fold_unique` :207.
- Unfolds: `unfold_next` Unfold.lean:55 and `unfold_close` :67. `unfold_unique` :155 holds for pure
  total steps only.
- Deep handler: `handle_return` Handler.lean:43, `handle_write` :50 and `handle_unique` :59.
- Context modalities: `copy_diag` Context.lean:41, `bang_idem` :70, `box_idem` :96 and
  `thunk_not_outlives` :111.

**REFUTED.** None in Lean.

**OPEN.**
- Fold laws at `Ref X`, and for `fold_imm`.
- Uniqueness of effectful unfolds, which "needs a relation between two runs".
- General-arity handlers (T15).
- Whether 6.64 needs a change for a boxed thunk holding a reborrowed view: "not derived, no
  obstruction verified".

**Kernel.**
- `Core/Handlers.lean:11` and `:210` cite its `Handler.lean` as precedent. That is a citation, not
  an import.
- Its recommendation "The kernel needs no handler construct" was overtaken by SPEC §19 (#186) and
  by the user's decision of 2026-09-30 (memory `effects-are-core.md`): "I want effects to be core
  to the language, we aren't going to be able to implement them correctly with sugar".

---

## 7. Suspension over codata: LoopBorrow

**PRs.** #111 (spike) and #112 (surface landing), both merged 2026-09-29. Related: #172 (the
spanning lend, K1) and #96, both open.

**Goal.** "Can `withbor` be lifted through every computation type, `ν` included?"

**World.** K-pure (`wpTS`, `TW`, `Tagged`, `Ext`), plus Frontend's checker for the programs.

**PROVED.**
- `wpTS_M_refold` Refold.lean:100: refolding at any depth.
- `refoldKripkeD` Dormant.lean:81: with the freeze, the refold step closes.
- `borrowFree_after_run` and `consumer_frame_world` (Dormant.lean).
- Six per-observation lend programs (Instances.lean), covered by `fundamentalC` and run with no
  cell left.

**REFUTED.**
- `refoldKripke_false` Obstruction.lean:245. **It arises**: `refold_fails_at_consumer_frame`
  (Dormant.lean:261) builds the failing configuration as a tagged typed world, via `TW.alloc` and
  `TW.immFrame`.
- `not_markerInstallable` :182: `↭` hands back only borrow cells the run started with.
- `not_lendingYield_mut` :306 and `not_lendingYield_imm` :314, from the unfolded lender's tagged
  typed world.
- The README is explicit: "This shows that the refold route does not close. It does not show that
  a spanning lend is unsound."

**OPEN.**
- The spanning lend. It needs "a register of open lends in `wpTS`/`TW` with `↭` read modulo it",
  which the README calls "a design reading of the paper, not a Lean result".
- `docs/effects-tr/16-regress.md:305` says to keep that register out of the world.
- Relabelling at `U` was not pursued. §16 links this remark to the regress GhostEnd met.

**Kernel.** **Used.** The per-observation lend is SPEC §14 (`SPEC.md:1400`, `:2703`),
`lib/lend.bc` and `Frontend/Elab/LoopLend.lean`. Decision 40 (`docs/decisions.md:281`) is
"Provisional … to be confirmed by the user".

---

## 8. Frames, purity and callbacks: FrameTheorems, TwoRun

### FrameTheorems (#37; PR #38, merged 2026-09-26)

**Goal (#37).** Does "a semantically typed callback `f : ∀'x ⊏ @b. Mut 'x A ⊸ ['x] T` …
provably leave every location [outside its lent resource] unchanged?"

**World.** K-pure, in the shape `wpTS` had before #76 (see the build note below).

**PROVED.**
- `wpTS_footprint` Footprint.lean:170.
- `stepsNA_det` EveryRun.lean:103 and `wpTS_footprint_every` :124.
- `call_frame` Callback.lean:132, `imm_call_keeps` :157 and `mut_call_frame` :234.
- `optic_frame` Laws.lean:43 and `over_fuse_typed` :189.

**REFUTED.** `not_runsAgreeOnDom` EveryRun.lean:159. Whether it arises was not checked.

**OPEN.** `EveryRunFootprint` EveryRun.lean:168 (stated), `ElemFrame`'s heap clause, and two-run
properties (`PureFn`'s value clause, fusion at effectful callbacks).

**Kernel.** Not promoted. It backs decision 22. `imm_call_keeps` is what excludes
InteriorMutability's option H.

### TwoRun (#39; PR #40, merged 2026-09-26)

**Goal (#39).** "Can they be had operationally, from the unary relation plus the machine's
determinism — or is a binary logical relation genuinely needed, and for what?"

**World.** K-pure, before #76, on runs with no array step.

**PROVED.**
- `steps_rename` Rename.lean:419.
- `freshRun_det` Fresh.lean:255.
- `fresh_run_image` Sim.lean:274, `wpTS_footprint_fresh` :286 and `everyFreshRunFootprint` :305.

**REFUTED.**
- `not_everyRunFootprint` Refute.lean:133.
- `not_everyRunFootprintRen` :237.
- `not_readFootprint` Read.lean:185.
- **None of these arises.** The witnesses "mention a location literal and are not typed by
  `CDerives`". They bound what follows from `wpTS` alone.

**OPEN.**
- `ReadFootprintTyped` Read.lean:81, stated: "I have not derived it and have not verified that any
  obstruction to it is real".
- Step 3 (the two-run laws) was not attempted.

**Kernel.** Not used.

### Build note for both: checked by reading, not by building

`experiments/README.md` lists FrameTheorems and TwoRun among the libraries that build at `main`.
By reading, they probably do not:
- Neither directory has changed since `cc32efb` (#73, 2026-09-27).
- Core's `wpTS` (`Core/World.lean:186–198`) now quantifies `∀ (A : Alloc) (k : Nat)` before its
  existential, and states the run as `ARun`.
- `Footprint.lean:174–177` still destructures `hw ρf fρ ps hf hc hT htg` directly into the
  existential, and states the run as `Steps`. `TwoRun/Refute.lean:45` does the same.
- The old "some run" form is now `wpTSAngelic` (`Core/World.lean:203`).

The same change affects TwoRun's explanation that "allocation is angelic". It describes the
pre-#76 `wpTS`. I did not build to confirm this.

---

## 9. Closures, codata and the affine closure

| experiment | effects relevance | world | proved (key) | refuted | open | kernel |
|---|---|---|---|---|---|---|
| **FnMut** (#236, PR #238; kernel #239, PR #240, merged 2026-10-02) | the affine closure `Aff^c A B = νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`; #274's `[gen]` types a continuation at it | K, `cC` with ν, no row | now in Core: `affBody_nuOk` Core/Aff.lean:53, `cC_aff_iff` :72, `aff_coind` :83, `hasDtor_aff` :108, `not_affine_aff` :128 | none | `[gen]` (see §11, lift-stage1) | **promoted**: SPEC §22, `Core/Aff*.lean`, `lib/aff.bc`; the fork is at `60936af`; the directory has no Lean |
| **Recursion** (borrow_lang `bb5de9b`, 2026-09-25) | ν/codata, coiteration | TW-old (CBPVWorld) | `unfold_sem` Nu.lean:281, `take2Close_runs` :403, `build3Free_runs` Mu.lean:221, `immReborrow_unroll` ImmMu.lean:414 | `naive_ne` ImmMu.lean:469 (syntactic inequality) | chooser and 6.131 at `μ`; observation depth | ancestor of SPEC §6/§7 (`SPEC.md:274`, `:386`) |
| **CBPVMu** | folds, fuel-free borrowed fold | TW-old | `vC_mu_iff` RelMu.lean:347, `vC_ind` :425, `fundamentalC`/`adequacyC` Fundamental.lean:211/:329 | none | `WpChainCommutes`, continuity | assembled into Core |
| **CBPVWorld** (borrow_lang `534637e`/`a31b498`, 2026-09-24) | none; ancestor of K | TW-old | `fundamentalC` Fundamental.lean:160, `adequacyC` :270 | none | `⊸E`/`∀E` on subterms | assembled into Core |
| **BorrowedClosures** | closures | PAPER | `reb_self_of_imm` Reborrow.lean:43, `reborrow_self_of_imm` :99, `envShape_unlinked` EnvCheck.lean:18 | none | stage 2 | superseded by `!T` (SPEC §2); stage 1 in `Support/Model/Unr.lean` |
| **Bang** (borrow_lang `c790ff9`) | `!` for closed code | PAPER | became the library | none | none | archived into `Paper/`, `Support/`, `Examples/Closures.lean` |
| **Grades** (#23, PR #42, merged 2026-09-26) | erasing capability tokens | K-pure | `cderives_iff_graded` Judgment.lean:349, `fundamentalG` Soundness.lean:327, `prog_runs_any` Erasure.lean:136 | none | migrating Core; graded checker | not adopted (decision 19) |
| **Affine** (#43, PR #45, merged 2026-09-27) | destructors; SPEC:1106 says `dtorE` is "total and pure" (no effectful finaliser) | K-pure | `ADerives.elab` Elab.lean:136, `fundamentalA` :177, `adequacyA` :183 | none | effectful destructors (out of scope) | **promoted**: SPEC §12, `Core/Dtor.lean` |
| **Optics** (#27, PRs #28/#35) | laws at effectful callbacks open | K-pure | `Optic.lift_cell` Lens.lean:326, `over_id`/`over_fuse` Laws.lean:131/:235 (under `PureFn`), `iterMut_shape` Shape.lean:503 | none | `AllAtOnceGoal` Traversal.lean:209 (L2, #176); effectful laws; "6.65/6.66 as an optic … not attempted" | not promoted (decision 22) |
| **Relaxed / FrameEnd / Projection** | none directly; FrameEnd's 6.64 exit is background for GhostEnd | TW-old | fundamental property and adequacy; `frame_image_empty` FrameEnd/FrameRules.lean:68 | `no_projection`, `frame_view_excluded`, `imm_view_rejected`, `mut_view_rejected`; no claim either way about arising | same-lifetime views | Relaxed became SPEC §4; the exclusions are cited in SPEC §5 |
| **ModesLabels**, **CBPVSplit** | none | PAPER | `weaken_sound`/`contract_sound`/`dup_sound`; `semX_iff_semC` | none | mode-indexed calculus | parts in Support; superseded by Core |
| **PositiveArrays** (PR #115) | none | K-pure | `wpTS_arrayMap` MapOwn.lean:167, `wpTS_M_framePartial` Partial.lean:25 | none | none | partly: SPEC §9, `Core/Slice*.lean` |

### InteriorMutability (PR #90, merged 2026-09-28)

This experiment has no Lean: a survey, eleven runnable programs and `run.sh`.

**Effects content.** Option E is a State handler (#18, open). Its sketch,
`sketches/state-handler.bc`, says: "SKETCH, not runnable … syntax … invented … Nothing here is
checked."

**Recommendation.** "no shared-cell resource kind; arena and array library first, then handlers".

**User standing.** Memory `no-interior-mutability.md`, 2026-09-28: "the user is ambivalent … it
is not a settled 'no'".

---

## 10. Outlives (#241 open, #243 closed; PRs #242, #244, merged 2026-10-02)

This entry is related to effects through T2: the outlives rule for thunks and continuations.

**World.** `LDerives`, a fork of K's `CDerives` with both premises relaxed (K-pure).

**PROVED.** `vC_outlivesL` Judgment.lean:174, `boxIL_compatC` Compat.lean:59,
`withbor2Le_compatX` :74, `fundamentalL` Derives.lean:345, `adequacyL` :446, and `counterTop` /
`nestTop` Programs.lean:153/:202.

**REFUTED.**
- `not_vC_outlives_le` Obstructions.lean:88. The witness is in the relation, but no run reaching it
  is shown.
- `no_nonstrict_stratum` :124, by Cantor.

**OPEN.** A non-strict `∀` binder.

**Kernel.** **Promoted**: SPEC §23 and decision 61 ("provisional spellings"). The strict cases stay
"Left as printed" (`SPEC.md:3588–3593`).

**Build discrepancy.** Its README says it builds at `b1cde24`, while `experiments/README.md` lists
it as building at `main`.

---

## 11. Effects work on other unmerged branches (not under `experiments/`)

**`origin/lift-stage1`** (`c9b3694`, 2026-10-02; 1 ahead of `main` and 2 behind; no PR)
- Commit message: "WIP (#274, not for merge): [gen] transcription in progress, stopped".
- `Core/Gen.lean` transcribes `docs/effects-tr` §15 D14.3–D14.7: `genE`, `Qgen` (D14.4, the
  greatest fixed point of `genF`) and `ewp_gen` (L14.3, :199).
- Per the commit, T14.4 (`affBox_of_kapRel`), T14.6 and the `CDerives` rule are not written.
- It is not imported by `Core.lean`. Status: ATTEMPTED, stopped. No failure is recorded; the commit
  says only "stopped".
- World: K. This is the one place outside GhostEnd where a continuation-typing result is being put
  into Core.
- #274's stated goal: "unary safety for full effects (FP, every-run safety, leak freedom, effect
  safety, T1), including stored continuations holding *external* borrows."

**`origin/effect-callbacks`** (`c321bd2`, 12 ahead of `main`; PR #233 CLOSED 2026-10-02)
- Frontend elaboration for #161 R2a: computation parameters, `|>`, `lib/callbacks.bc`, corpus.
- It contains no Lean results.
- REJECTED / ABANDONED by the user (PR #233 comment, empath-nirvana, 2026-10-02): "It solves the
  first-order case only, and the higher-order cases (callbacks taking callbacks, stored or returned
  callbacks, policies as values, effectful codata) were left pending behind workarounds. The goal
  was the general form, so we're stepping back to restate what we're trying to do before building
  again. The branch is kept for reference."

**`origin/loophandle`** (`51772c1`, docs only: `docs/handlers-over-div.md`)
- A design spike for handlers around divergent computations (SPEC §21 Open, decision 59).
- The doc says it was "**Parked** by the user before any Lean or probe was written: handlers around
  loops are not a priority". That is "not a priority", not "never".
- Every claim in it is marked [inspection] or [hypothesis]; nothing is [Lean].

**`origin/feature/borrowed-iter`** (PR #61 CLOSED 2026-09-27)
- `Core/BorrowedIter.lean`: `iterImm_wf` :133 and `iterImm_sem` :146, sorry-free.
- It is about iteration, not effects. It was closed as "the narrow version"; the branch is kept as
  a reference.

**`origin/effects-audit`** (#288, PR #289 open) and **`origin/effects-calculus-spec`** (#290, PR
#461 open)
- These are docs. Their verdicts on experiments are cited above.
- The draft spec failed validation, so treat it as a list of questions. Its
  `08-correspondence.md:355–356` classes EffModel and EffModelRel as "evidence (OQ-5)".

## 12. borrow_lang history

The experiments were developed in `~/repos/borrow_lang/Experiments/`. They were moved by
`065b102` (2026-09-24, "Remove Experiments/: moved to borrow-core/experiments"). The last commit
containing them is `a31b498`.

The 16 commits under `Experiments/` are all dated 2026-09-24:
- CBPVSplit (`57c633d`);
- ModesLabels (`c2a6110`);
- Shifts (`3fd565b`);
- BorrowedClosures (`efa2084` … `dfe907b`);
- Bang (`c790ff9`);
- CBPVCore (`60578d3`, `93bbbf0`);
- CBPVWorld (`646a03e` … `a31b498`).

None of them is an effects experiment. Shifts (the borrow axioms as one labelled-shift schema) and
ModesLabels (ownership kinds as adjoint modes) are what HandlersAsBorrows later builds on.

---

## 13. Cross-reference table

| experiment | world | proved | refuted (arises?) | open | used by kernel? |
|---|---|---|---|---|---|
| GhostEnd: Segment | K | `segment_fundamental` | none | none | no |
| GhostEnd: Relend | K + G1 | `ewpTS_M_frameR` | none | none | no (audit: promote) |
| GhostEnd: Freeze | K `wpG` | `freeze_at`, `wpG_box`, `frozen_above_extent` | none | handler body in `Res_h` (#274 item 3) | no |
| GhostEnd: Chain | K + G1 | `relend_chain` | none | borrowers that are not straight-line | no |
| GhostEnd: Tree | K lifetimes | `relend_respects_nesting` | none | nested lends at a stop | no |
| GhostEnd: Program | K `cC` at row (semantic) | `withbor_spans_yields_cC` | none | general borrowers | no |
| GhostEnd: Instance | K | `spans_two_yields_sem` (shape arises) | none | none | no |
| GhostEnd: Handle | K | `handle_spans_yields` | none | drop half | no |
| GhostEnd: Open | K `CDerives`→`cC` | `withbor_of_relendOfTyped` | none | `RelendOfTyped`, `O151AsStated` (not attempted) | no |
| GhostEnd: Witness | Restrat carrier over K | `relent_holds`, `gap_accepted` | none | arising of `ρ₀` not checked | no |
| GhostEnd: Body | K + G1 | `open_bind`, `relend_of_open` | none | determinism route declined (unchecked) | no (audit: retire) |
| GhostEnd: Typed | K + G1 | `RBody` rules, `withbor_of_rbody` | none | lam/app/force/∀E/then/handle/borrow constants | no (audit: retire) |
| GhostEnd: General | K + G1 | reduction lemma | none | `RBodyOfTyped` | no |
| GhostEnd: Branch | K | `branch_spans_yields` | none | none | no |
| GhostEnd: Loop | K + G1 | `loop_spans_yields` | none | the `[app]` gap | no |
| GhostEnd: Drop | K at an affine row | `withborR_compat`, `spans_two_affine_yields` | none | `RBody` at an affine row | no |
| GhostEnd: Frames | K | `ewpTS_M_antiFrameR` | none | 6.150 lift (#277) | no (audit: promote) |
| GhostEnd: Table | K | `wpG_tabAt` | none | `Imm` table | no (audit: promote) |
| GhostEnd: Descend | K + G1 | `openD_bind` | none | none | no |
| GhostEnd: Values | K `vC` at `δ[x↦α]` | `lok_thaws` | none | none | no |
| GhostEnd: TypedD | K + G1 | `withbor_of_rbodyT` | none | `RBodyTOfTyped` | no |
| GhostEnd: Tuple | G1 → K | `tuple_spans_yield` | none | none | no |
| GhostEnd: Closures | G1 | `tv_sound`, `tv_freeze`, `tv_thaw` | none | to be deleted under the generalised relation | no (audit: retire) |
| GhostEnd: ClosureBody | G1 | `withbor_of_rbodyC` | none | ∀E/then/handle/constants; `CloL` handed to a pure piece | no |
| GhostEnd: Capture | G1 | `closure_spans_yield` | none | none | no |
| GhostEnd: Callee | G1 | `callee_spans_yields` | none (the prose argument has no Lean refutation) | superseded by `cloL_of_vRL` | no |
| GhostEnd: Kernel | G1 over K | `capture_hides_lend` | none | `KernelInvariant` | no |
| GhostEnd: Bridge | K, vRL | `frameThawsD_thunk_iff`, `tw_heap_any` | none | `URelend` at K (reduces to `WpNatural`) | no |
| GhostEnd: RLCompat | vRL, vRLg | `uRelendRL`, `bind_RL`, `thunkF_RLg_below` | `thunkF_RL_fails_below` against our vRL (arising argued in prose only) | full FP at vRL; effThen, effHandle inner stop, unfoldN, `*U` | no |
| GhostEnd: Payload | K + `TabAt` | `payload_strict`, `payFree_handed` | none | none | no (audit: promote) |
| GhostEnd: ImmLend | G1 | `ewpTS_I_frameR`, `imm_spans_yield` | none | `Imm` table through nested references | no (audit: promote) |
| GhostEnd: Nested | G1, two-entry stacks | `nested_relend`, `nested₂_relend` | none | #275, #276 | no |
| GhostEnd: Stacked | vRLs | structural D16.1, `vRLs_nil`, `gfpAt_nil` | none | GFP (stated only) | no |
| GhostEnd: StackStep | vRLs | `stack_step_*` at every stack | none | GFP induction; #275, #276, #278 | no (audit: promote) |
| GhostEnd: Below (gfp) | vRLs | `tw_innerView` | `not_gfp` against our GFP (does **not** arise) | the remaining rows (hard stop) | no; unmerged (#284) |
| GhostEnd: Arising (gfp-arising) | vRLa | `wpG_below_not_arises`, `lam_RLa`, `allI_RLa` | none | GFP at a non-empty stack | no; unmerged (#285) |
| GhostEnd: Extend (borrow-callbacks) | vRLk | `all_elimK`, `callback_ext` | none | `OpenS` conversion; GFP at vRLk | no; unmerged (#287) |
| Restrat | PAPER-carrier + `Core.SemC` | audit, operation-wise naturality, `restrat_segment` | `mut_not_natural` / `not_vDenNatural` (arising not checked) | `WpNatural` | no; imported by GhostEnd |
| EffModel | standalone model + CK machine | none as theorems (`#guard`s) | none | superseded by EffModelRel | no |
| EffModelRel | SIB | binary FP, soundness, algebraicity, H-laws, tensor, ν laws, no accidental handling, `safety` | `nu_op_fails_multishot` (arises, for `unr`); `nu_op_fails_linear`, `eta_fails_linear` (do not arise in moded contexts) | `O1`; T1 in the calculus; lift to the BoLo carrier; T6.6 | no |
| HandlersAsBorrows | PAPER | `translate_typed`, `effect_safety` | `twoBlocks_refused` (typing; not applicable) | block params, T2, control | no; cited as SPEC §19 motivation |
| HandlersControl | PAPER | `progP_eval`, `memoPair_eval`, `lam_bang_persistent`, `box_lolli_outlives_iff` | `no_uniform_comp`, `spanFwd_refused`, `multiShot_*_refused` (typing; not applicable) | K-a (superseded by Core §19), K-b, K-c | results quoted in SPEC §19; code not imported |
| Shifts | PAPER syntax | shift instances (`rfl`) | none | `withborMI_compat` ATTEMPTED-FAILED | only via HandlersAsBorrows |
| SecondClass | K with rows | `boundedFix*_compatX`, `d_handleAbortCapture`, `handleAt_compatC` | none | run-time name step; name variables | partly duplicates Core (instances of `boundedFix_compatX`); cited by #274; decision 59 |
| Coeffects | K-pure | `d_seqD`, `KDem.elab`, `main_every_run` | none | parallel `Mut` contraction | no |
| CoeffectsStrict | K-pure | fold/unfold laws, `handle_write`, `bang_idem` | none | effectful uniqueness, general arity | cited as precedent in `Core/Handlers.lean` |
| LoopBorrow | K-pure | `wpTS_M_refold`, `refoldKripkeD`, six programs | `refoldKripke_false` (**arises**), `not_markerInstallable`, `not_lendingYield_*` | spanning lend (#172) | **yes**: SPEC §14 per-observation lend |
| FrameTheorems | K-pure (pre-#76 `wpTS`) | `wpTS_footprint`, `call_frame`, `imm_call_keeps` | `not_runsAgreeOnDom` (arising not checked) | `EveryRunFootprint`, two-run laws | no; probably stale against current `wpTS` |
| TwoRun | K-pure (pre-#76 `wpTS`) | `freshRun_det`, `wpTS_footprint_fresh` | `not_everyRunFootprint`, `not_everyRunFootprintRen`, `not_readFootprint` (none arise) | `ReadFootprintTyped` | no; probably stale against current `wpTS` |
| FnMut | K, ν | `cC_aff_iff`, `aff_coind` (now in Core) | none | `[gen]` (lift-stage1) | **yes**: SPEC §22 |
| Recursion / CBPVMu / CBPVWorld | TW-old | ν coiteration, μ folds, FP | `naive_ne` (syntactic) | `WpChainCommutes` etc. | **yes**: assembled into Core |
| Affine | K-pure | `ADerives.elab`, `fundamentalA` | none | effectful destructors | **yes**: SPEC §12 |
| Grades | K-pure | `cderives_iff_graded`, `prog_runs_any` | none | migrating Core | no (decision 19) |
| Optics | K-pure | `lift_cell`, `over_fuse` (pure) | none | effectful laws; `AllAtOnceGoal` | no (decision 22) |
| Outlives | `LDerives` (K-pure fork) | `fundamentalL`, `boxIL_compatC` | `not_vC_outlives_le` (no run shown), `no_nonstrict_stratum` | non-strict ∀ | **yes**: SPEC §23 |
| BorrowedClosures / Bang / ModesLabels / CBPVSplit | PAPER | closures, `!`, modes | none | none | absorbed into Paper/Support |
| InteriorMutability | no Lean | none | none | State handler (#18) | no |
| lift-stage1 (branch) | K | `ewp_gen` (L14.3) | none | T14.4, T14.6, the `[gen]` rule | not imported; WIP stopped |
| effect-callbacks (branch) | Frontend | none (Lean) | none | higher-order callbacks | no; PR #233 closed by the user |

**Summary of standing.**
- At K, the effects results the kernel uses come from three places: LoopBorrow's per-observation
  lend, FnMut's affine closure, and the motivations HandlersControl supplied for SPEC §19.
- Every GhostEnd, Restrat and EffModelRel result lives at a world other than K or W, and none is
  imported by Core.
- No experiment states or proves anything at the planned Kripke world W.

## Sources read

- `~/repos/borrow-core` at `8a1c326`:
  - `experiments/README.md`, and the README and Lean of every experiment named above. The GhostEnd
    README in full, and the declaration headers and docstrings of its files.
  - `SPEC.md` (§§2, 4–7, 12, 14, 18, 19, 21–23), `docs/decisions.md` (19, 20, 22, 23, 40, 48–61),
    `docs/effects-tr/README.md`, `docs/effects-tr/16-regress.md`, `docs/effect-model.md`.
  - `Core/World.lean:183–205`, `Core/EffDefs.lean`, `Core/Handlers.lean`.
- Branches:
  - `origin/gfp` `daf56c0`, `origin/gfp-arising` `d31cbb3`, `origin/borrow-callbacks` `5cfe062`
    (`Below.lean`, `Arising.lean`, `Extend.lean`, `docs/effects-tr/17-borrow-callbacks.md`, README
    deltas);
  - `origin/lift-stage1` `c9b3694` (`Core/Gen.lean`);
  - `origin/effect-callbacks` `c321bd2` (diffstat);
  - `origin/loophandle` `51772c1` (`docs/handlers-over-div.md`);
  - `origin/feature/borrowed-iter` (`Core/BorrowedIter.lean`);
  - `origin/effects-audit` `6db9b86` (`docs/effects-audit.md`).
- GitHub, read only:
  - `gh issue list --state all`, `gh pr list --state all`;
  - issues #18, #23, #37, #39, #43, #161, #170, #186, #216, #229, #235, #236, #239, #241, #243,
    #246, #249, #253, #258, #260, #262, #264, #266, #268, #274–#280, #286;
  - PRs #38, #40, #42, #45, #61, #90, #100, #101, #111, #112, #184, #185, #191, #231, #233, #237,
    #238, #240, #242, #244, #247, #255, #257, #259, #261, #263, #265, #267, #273, #281–#285, #287,
    #289.
- `~/repos/borrow_lang`: `git log -- Experiments` (16 commits, 2026-09-24), `065b102`.
- Memory: `MEMORY.md`, `hard-stop-on-regress.md`, `effects-are-core.md`,
  `multishot-only-if-free.md`, `unknowns-first.md`, `no-interior-mutability.md`,
  `effect-handling-is-erased.md`, `paper-mu-tabled.md`, `threads-are-required.md`.
