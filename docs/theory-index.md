# Theory index

One entry per experiment (`experiments/*/README.md`) and per idea, scope, survey and design
document that asks a theoretical question. Each entry gives the question, the source's own
answer (quoted), its status, the Lean names that carry it, and what it feeds. The last two
sections collect the **open theoretical problems** across all sources, deduplicated and each
with its issue, and the results that later work can **rely on**.

Conventions:

- **Status** is one of *proved*, *refuted* (a stated goal is machine-checked false in our
  model), *partial*, *open*, *superseded (by …)*, or *survey* (a literature reading, no Lean).
- "Refuted" and "excluded" always refer to a specification or extension stated in this
  repository, checked against our model. No entry says a printed result of `[CONF]`/`[TR]` is
  false; where a printed lemma is the tool of a refutation (for example 6.38 in
  `frame_view_excluded`), it is named as the tool.
- Quotations are from the named README or document. **(inferred)** marks a statement that is
  this index's reading, not the source's.
- Issue numbers: [#N] links are to this repository's issues. `K1`–`K5` are
  `docs/effects-scoping.md` §0's kernel items; the strings design's `K0`–`K5` and `K2′` are a
  different series (`docs/strings-slices-design.md` §0) and are always written "strings K…".
- Building the experiments: `experiments/README.md` says which build at `main` and which need
  `c8694fa` or earlier.

`docs/adjudications.md` is not indexed entry by entry: it records how the mechanisation reads
`[CONF]`/`[TR]` (§12.1–§12.73, conventions G1–G8), and entries below cite it where they depend
on a reading (§12.67–§12.73 are the typed-world repairs behind the Fundamental Property).

**Contents.** [Experiments](#experiments) · [Idea and scope documents](#idea-and-scope-documents) ·
[Surveys](#surveys) · [Designs with open kernel items](#designs-with-open-kernel-items) ·
[Open theoretical problems](#open-theoretical-problems) · [Settled](#settled)

---

## Experiments

### Affine

- **Question:** "Can an owned value (`Ref A`, a block, a list, a codata thunk) go unused, with
  the elaborator inserting its destructor so the result is an ordinary linear core program?"
  (#43)
- **Answer:** "yes, with no model change and no new invariant. Every droppable type's destructor
  is a closed `CDerives` derivation. The affine judgment `ADerives` elaborates into `CDerives`
  by a translation that never inverts `CDerives`."
- **Status:** proved; promoted (SPEC §12, `Core/Dtor.lean`, `Frontend/Check`).
- **Key results:** `dtor_wf`, `hasDtor_of_affine`, `ADerives.elab`, `fundamentalA`,
  `adequacyA`, `owner_not_shared`, `drop_needs_live`, `sumAff_leaks`, `blockAff_leaks`.
- **Feeds:** SPEC §12; K3 (destructors that perform I/O, [T9](#t9-destructors-that-perform-io-or-fail-k3));
  decision 23; `U C` has no destructor, which is why `ν` needs `close`.
- **Links:** [`experiments/Affine/README.md`](../experiments/Affine/README.md).

### Bang

- **Question:** add the paper's suggested exponential `!T` ("completely compatible with our type
  system", `[CONF]` 415:4) in place of closed code.
- **Answer:** "the Fundamental Property and adequacy over the extended `DerivesWf`"; closures
  owning their environment are typable, and "`fn T₁ T₂` is `!(T₁ ⊸ T₂)`".
- **Status:** proved; archived (became `Paper/`, `Support/`, SPEC §2).
- **Key results:** `bangLamI`, `bangAllI`, `bangE`, `copyBangAx`, `forgetBangAx`,
  `gSepX_persistent`, `reborrow_self_of_imm` (6.131's `!` case); programs `ownedFn`,
  `mutClosure`.
- **Feeds:** SPEC §2; decision 3; borrowed closures ([BorrowedClosures](#borrowedclosures));
  [#170].
- **Links:** [`experiments/Bang/README.md`](../experiments/Bang/README.md).

### BorrowedClosures

- **Question:** "can a borrowed closure be called?" Today `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk`.
- **Answer:** Stage 1: "at an `unr` closure type, 6.131 holds with `Imm̲ 'b T ≜ T` instead of
  `Unk`". Stage 2 stopped at `TypedImage.image_dom`: "At `fn` the image must be the closure's
  captured resource, and neither the type nor the value determines it"; with closure conversion,
  closed code `fn T₁ T₂` goes through the typed world. The fork is "superseded by the
  exponential `!T` … `fn T₁ T₂` is `!(T₁ ⊸ T₂)`".
- **Status:** stage 1 proved (in the library as `Support/Model/Unr.lean`); stage 2 superseded by
  `!T` (SPEC §2, decision 3). Environments and `FnMut` as a closure former: "not attempted".
- **Key results:** `reb_self_of_imm`, `reborrow_self_of_imm`, `envShape_unlinked`,
  `envValue_unlinked`; archived fork: `fnI_compatX`, `fnE_compatX`, `callBorrowed_runs`.
- **Feeds:** decision 3 ("A closure former's borrowed image is not determined by its type");
  SPEC §2 *Why `!`*; `docs/scope-recursion.md` §3.1 (the same obstruction for a packed `∃S`).
- **Links:** [`experiments/BorrowedClosures/README.md`](../experiments/BorrowedClosures/README.md);
  archived commits `d1f3929`, `8d43821`, `6b8a77e`, `dfe907b` in `borrow_lang`.

### CBPVCore

- **Question:** are the CBPV term formers sound over the typed world, and does "the full
  resource calculus live in the CBPV core"?
- **Answer:** all compatibility lemmas close; `fundamentalC` and `adequacyC` hold. Limitation:
  records are typed at BoLo's `Ty`, so `Imm @a A` "is empty" where `A` has no `cbv` preimage.
- **Status:** proved; superseded by [CBPVWorld](#cbpvworld) for the `Imm` restriction.
- **Key results:** `vX_eq_vC_fun`, `semX_iff_semV`, `cC_iff_stacks`, `cC_bind`, `fundamentalC`,
  `adequacyC`, `fundamentalCBV`, `vC_imm_outside_image`.
- **Feeds:** SPEC §3; decision 4. Open there: "The syntactic CBV embedding … is not attempted"
  ([T7](#t7-conservative-extension-and-agreement-of-the-worlds)).
- **Links:** [`experiments/CBPVCore/README.md`](../experiments/CBPVCore/README.md).

### CBPVSplit

- **Question:** "If CBPV is the right home, the Kripke part should sit only at `U`, the `wp` only
  at `F`, and `→` (and the lifetime `∀`) should need neither."
- **Answer:** "The factoring holds clause for clause"; `Ext`-stability "survives on native
  types". Caveat: "The correspondence is by construction … It does not show that the
  CBPV-native term formers are sound."
- **Status:** proved; superseded by [CBPVCore](#cbpvcore).
- **Key results:** `vX_eq_vC_fun`, `semX_iff_semC`, `fundamentalPropertyC`, `vC_local`.
- **Feeds:** decision 4.
- **Links:** [`experiments/CBPVSplit/README.md`](../experiments/CBPVSplit/README.md).

### CBPVMu

- **Question:** R4 of `docs/scope-recursion.md`: add `μ` to the typed world's `VTy` and find out
  "whether the typed world's choosers and invariants accept a recursive payload"; then a borrowed
  fold, and the delay type.
- **Answer:** "The chooser and invariant proofs accept `μ` unchanged." A fuel-free borrowed fold
  terminates by "the loaded witness's cell count, carried across `withload` by
  `withload_sized`". Delay: `fixD` "sound by coinduction … No approximation and no index";
  `λd. later (g d)` "is **not** a guardedness condition".
- **Status:** proved; promoted into `Core` (SPEC §6, §7). Open items below.
- **Key results:** `vC_mu_iff`, `vC_ind`, `vShape_ind`, `vC_outlives` at `μ`,
  `reborrow_vShape`, `withload_sized`, `foldImm_compatX`, `foldOwn_compatX`,
  `foldReuse_compatX`, `mapIncR_inPlace`, `cC_delay_iff`, `fixD_compatX`, `naive_not_sem`,
  `delayRel_le_approxLim`, `approxLim_le_delayRel`, `not_exists_forall`.
- **Open, per the README:** "`X` under `U`, and `Ref` over `⊕`: not done"; a borrowed fold at
  `Ref S` with `X` inside a compound `S` ("I have not derived such a rule"); "`foldImm`'s `R`
  must outlive every lifetime, so a fold returning a borrow into the structure is not covered";
  "The continuity question of Step 1 is open" (`WpChainCommutes`); non-tail recursion needs a
  stack or a `bind` on `D`.
- **Feeds:** SPEC §6, §7; [T12](#t12-non-tail-recursion-and-a-direct-fix), [T13](#t13-the-delay-type-approximations-and-codata-adequacy),
  [T15](#t15-recursive-types-and-folds-beyond-fshape); K4, K5; [#12], [#32]; decision 7.
- **Links:** [`experiments/CBPVMu/README.md`](../experiments/CBPVMu/README.md).

### CBPVWorld

- **Question:** does the typed world, re-typed at CBPV types, remove the four `cbv`
  restrictions "while keeping the Fundamental Property and adequacy"?
- **Answer:** "No rule has a `cbv T` restriction." BoLo embeds: `embed : DerivesWf Δ Γ e T → …
  → CDerives Δ (cbvCtx Γ) e (.val (cbv T))`, and `adequacy_of_derivesWf`.
- **Status:** proved; became `Core` (SPEC §3).
- **Key results:** `vC_outlives` (6.60 at `vC`), `boxI_compatC`, `allE_compatC`,
  `fundamentalC`, `adequacyC`, `embed`, `adequacy_of_derivesWf`, `cRecBorrow_runs`.
- **Open, per the README:** "Agreement with the old world on translated types … is not
  attempted"; the embedding goes through three derived forms; "`VOutlives` … has no rule at
  `U C` or `Unk`".
- **Feeds:** [T2](#t2-an-outlives-rule-for-thunks-u-c), [T7](#t7-conservative-extension-and-agreement-of-the-worlds); SPEC §3.
- **Links:** [`experiments/CBPVWorld/README.md`](../experiments/CBPVWorld/README.md).

### Coeffects

- **Question:** Wagner's suggestion: does a borrow block *provide* a coeffect the way a handler
  *discharges* an effect? Plus the 2×2 of data/codata/effects/coeffects, "every handled effect
  carries a coeffect", and tail-resumptive effects needing only the coeffect interface.
- **Answer:** "Wagner's hypothesis holds as an identity of scope shape. As a duality it only
  rhymes." "A borrow block is a handler that has no operations and resumes once in tail
  position." Recommendation: "`needs`/`provides` as an elaboration layer … no kernel change".
- **Status:** partial; "Superseded in part by `experiments/CoeffectsStrict` … (e.g. `Mut`
  capabilities are effects, not coeffects). The `needs` elaboration prototype here remains
  valid."
- **Key results:** `d_seqD` (contraction by reborrowing), `d_parI`, `d_weakenD`, `KDem.elab`,
  `KDem.sem`, `provide_wf`, `reprovide_wf`, `main_every_run`, `main_eval`.
- **Not derived:** "The `Mut` row's missing `⊕` is `Mut 'x U ⊸ Mut 'x U ⊗ Mut 'x U`. … This
  spike neither derives it nor verifies an obstruction to it." (Recorded under
  [Not derived, no consumer](#not-derived-no-consumer).)
- **Feeds:** [#18]; [#170]; `docs/ideas-handlers-and-borrows.md`; decision 48.
- **Links:** [`experiments/Coeffects/README.md`](../experiments/Coeffects/README.md); PR #100.

### CoeffectsStrict

- **Question:** do data/codata and effects/coeffects "work together once each is defined in a
  strict algebraic sense"?
- **Answer:** "They do work together, but as axes, not as a 2×2 of dualities." "Scope is a third
  axis … They meet the scope axis only through the Fundamental Property." "The comonad `FU` of
  Levy's adjunction is not a coeffect." "Borrows are an instance of none of the four."
- **Status:** proved (the laws, at the reach its §5 states); the account is a paper argument.
- **Key results:** `fold_beta`, `fold_unique`, `unfold_next`, `unfold_close`,
  `unfold_unique` (pure steps), `handle_return`, `handle_write`, `handle_unique`,
  `copy_diag`, `copy_counit`, `bang_idem`, `box_idem`, `d_box_dig`, `thunk_not_outlives`,
  `d_box_data`, `d_box_codata`.
- **Open, per the README:** fold laws "at `Ref X`, and for `fold_imm`" and unfold uniqueness at
  effectful steps "not derived, no obstruction verified"; "Whether the frame end of `withbor`
  (6.64) needs any change for a boxed thunk that holds a reborrowed view: not derived"; a
  scheduler over heterogeneous lifetimes "needs existential lifetimes or scoped spawning".
- **Feeds:** [#18] (handlers as folds; general arity needs `X` under `U`), [#52],
  [T2](#t2-an-outlives-rule-for-thunks-u-c), [T15](#t15-recursive-types-and-folds-beyond-fshape),
  [T16](#t16-read-footprint-and-two-run-laws), [T19](#t19-tasks-holding-borrows-at-different-lifetimes);
  effects-scoping E5 (handler laws).
- **Links:** [`experiments/CoeffectsStrict/README.md`](../experiments/CoeffectsStrict/README.md); PR #101.

### Core

- **Question:** none of its own; the promoted consolidated world.
- **Answer:** "The consolidated world is now the library target `Core` … the implementation of
  `SPEC.md` §3–§7."
- **Status:** promoted (assembled from CBPVMu, CBPVWorld, Relaxed, Records, Places, LeafPlaces,
  Recursion).
- **Links:** [`experiments/Core/README.md`](../experiments/Core/README.md), `Core/README.md`,
  [`docs/consolidation-audit.md`](consolidation-audit.md).

### FrameEnd

- **Question:** with a 6.64 frame end that subtracts the image at the frame's own lifetime (the
  survey's option 5.1(b)), do FP and adequacy hold, and do a same-lifetime `Imm` projection, L3
  and L2 then go through?
- **Answer:** FP and adequacy hold, and "at 6.64's end the subtraction is empty". The projection
  is still excluded, "by `↭` at the projection's own run"; L3 "excluded the same way"; "L2 free
  rider: no". "No resource entailment can produce the view … No term can produce it either,
  because every `wpTS` run ends in a `↭`."
- **Status:** refuted for the projection in this model (the frame-end change is proved sound but
  unused); dropped by the consolidation audit.
- **Key results:** `FrameEnd.fundamentalProperty`, `frame_image_empty`, `ti_sub`,
  `Views.imm_view_rejected`, `Views.mut_view_rejected`, `Projection.no_projection`.
- **Feeds:** SPEC §5 Open; decision 5; [T4](#t4-same-lifetime-views-through-a-pointer);
  effects-scoping §7.3 (operations returning a borrow).
- **Links:** [`experiments/FrameEnd/README.md`](../experiments/FrameEnd/README.md).

### FrameTheorems

- **Question:** (#37) are the Optics frame hypotheses (`ElemFrame`, `PureFn`, distinct cells)
  "theorems of the logical relation"?
- **Answer:** "An existing location changes only where `⦇ρ⦈` holds it exclusively." "None of the
  Optics laws becomes unconditional in its own form"; unconditional at typed worlds:
  `over_fuse_typed`, `optic_frame`, `imm_call_keeps`.
- **Status:** partial.
- **Key results:** `wpTS_footprint`, `flat_factor`, `stepsNA_det`, `wpTS_footprint_every`,
  `call_frame`, `imm_call_keeps`, `mut_call_frame`, `optic_frame`, `over_fuse_typed`,
  `elemFrameNA_of_typed`, `pure_heap_of_typed`, `not_runsAgreeOnDom`.
- **Not derived:** the footprint on runs that allocate (`EveryRunFootprint`, settled by
  TwoRun for fresh runs); the laws at intermediate typed worlds (`iterMut_shape` keeps
  `ElemFrame`); two-run properties.
- **Feeds:** [T16](#t16-read-footprint-and-two-run-laws) ([#41]); [#14] (borrow invariants as
  theorems); InteriorMutability's option H.
- **Links:** [`experiments/FrameTheorems/README.md`](../experiments/FrameTheorems/README.md).

### Grades

- **Question:** (#23) "Is an explicit grade semiring equivalent to that, does migrating `Core` to
  it delete more than it adds (decision 20), and does grade `0` give erasure?"
- **Answer:** equivalent under the Core profile; "Verdict: not net-negative … the relation never
  reads them"; the deletions "come from the **endpoint type conditions**, and `Core` can adopt
  those without grades"; erasure: "`prog_runs_any v` runs `main v` to the same result for
  **every** value `v`".
- **Status:** proved; not migrated. Widening promotion is shown sound here and is still SPEC §10
  Open.
- **Key results:** `cderives_iff_graded`, `splitP_iff`, `deadP_iff`, `soloP_iff`,
  `persistent_iff`, `fundamentalG`, `fundamentalGraded`, `bangThunkF_compatG`, `promote_int`,
  `promote_int_not_core`, `semC_weak`, `copyBang_core`, `forgetBang_core`, `forgetUnk_core`,
  `prog_runs_any`, `scale_nonpersistent_rejected`.
- **Feeds:** [#9] ([T6](#t6-widening-promotion)); decisions 19, 20; [#52] (erased
  capabilities); `docs/prior-art-sessions.md` S5.
- **Links:** [`experiments/Grades/README.md`](../experiments/Grades/README.md).

### InteriorMutability

- **Question:** "What do real Rust programs use interior mutability for? And what does each use
  cost here, today and with the features that are planned?"
- **Answer:** "**Do not add a shared-cell resource kind to the model.**" What is inexpressible
  "is shared ownership (`Rc`) and closures capturing non-persistent values", not mutation. "H is
  closed": an `unsafe` write through `Imm` "contradicts `imm_call_keeps`".
- **Status:** survey with runnable programs (no Lean).
- **Key results:** none new; relies on `imm_call_keeps`, `wpTS_footprint`.
- **Feeds:** [#119], [#79], [#94], [#18] (State/Writer handlers); decision 30.
- **Links:** [`experiments/InteriorMutability/README.md`](../experiments/InteriorMutability/README.md).

### LeafPlaces

- **Question:** "does anything in the model depend on a location holding a whole value?" Can an
  owned struct handle be a packed family of leaf locations?
- **Answer:** "**No.** … What the machine lacks is **address arithmetic**"; alloc, free and
  borrow of any plain shape are derived rules; `crossPack` shows re-pairing leaves across blocks
  "is fine in the model but not for a one-word handle", a checker rule.
- **Status:** proved; promoted (SPEC §5 blocks).
- **Key results:** `allocS_wf`, `freeS_wf`, `withborS_wf`, `shortenE_wf`, `wpTS_allocS`,
  `withborS_ret`, `withborS_packed`, `packed_node`, `crossPack_not_packed`,
  `infinite_blockPath`.
- **Not derived:** the family rule at a result `T` "holding a borrow, a function or `Unk`";
  variants.
- **Feeds:** decision 6; [#20], [#77], [#19], [#11]; [T17](#t17-side-conditions-of-family-borrows).
- **Links:** [`experiments/LeafPlaces/README.md`](../experiments/LeafPlaces/README.md).

### LoopBorrow

- **Question:** (O1) "Can `withbor` be lifted through every computation type, `ν` included?
  Which of the blocked programs need that, and which are already expressible?"
- **Answer:** "**The per-observation lend works today, with no new rule.**" "**A lend that spans
  observations does not close in this model.** … So the spanning lend needs a model change: a
  borrow that `↭` lets outlive the run that opens it. That change is not verified sound, and
  nothing here shows the spanning lend unsound." "**A lending yield in pull form … is excluded
  in every route here.**"
- **Status:** partial: per-observation lend proved and landed (SPEC §5, §14); the spanning lend
  open.
- **Key results:** `not_upd_of_new_mut`, `not_upd_of_ended_mut`, `not_upd_of_new_imm`,
  `ext_of_cellIn`, `refoldKripke_false`, `refold_fails_at_consumer_frame`, `wpTS_M_refold`,
  `refoldKripkeD`, `not_markerInstallable`, `upd_borrow_top`, `borrowFree_after_run`,
  `not_lendingYield_mut`, `not_lendingYield_imm`.
- **Feeds:** K1 ([T1](#t1-the-spanning-lend-k1)), K2 ([#96]), [#52], [#162], [#18],
  [#57], `lib/lend.bc`, decision 40.
- **Links:** [`experiments/LoopBorrow/README.md`](../experiments/LoopBorrow/README.md).

### ModesLabels

- **Question:** "Do the paper's three ownership kinds behave as adjoint-logic modes?"
- **Answer:** "`σ` is sound for the model as it stands"; "`Imm̲ 'b T` is unrestricted at every
  `T`. The paper's metafunction is the projection to the top mode." "a label is a licence to
  break independence for the duration of a scope" is "an interpretation … not a theorem".
- **Status:** proved (checked for the model, not derived from a mode-indexed calculus).
- **Key results:** `weaken_sound`, `contract_sound`, `dup_sound`, `mode_immReborrow`.
- **Feeds:** [Shifts](#shifts), [BorrowedClosures](#borrowedclosures), [#68].
- **Links:** [`experiments/ModesLabels/README.md`](../experiments/ModesLabels/README.md).

### Optics

- **Question:** (#27) "Is a borrow an instance of a general abstraction, a linear optic whose
  residual the lender holds for a lifetime?"
- **Answer:** "Stages 1–3 need nothing beyond existing rules. The one piece not derived is the
  all-at-once borrow form over a dynamic length (L2)." "The spatial half, residuation, is a
  machine fact. … The temporal half, the lifetime order, appears only in typing."
- **Status:** partial; decision 22 ("Optics are a parallel to borrowing, not its abstraction").
- **Key results:** `Optic.runs`, `Optic.lift_cell`, `Optic.comp_obs`, `over_id`, `over_fuse`,
  `withload_read`, `get_copy`, `tag_frozen`, `prismLift_runs`, `d_iterMut`, `iterMut_shape`,
  `splitMut`; stated goal `AllAtOnceGoal`.
- **Not derived:** `AllAtOnceGoal` (L2 over a dynamic list); the linear prism with `T ⊕ 1`;
  laws at effectful callbacks; lens-with-prism composition ("`VOutlives` has no rule at `U C`").
- **Feeds:** [T5](#t5-l2-borrowing-a-dynamic-length-structure-at-one-lifetime),
  [T2](#t2-an-outlives-rule-for-thunks-u-c), [T16](#t16-read-footprint-and-two-run-laws);
  `docs/prior-art-optics.md`.
- **Links:** [`experiments/Optics/README.md`](../experiments/Optics/README.md).

### Places

- **Question:** "Is borrowing several disjoint locations at one lifetime derivable from existing
  constructs?"
- **Answer:** "Yes. The binary family is a term of the language, and its typing is a derived rule
  of `DerivesWf`. No constructor is added." Static `split_at_mut` "yes, for free".
- **Status:** proved; promoted (SPEC §5 family borrows).
- **Key results:** `withbor2_wf`, `withborM2_wf`, `withborI2_wf`, `withborM2_sem`,
  `swapBoth_runs`, `splitFour_runs`.
- **Not derived:** the family rule at a `B` or `T` containing `⊸`, `∀` or `Unk` outside `!`.
- **Feeds:** decision 5; [T17](#t17-side-conditions-of-family-borrows),
  [T2](#t2-an-outlives-rule-for-thunks-u-c).
- **Links:** [`experiments/Places/README.md`](../experiments/Places/README.md).

### PositiveArrays

- **Question:** does the positive-array eliminator of *Compiling with Arrays* give strings K2 "a
  cleaner statement and a proof"; are "arrays, records and structs … all instances of one indexed
  tensor"?
- **Answer:** "**K2 is proved at `Mut` and at `Imm`** … with no model change"; "**K2 has side
  conditions the one-cell rules do not all have.** … Whether they are needed is not verified";
  "The class hypothesis holds at the model, not at the types"; "The eliminator is a bulk
  operation, not a fold."
- **Status:** proved; K2 promoted (SPEC §9, `Core/Slices.lean`, `Core/SliceFrames.lean`). Open
  items below.
- **Key results:** `wpTS_M_frameList`, `wpTS_I_frameList`, `sliceBorrowM_compatX`,
  `sliceBorrowI_compatX`, `vP_fam_split`, `vP_fam_join`, `sepList_partition`,
  `wpTS_M_framePartial`, `wpTS_arrayMap`, `arrMap_compatX`, `famLenBound`.
- **Open, per the README:** "Whether K2's side conditions are needed"; "K2′ (an `imm` reborrow
  of a `mut` family) by the same induction with `withbor3`"; strided families; map fusion and
  fission as two-run laws.
- **Feeds:** the strings design; [T3](#t3-lending-a-mut-as-an-imm), [T17](#t17-side-conditions-of-family-borrows),
  [T16](#t16-read-footprint-and-two-run-laws); decision 29.
- **Links:** [`experiments/PositiveArrays/README.md`](../experiments/PositiveArrays/README.md).

### Projection

- **Question:** "From `v : Imm 'a (Ref A ⊗ Ref B)` … can we soundly get `Imm 'a A`?"
- **Answer:** "**No, not at the typed world as it stands.**" "The obstruction is the typed world's
  tag discipline" (`FrameLife`'s strict bound). Pointers for a follow-up are "not verified".
- **Status:** refuted (at the unrelaxed typed world); superseded in diagnosis by
  [Relaxed](#relaxed) and [FrameEnd](#frameend).
- **Key results:** `no_projection`, `callback_blocked`, `no_view_at_tag`.
- **Feeds:** [T4](#t4-same-lifetime-views-through-a-pointer).
- **Links:** [`experiments/Projection/README.md`](../experiments/Projection/README.md).

### Records

- **Question:** does `[CONF]` §5's "Pure constructs, like records or variants, would be
  straightforward to add" hold, and "what does field access through a borrow give?"
- **Answer:** "**The claim holds here.** Records and variants need no model change." Gaps: "*Cells:
  fields are not locations*" (a memory-model gap) and "*The indivisible `imm` witness*" (the
  same-lifetime projection).
- **Status:** proved; promoted (SPEC §5, with the encoding changed to "no trailing `1`").
- **Key results:** `immReborrow_recTy`, `outlives_recTy`, `reborrow_vDen_recTy`,
  `vX_outlives_recTy`, `affine_immReborrow`, `loadField_sem`, `swapField_sem`,
  `not_outlives_own_view`.
- **Not derived:** "The `Mut` analogue for a boxed field … is not attempted" (the fresh-lifetime
  form was later derived by Optics' `fstLens`/`splitMut`).
- **Feeds:** [#10] ([T18](#t18-affine-at-recursive-types)), [T4](#t4-same-lifetime-views-through-a-pointer).
- **Links:** [`experiments/Records/README.md`](../experiments/Records/README.md).

### Recursion

- **Question:** "Before `μ` is added to a type grammar (R4), does each piece hold for one fixed
  recursive type?"
- **Answer:** "Everything else in §6's P-μ and P-ν came out as the note says"; `Imm̲` at `μ` "needs
  an environment of payload types, one per bound variable"; the naive clause differs
  (`naive_ne`).
- **Status:** proved; superseded by [CBPVMu](#cbpvmu) (R4) and SPEC §6–§7.
- **Key results:** `listRel_unroll`, `listRel_outlives`, `listRel_local`, `freeAll_sem`,
  `build3Free_runs`, `stRel_iff`, `unfold_sem`, `take2Close_runs`, `immG_subst`,
  `immReborrow_unroll`, `naive_ne`, `wpTS_selfV_in`.
- **Feeds:** decision 7; [`docs/scope-recursion.md`](scope-recursion.md).
- **Links:** [`experiments/Recursion/README.md`](../experiments/Recursion/README.md).

### Relaxed

- **Question:** do FP and adequacy hold with `FrameLife.2` non-strict, and does the same-lifetime
  projection then go through?
- **Answer:** "**Relaxed FP and adequacy hold.**" "**The same-lifetime projection is still
  refuted, and the cause is not a strict inequality.**" Its key step, `frame_view_excluded`, is
  `[TR]` 6.38 applied at the frame's borrow.
- **Status:** proved (FP); merged as SPEC §4 ("No current rule uses this; it is kept for later
  same-lifetime views").
- **Key results:** `Relaxed.fundamentalProperty`, `Relaxed.adequacy`,
  `Relaxed.Projection.no_projection`, `frame_view_excluded`.
- **Feeds:** SPEC §4; [T4](#t4-same-lifetime-views-through-a-pointer).
- **Links:** [`experiments/Relaxed/README.md`](../experiments/Relaxed/README.md).

### Shifts

- **Question:** are the borrow axioms instances of one labelled-shift schema?
- **Answer:** the four label-introducing axioms are instances "by `rfl`"; "The source is returned
  exactly when its mode lacks contraction". "**The gap the schema predicts.** … **aff→unr**; the
  table has no axiom for the last, lending a `Mut` as an `Imm` (`axWithborMITy`). Rust has it
  (`&mut T → &T`)." "I have not derived `withborMI_compat` and have not verified that any
  obstruction is real."
- **Status:** partial (schema proved; the predicted rule open).
- **Key results:** `shiftTy`, `ret_iff_not_C`, `axWithborMITy` (stated type).
- **Feeds:** [T3](#t3-lending-a-mut-as-an-imm) (= strings K2′); [BorrowedClosures](#borrowedclosures).
- **Links:** [`experiments/Shifts/README.md`](../experiments/Shifts/README.md).

### TwoRun

- **Question:** (#39) can two-run properties "be had operationally, from the unary relation and
  the machine's determinism, or is a binary logical relation needed?"
- **Answer:** "The every-run half of #37 is operational: renaming plus freshness, no new
  relation. The two-run laws all reduce to one missing fact, the read footprint of typed
  computations." "A unary strengthening (A) is the cheaper candidate … A binary relation (B) is
  needed only if (A) fails."
- **Status:** partial; step 3 not attempted.
- **Key results:** `steps_rename`, `freshRun_det`, `fresh_run_image`, `wpTS_footprint_fresh`,
  `everyFreshRunFootprint`, `not_everyRunFootprint`, `not_everyRunFootprintRen`,
  `not_readFootprint`; stated `ReadFootprintTyped`.
- **Feeds:** [#41] ([T16](#t16-read-footprint-and-two-run-laws)); dream C1 (deforestation), P4.
- **Links:** [`experiments/TwoRun/README.md`](../experiments/TwoRun/README.md).

---

## Idea and scope documents

### ideas-handlers-and-borrows

- **Question:** is "**A stateful handler … a borrow presented through an interface**", with each
  kind of handler (by what it does with `k`) landing on an existing mechanism?
- **Answer:** "Brainstorm, not design. Nothing here is decided or proved." Proposed check: "state
  row 1 precisely: a stateful tail-resumptive handler, compiled as a borrow block plus direct
  calls, gives the same runs as its handler semantics."
- **Status:** open (untested).
- **Feeds:** [#170] ([T20](#t20-lexically-scoped-handlers-as-borrows)), [#18], K1.
- **Links:** [`docs/ideas-handlers-and-borrows.md`](ideas-handlers-and-borrows.md).

### ideas-pointers-and-lifetimes

- **Question:** family borrows with deref as a path step; smart pointers; cycles without giving up
  leak freedom; non-lexical lifetimes.
- **Answer:** "Brainstorm, not design." Family borrows: "No cell's witness contains another's, so
  the view-rejection lemmas do not apply. Possibly no model change". Truly non-lexical lifetimes:
  "A large model change, to be paid only if programs require it."
- **Status:** open; the family-borrow probe (`borrowAll`) is not built.
- **Feeds:** [T5](#t5-l2-borrowing-a-dynamic-length-structure-at-one-lifetime),
  [T4](#t4-same-lifetime-views-through-a-pointer), [#119], [#57].
- **Links:** [`docs/ideas-pointers-and-lifetimes.md`](ideas-pointers-and-lifetimes.md).

### scope-deep-freeze

- **Question:** would changing how frozen data is represented (option B: hand over the frame's
  `reb_α` image beside the printed cell) "let `↭` accept a same-lifetime interior view, and what
  would that cost"?
- **Answer:** "Pursue (ii), and probe it first as (iii)." The decisive step is `six38_img`, not
  built. L3/L2 by this route: "machine-checked to fail for `mut`" (`mut_lens_beside_parent_invalid`).
  "Main risk: row 4.8 has to carry the image."
- **Status:** open; dropped from the consolidation plan (`docs/consolidation-audit.md`: "Drop
  option B (never built)").
- **Key results (scratch, not committed):** `entry_valid`, `entry_heap`, `view_accepted`,
  `six52_H1_frame`, `reb_frame_absImm_local`, `mut_lens_beside_parent_invalid`.
- **Feeds:** [T4](#t4-same-lifetime-views-through-a-pointer); dream P2.
- **Links:** [`docs/scope-deep-freeze.md`](scope-deep-freeze.md).

### scope-recursion

- **Question:** where `μ`/`ν` and a delay monad go "without step-indexing", what each touches,
  which parts are risky.
- **Answer:** recommends a fork of CBPVWorld; `μ` as an impredicative least fixed point with an
  environment; `ν` as a direct greatest fixed point; the main risk R4. A direct
  `fix : !U(U(D A) ⊸ D A) ⊸ D A` "is **not derived, not verified**".
- **Status:** superseded by [Recursion](#recursion), [CBPVMu](#cbpvmu), SPEC §6–§7. Items still
  open: §2.2's `X` under a `U`-codomain (not implemented: "`U C` is a leaf for type variables");
  §4's direct `fix` and the cancellable `bind`; §7's downstream items.
- **Feeds:** [T12](#t12-non-tail-recursion-and-a-direct-fix), [T13](#t13-the-delay-type-approximations-and-codata-adequacy),
  [T15](#t15-recursive-types-and-folds-beyond-fshape), [#57]; decision 7.
- **Links:** [`docs/scope-recursion.md`](scope-recursion.md).

### dream-properties

- **Question:** "A list of candidate properties for the language, grouped by what they buy."
- **Answer:** "Nothing here is decided". Status column "as of 2026-09-25".
- **Status:** open list; partly stale (U2 says "there is no `μ`/`ν`", since built; F4's
  "second model" is replaced by divergence as an effect, decision 35).
- **Feeds:** F3 → [T7](#t7-conservative-extension-and-agreement-of-the-worlds); P2 →
  [T4](#t4-same-lifetime-views-through-a-pointer); C1 and P4 →
  [T16](#t16-read-footprint-and-two-run-laws); P6 → [#19]; C7 → [#14].
- **Links:** [`docs/dream-properties.md`](dream-properties.md).

### consolidation-audit

- **Question:** check the plan to consolidate the experiments into one world, claim by claim.
- **Answer:** the base is `CBPVMu`; "`Relaxed` transfers cleanly, but nothing uses it"; "`embed`
  transfers typings at `cbv` images only"; loose ends: outlives at `U C`/`Unk`, `NoMut`, the
  fold class, variants in place, `Affine` at `μ`, reuse tokens, same-lifetime projection, the
  delay type.
- **Status:** done (the work list became SPEC §3–§7); its §5 loose ends are indexed below.
- **Feeds:** [T2](#t2-an-outlives-rule-for-thunks-u-c), [T4](#t4-same-lifetime-views-through-a-pointer),
  [T7](#t7-conservative-extension-and-agreement-of-the-worlds), [T15](#t15-recursive-types-and-folds-beyond-fshape),
  [T18](#t18-affine-at-recursive-types), [#19], [#20], [#77].
- **Links:** [`docs/consolidation-audit.md`](consolidation-audit.md).

---

## Surveys

### prior-art-borrow-splitting

- **Question:** which laws L1–L5 (Imm distribution, multiplicative `Mut` split, lens access, a
  Seely law, borrowing computations) other systems validate, and at what model cost.
- **Answer:** "L1 at a fresh, shorter lifetime is printed" (`Imm̲` over `⊗`, 6.125, 6.131); "L1 at
  the same lifetime is refuted in the current model" (our `experiments/Projection`, `Relaxed`);
  "Deep immutability is not what blocks L1. … The obstruction is the representation". Options
  (a)–(e) for L1.
- **Status:** survey. Partly stale: L3 and L2 "at fresh lifetimes" are marked unverified there;
  Optics has since derived them (`fstLens` lifted, `splitMut`).
- **Feeds:** [T4](#t4-same-lifetime-views-through-a-pointer), [T5](#t5-l2-borrowing-a-dynamic-length-structure-at-one-lifetime),
  [FrameEnd](#frameend).
- **Links:** [`docs/prior-art-borrow-splitting.md`](prior-art-borrow-splitting.md).

### prior-art-effects-coeffects

- **Question:** ownership and borrowing expressed with grades or coeffects; capabilities as
  coeffects; the BoLo authors' own line.
- **Answer:** "The best-supported reading … is (1). 'Check out coeffects' most likely means: treat
  what a borrow needs as a context-side demand" (labelled inference); "There is no system that is
  both a coeffect system in the strict … sense *and* a borrowing system with lifetimes."
- **Status:** survey.
- **Feeds:** [#18], [#170], [Coeffects](#coeffects).
- **Links:** [`docs/prior-art-effects-coeffects.md`](prior-art-effects-coeffects.md).

### prior-art-memory-model

- **Question:** Q1–Q7 for the memory model (places vs cells, `split_at_mut`, a place algebra,
  allocation as an effect, lowering to bytes and Wasm, places vs streams, borrows as views) and
  Move.
- **Answer:** lists "What the literature does not seem to answer", including "Same-lifetime
  `split_at_mut` as a checked typing rule", "Arenas in a borrow calculus with leak-freedom",
  "Borrows as lenses with stated laws".
- **Status:** survey.
- **Feeds:** [T5](#t5-l2-borrowing-a-dynamic-length-structure-at-one-lifetime), [#94], [#15].
- **Links:** [`docs/prior-art-memory-model.md`](prior-art-memory-model.md).

### prior-art-optics

- **Question:** (#27) is a borrow "a linear optic whose residual is held by the lender for a
  lifetime"?
- **Answer:** "What BoLo prints is already the lens with a wand for a residual, guarded by a
  lifetime" (`[TR]` 6.65, 6.66); "Nothing connects optics to lifetimes or borrowing." Status
  table: H1, H4, H7 established; H2, H3, H5, H6 plausible; H8 open.
- **Status:** survey; tested by [Optics](#optics).
- **Links:** [`docs/prior-art-optics.md`](prior-art-optics.md).

### prior-art-rust-wishlists

- **Question:** what Rust's designers wish they had done, mapped onto borrow-core.
- **Answer:** lessons, among them "**Settle self-reference before the iteration interface
  freezes.** … can a generator or future hold a borrow across a suspension?" and "**Never trade
  away leak freedom for convenience.**"
- **Status:** survey.
- **Feeds:** [T1](#t1-the-spanning-lend-k1), [#52], [#18].
- **Links:** [`docs/prior-art-rust-wishlists.md`](prior-art-rust-wishlists.md).

### prior-art-sessions

- **Question:** (#68) are borrows, iterators, handlers and futures instances of one session
  mechanism; par; modes.
- **Answer:** "S1 holds for three of the four and only rhymes for the fourth. *(ours)*" Handlers
  join "if `ν` admits one position it excludes today: an observation that takes an input";
  "Borrows are different. … None of what makes a borrow sound … is in the session type." "`⅋` as
  a former fails the unlock tests in the sequential setting."
- **Status:** survey; its top-ranked experiment is [#96].
- **Feeds:** [#96] ([T8](#t8-observations-that-take-input-k2)), [#68], [T14](#t14-codata-positions-of-x-beyond-nuok).
- **Links:** [`docs/prior-art-sessions.md`](prior-art-sessions.md).

---

## Designs with open kernel items

### effects-scoping

- **Question:** scope #18: which effect ideas the core already has, and where elaboration breaks.
- **Answer:** "**Most of #18 surfaces what the core already has.**" "a handler's meaning is its
  elaboration into core". "It breaks in exactly K1–K5, and each of those already has an issue or
  an experiment." Its §9 lists what it has "not established", including "That the projection
  form of §7.3 has a derived type in the core" and the handler laws beyond one effect.
- **Status:** design; S1 built (SPEC §18).
- **Open kernel items:** K1 → [T1](#t1-the-spanning-lend-k1); K2 → [T8](#t8-observations-that-take-input-k2);
  K3 → [T9](#t9-destructors-that-perform-io-or-fail-k3); K4 → [T10](#t10-early-exit-from-a-kernel-fold-k4);
  K5 → [T11](#t11-structural-and-borrowed-descent-for-rec-k5); projection operations →
  [T21](#t21-the-derived-type-of-projection-operations).
- **Links:** [`docs/effects-scoping.md`](effects-scoping.md); [#151], decisions 48–53.

### strings-slices-design

- **Question:** strings and slices end to end: types, API, and "the memory model this forces".
- **Answer:** "**Kernel.** Six additions. Each is a constant with an ordinary term and one
  compatibility lemma." Stages S1–S5 built. "Deliberately left out": "An `imm` reborrow of a
  `mut` family … a natural K2′ once K2 exists."
- **Status:** design; S1–S5 built. Left: strings K2′ ([T3](#t3-lending-a-mut-as-an-imm)), K2's
  side conditions ([T17](#t17-side-conditions-of-family-borrows)), lists in `for` ([#57]).
- **Links:** [`docs/strings-slices-design.md`](strings-slices-design.md); SPEC §8, §9, §16, §17.

---

## Open theoretical problems

Deduplicated across every source above and every `### Open` of `SPEC.md`. Each problem has one
issue; related issues are named. "Not derived" means no proof and no machine-checked
obstruction exist unless a Lean name is given.

| # | Problem | Issue |
|---|---|---|
| T1 | The spanning lend (K1) | [#172] |
| T2 | An outlives rule for thunks `U C` | [#173] |
| T3 | Lending a `Mut` as an `Imm` (strings K2′) | [#174] |
| T4 | Same-lifetime views through a pointer | [#175] |
| T5 | L2 over a dynamic-length structure | [#176] |
| T6 | Widening promotion | [#9] |
| T7 | Conservative extension, agreement of the worlds | [#177] |
| T8 | Observations that take input (K2) | [#96] |
| T9 | Destructors that perform I/O or fail (K3) | [#162] |
| T10 | Early exit from a kernel fold (K4) | [#178] |
| T11 | Structural and borrowed descent for `rec` (K5) | [#179] |
| T12 | Non-tail recursion, a direct `fix` | [#12] |
| T13 | Delay approximations, codata adequacy | [#180] |
| T14 | Codata positions of `X` beyond `NuOk` | [#181] |
| T15 | Recursive types and folds beyond `FShape` | [#182] |
| T16 | Read footprint and two-run laws | [#41] |
| T17 | Side conditions of family borrows | [#183] |
| T18 | `Affine` at recursive types | [#10] |
| T19 | Tasks holding borrows at different lifetimes | [#52] |
| T20 | Lexically scoped handlers as borrows | [#170] |
| T21 | The derived type of projection operations | [#160] |

### T1. The spanning lend (K1)

- **Statement.** A rule that lends a place across observations of codata, e.g. `withborLoop :
  Ref A ⊸ (∀'x ⊏ ⊓Δ. Mut 'x A ⊸ F(U(Loop (['x] B) R))) ⊸ F(U(Loop (Ref A ⊗ B) (Ref A ⊗ R)))`,
  sound with FP and adequacy. Equivalently: a borrow held across a suspension (a `yield`,
  `await`, or a projection held across either).
- **Origin.** `experiments/LoopBorrow` (O1); SPEC §5 and §14 ("a lend that spans observations
  needs a model change that is not verified"); `docs/effects-scoping.md` §0 K1, §1.2 item 2.
- **Known partial results.** Refolding is a theorem (`wpTS_M_refold`); the Kripke step fails at
  an arising consumer frame (`refoldKripke_false`, `refold_fails_at_consumer_frame`); with a
  freeze it closes (`refoldKripkeD`), but no run installs one (`not_markerInstallable`). The
  README's proposal: "a **register of open lends** in `wpTS` … `↭`'s `mut` clause would be read
  modulo the register … This is a design reading of the paper, not a Lean result." Relabelling
  at a fresh `α′` needs parametricity at `U`, "not pursued".
- **Why it matters.** Opaque codata holding a borrow: a library generator over a borrow, a div
  callee with a borrow parameter ("For 'no function coloring' that is the case that matters"),
  async tasks that borrow ([#52] phase 5), effects S4/S5, external iteration over linked data
  per [#57]'s reframe.
- **Issue:** [#172]. Related: [#162], [#52], [#170], [#57].

### T2. An outlives rule for thunks `U C`

- **Statement.** `VOutlives` has no rule at `U C` or `Unk` (`thunk_not_outlives`). Find a sound
  rule (or a typed capture bound) under which a thunk whose captures outlive `@a` satisfies
  `U C ⊐ @a`, or establish that `[@d] U C` is the only route.
- **Origin.** `docs/consolidation-audit.md` §5; `experiments/CBPVWorld` "What remains
  restricted"; `experiments/CoeffectsStrict` (`thunk_not_outlives`, test case 2);
  `experiments/Optics` (affine composition not built); `experiments/Places`,
  `experiments/LeafPlaces` (results with `⊸`/`∀`/`Unk`); [#170]'s comment.
- **Known partial results.** The box works: `[]I` boxes codata as it boxes data (`d_box_codata`),
  and "the box is the only way a thunk crosses a scope" (CoeffectsStrict). Not derived: "Whether
  the frame end of `withbor` (6.64) needs any change for a boxed thunk that holds a reborrowed
  view". **(inferred)** A rule on `U C` alone meets the obstruction `docs/scope-recursion.md`
  §3.1 and `EnvCheck` record: the type does not determine the captured resource.
- **Why it matters.** Today `[]I` cannot box a context holding an unboxed thunk; family borrows
  and `withborS` exclude thunk results; `foldImm`'s result must outlive every lifetime; lens ∘
  linear prism is not built; two opaque lending sources cannot be zipped (LoopBorrow). [#170]'s
  comment names it as the rule a continuation capturing borrows needs.
- **Issue:** [#173]. Related: [#170], [T1](#t1-the-spanning-lend-k1).

### T3. Lending a `Mut` as an `Imm`

- **Statement.** A compatibility lemma for `axWithborMITy`, `Mut @a T ⊸ (∀'x ⊏ ⊓Δ. Imm 'x T ⊸
  ['x] T₂) ⊸ Mut @a T ⊗ T₂` (Rust's `&mut T → &T`), and its family form, strings K2′:
  `[Mut 'c A] ⊸ (∀'d. [Imm 'd A] ⊸ ['d] T) ⊸ …`.
- **Origin.** `experiments/Shifts` ("The gap the schema predicts"); `experiments/PositiveArrays`
  Open; SPEC §9 Open; `docs/strings-slices-design.md` §5.2.
- **Known partial results.** Shifts: the lemma would be "anti-frame + `Imm` frame"; it "does not
  compose as stated" because `wpTS_I_frameX`'s `hQ` asks `Ext`-stability of a postcondition
  holding `ptoMutS l α₀ ls'' _ ─⋆ Q`; route: "a variant of `wpTS_I_frameX` whose `hQ` is stated
  at the drop step". PositiveArrays: K2′ is "the same list induction with `withbor3`'s anti-frame
  per leaf, and was not attempted". Neither derived; no obstruction verified.
- **Why it matters.** `peek` and `sort` in `lib/slice.bc` take a filler meanwhile; `imm` access
  through `mut` capabilities and handler state.
- **Issue:** [#174].

### T4. Same-lifetime views through a pointer

- **Statement.** From `Imm @a (Ref A ⊗ Ref B)` obtain `Imm @a A` (L1 at the same lifetime), and
  the `Mut` analogues (L3, L2). In the current model these are excluded by `↭` at the
  projecting run (`imm_view_rejected`, `mut_view_rejected`; `frame_view_excluded` via `[TR]`
  6.38). The open question is whether a model extension admits them: option B of
  `docs/scope-deep-freeze.md`, first `six38_img`.
- **Origin.** `experiments/Projection`, `Relaxed`, `FrameEnd`; `docs/scope-deep-freeze.md`;
  SPEC §5 Open; dream P2; `docs/prior-art-borrow-splitting.md` §5.1.
- **Known partial results.** Entry side of option B costs nothing (`entry_valid`,
  `entry_heap`); 6.52's H1 and 6.59's closing step localize (`six52_H1_frame`,
  `reb_frame_absImm_local`), scratch only. `mut` by that route is machine-checked to fail
  (`mut_lens_beside_parent_invalid`, scratch, not committed). Decision 5 routes around it (places by disjointness), and
  effects-scoping §7.3 recommends against a kernel extension. SPEC §4 keeps the relaxed
  `FrameLife` "for later same-lifetime views".
- **Why it matters.** `&'a self.field` through a `Box`; external iterators over borrowed boxed
  structures (`docs/scope-recursion.md` §7); operations returning a borrow into handler state.
- **Issue:** [#175]. Related: [#57], [#160].

### T5. L2: borrowing a dynamic-length structure at one lifetime

- **Statement.** `AllAtOnceGoal E`: a closed value of type `L_E ⊸ (∀'c ⊏ ⊓Δ. (μX. 1 ⊕ (Mut 'c E
  ⊗ X)) ⊸ ['c] T) ⊸ L_E ⊗ T`; more generally the family borrow of every cell a recursive
  structure reaches (`borrowAll`).
- **Origin.** `experiments/Optics` (Traversal.lean); `docs/ideas-pointers-and-lifetimes.md`
  (*Family borrows*); `docs/prior-art-borrow-splitting.md` §5.4; consolidation audit §5 ("nothing
  has been built for them").
- **Known partial results.** Static shapes: `withborS`, `withborF2`. Arrays at a run-time length:
  strings K2 (`sliceBorrowM_compatX`) by `wpTS_M_frameList`. Per-element: IterMut (`d_iterMut`,
  `iterMut_shape`). **(inferred)** The array proof's list induction over places is the candidate
  technique, with the places found by a fold.
- **Why it matters.** `IterMut` over linked data at one lifetime; the proposed way around T4.
- **Issue:** [#176].

### T6. Widening promotion

- **Statement.** (a) Promotion's `!Γ` widened to "every live slot persistent"; (b) SPEC §2's
  "Promotion at every value. Needs `wp` at a value to leave the resource in place; not proved."
- **Origin.** SPEC §10 Open, §2 Open; `experiments/Grades`.
- **Known partial results.** (a) is sound: `bangThunkF_compatG`, `promote_int`; measured "≈
  −23" lines with no grades. Conflict noted: "(b) and (c) conflict: if `DeadP` drops `Imm`,
  promotion needs its own 'live slots persistent' predicate back". (b) not derived.
  CoeffectsStrict: promotion at a *computation* would need `!(T A) → T(!A)`, which `alloc`
  refutes.
- **Issue:** [#9].

### T7. Conservative extension and agreement of the worlds

- **Statement.** Every baseline derivation is a derivation of the extended calculus "and means the
  same thing" (F3), stated as a theorem; and agreement of the CBPV world with the library's typed
  world on translated types (a `vX_eq_…`-style check).
- **Origin.** SPEC §2 Open; `experiments/CBPVWorld` Open; `experiments/CBPVCore` Open (the
  syntactic CBV embedding); `docs/consolidation-audit.md` §4 ("The entry has to say which
  statement counts as 'preserved'"); dream F3.
- **Known partial results.** `embed` and `adequacy_of_derivesWf`; `vX_eq_vC_fun` in
  CBPVSplit/CBPVCore (by construction). Agreement "would first need a translation of worlds and
  record lists along `cbv`".
- **Why it matters.** It is what "extends BoLo" means as a theorem.
- **Issue:** [#177].

### T8. Observations that take input (K2)

- **Statement.** Allow a `ν` observation `A ⊸ (observation tree)` with `X ∉ A` (a sink) and prove
  `unfold` sound there.
- **Origin.** SPEC §7 Open; `docs/prior-art-sessions.md` §6.5 item 1; `experiments/LoopBorrow`
  (*Sink observations*); effects-scoping K2.
- **Known partial results.** LoopBorrow's cost estimate: "An `X`-free input leaves `Φ_C`
  monotone, so no step index is needed. The estimate is a few hundred lines". Not built.
- **Issue:** [#96]. Related: [#162], [#68].

### T9. Destructors that perform I/O or fail (K3)

- **Statement.** Whether a host resource type gets an implicit destructor that performs I/O or
  can fail, and what a failing one does, with `dtor_wf` at the extern context.
- **Origin.** SPEC §12 Open, §11 Open; effects-scoping K3, §7.10.
- **Known partial results.** "The platform draft (§2.3) calls its kernel side 'small'"; S1
  rejects an abort while a class-3 value is live.
- **Issue:** [#162].

### T10. Early exit from a kernel fold (K4)

- **Statement.** A `raise` inside a `fold_own`/`fold_imm` algebra that stops the fold: a constant
  with a machine step and its compatibility lemma.
- **Origin.** SPEC §18 Open; effects-scoping §1.2 item 4, E8; `corpus/pending/raise-in-fold.bc`.
- **Known partial results.** Such an algebra is rejected today; the propagating form (a sum to
  the end of the fold) needs nothing new.
- **Why it matters.** Fallible folds over `μ` data; [#168] (errors as a control effect).
- **Issue:** [#178].

### T11. Structural and borrowed descent for `rec` (K5)

- **Statement.** Total recursion by size that the checker can see (R8), and recursion over a
  borrowed tree at one lifetime (R9).
- **Origin.** effects-scoping §0 K5, §1.2 item 7; rec-effect R8, R9 (branch `iteration-design`).
- **Known partial results.** Borrowed descent as a fold exists: `foldImm` terminates by witness
  size (`withload_sized`). [#72] (sized types) would "surface the borrowed fold's witness-size
  measure". Meanwhile `fuel` and data-sized drivers give totality.
- **Issue:** [#179]. Related: [#158], [#72].

### T12. Non-tail recursion and a direct `fix`

- **Statement.** A `bind` on `D` with closable continuations, or explicit `μ`-list stacks; and
  the direct `fix : !U(U(D A) ⊸ D A) ⊸ D A`, "not derived, not verified".
- **Origin.** SPEC §7 Open; `docs/scope-recursion.md` §4; `experiments/CBPVMu` (*Not done*).
- **Known partial results.** `fixD_compatX`; the naive guard is refuted (`naive_not_sem`); SPEC
  §14's delay bind sequences loops.
- **Issue:** [#12].

### T13. The delay type: approximations and codata adequacy

- **Statement.** `WpChainCommutes`: `wpTS` commutes with the intersection of a decreasing chain of
  postconditions, which gives `⟦D A⟧ = ⋂ₙ approx n` (`delayRel_iff_approxLim`). Also: adequacy
  for `D` without `close` (a `theorem32` with a non-pure postcondition), and stream adequacy
  beyond `Stream 1`.
- **Origin.** SPEC §7 Open; `experiments/CBPVMu` Step 1; `docs/scope-recursion.md` §4.
- **Known partial results.** `delayRel_le_approxLim`; `approxLim_le_delayRel` under the
  hypothesis; "Over a finite witness type a decreasing chain commutes with `∃`
  (`exists_forall_of_finite`); over `ℕ` it does not (`not_exists_forall`)". Not derived; no
  obstruction verified. Only `take_runs` at `Stream 1`.
- **Issue:** [#180].

### T14. Codata: positions of `X` beyond `NuOk`

- **Statement.** Coiteration's map where `X` occurs under a `Ref`, a borrow, `!` or `[@a]` in an
  observation result (the sink position is T8).
- **Origin.** SPEC §7 Open ("The relation is monotone wherever `X` avoids `Mut` payloads; what is
  missing is coiteration's map at those positions"); `experiments/LoopBorrow` (two opaque lending
  sources need "`X` under `[@a]` in an observation result").
- **Known partial results.** Monotonicity is available; the map is not built.
- **Issue:** [#181]. Related: [T8](#t8-observations-that-take-input-k2).

### T15. Recursive types and folds beyond `FShape`

- **Statement.** (a) `X` under a `U`-codomain (W-types, free monads through `U`); (b) folds for
  `X` under a `Ref` of a compound (`L′ = μX. 1 ⊕ Ref (N ⊗ X)`), a borrowed fold at `Ref S` with
  `X` inside `S`, nested `μ`; (c) a borrowed fold whose result borrows into the structure (today
  "`R` must outlive every lifetime").
- **Origin.** `experiments/CBPVMu`; `docs/consolidation-audit.md` §5; SPEC §6; CoeffectsStrict
  §3 and §8 item 3 (general-arity handlers "need `X` under `U` in `FShape` … the one kernel
  extension on this path"); `docs/scope-recursion.md` §2.2.
- **Known partial results.** `foldImm`, `foldOwn`, `foldReuse` at `FShape`; `MapMut`'s `mapInc`
  over `L′` by hand; the block view puts the common list in `FShape`. Not derived for (b):
  "I have not derived such a rule and have not verified that any obstruction is real."
- **Issue:** [#182]. Related: [#32], [#18].

### T16. Read footprint and two-run laws

- **Statement.** `ReadFootprintTyped`: the run `wpTS` exhibits for a typed computation touches
  only its resource and fresh locations. With it: `PureFn`'s value clause, effectful fusion, the
  Optics laws on every run, map fusion/fission, deforestation (C1). Also the renamed footprint on
  every (including stale) run of a well-typed program, runs with array steps under block
  renaming, and fold/unfold laws that step through the heap.
- **Origin.** `experiments/TwoRun`; `experiments/FrameTheorems`; `experiments/Optics`;
  `experiments/PositiveArrays`; `experiments/CoeffectsStrict` §5; dream C1, P4.
- **Known partial results.** `wpTS_footprint_fresh`; `not_readFootprint` (at an untyped term);
  [#41]'s comments: a syntactic reachability route on the paper side (`derivesWf_runIn`) and
  `Core/Stale.lean`. Route (B), a binary relation, is also the route to lifetime parametricity
  (P4).
- **Issue:** [#41].

### T17. Side conditions of family borrows

- **Statement.** Whether `slice_borrow`'s conditions ("`A` and `B` outlive a lifetime of `Δ`"),
  `withborF2`'s, and `withborS`'s (leaves and result lifetime-free: not `Imm @e`, `Mut @e`,
  `[@e]`) are needed.
- **Origin.** SPEC §9 Open, §5, §17 Open; `experiments/PositiveArrays`; `experiments/Places`,
  `experiments/LeafPlaces`.
- **Known partial results.** The proofs use them for the rebox at outer frames (6.60). "not known
  to be needed" (SPEC §9); "not derived, not known to be blocked" (SPEC §5).
- **Why it matters.** `borrow mut` of a `buf (text 't)` inside the views' block is rejected
  (SPEC §17 Open).
- **Issue:** [#183]. Related: [#11].

### T18. `Affine` at recursive types

- **Statement.** A lemma that `Imm̲ 'b` of a `μ`-typed field is droppable (e.g. `Imm̲ 'b N =
  μY. 1 ⊕ Y` needs a recursive drop), so projection past an unboxed `μ`-typed field is available.
- **Origin.** SPEC §5; `docs/consolidation-audit.md` §5.
- **Issue:** [#10].

### T19. Tasks holding borrows at different lifetimes

- **Statement.** "a scheduler holding tasks whose borrows are at different lifetimes needs
  existential lifetimes or scoped spawning" (CoeffectsStrict §6); [#52] phase 5's
  "lifetime-forest question".
- **Known partial results.** Scoped tasks and per-poll lends work (LoopBorrow
  `lend-config-imm.bc`).
- **Issue:** [#52].

### T20. Lexically scoped handlers as borrows

- **Statement.** A Ξ-style fragment of answering handlers translates into BoLo + `!` preserving
  typing, with effect safety a corollary of FP; and a separating program BoLo + `!` types that Ξ
  cannot express.
- **Origin.** [#170]; `docs/ideas-handlers-and-borrows.md`; `experiments/Coeffects`.
- **Issue:** [#170].

### T21. The derived type of projection operations

- **Statement.** `let v = m.get(k); S` as a projection at a fresh lifetime: "That the projection
  form of §7.3 has a derived type in the core. I have argued it from `withload`'s shape … I have
  not written the derivation."
- **Origin.** `docs/effects-scoping.md` §7.3, §9.
- **Issue:** [#160].

### Also open, filed under their issues

- Session types as the unifying abstraction: `docs/prior-art-sessions.md` answers S1–S6 as a
  survey; no Lean. [#68].
- The sink position (T8) is its top-ranked experiment.

### Not derived, no consumer

Recorded so they are not rediscovered; no design depends on them, so no issue is filed.

- `Mut 'x U ⊸ Mut 'x U ⊗ Mut 'x U`, parallel contraction of a `Mut` demand (Coeffects §2,
  CoeffectsStrict §2.3: "not derived, no obstruction verified. BoLo's `○` composes two `mut`
  cells at one location, so the obstruction is not a disjointness of the resource algebra").
- L4, `Imm_α (A & B) ≅ Imm_α A ⊗ Imm_α B` ("If pursued, it would be a new result",
  `docs/prior-art-borrow-splitting.md` §5.3).
- A linear prism typed `Ref A ⊕ Ref B ⊸ G ⊸ (Ref A ⊕ Ref B) ⊗ (T ⊕ 1)` with linear `G` (Optics:
  "I have not derived it").
- Digging `!A ⊸ !!A` and same-index `[@a]A ⊸ [@a][@a]A`: valid in the model (`bang_idem`,
  `box_idem`), "one compatibility lemma if a program needs it".

### Checked and not open

- **Borrowed closures, stage 2.** Superseded by `!T` (decision 3; SPEC §2 *Closures, in these
  terms*); what stopped it is machine-checked (`envShape_unlinked`, `envValue_unlinked`).
- **L3 and L2 at fresh lifetimes.** Derived (`fstLens` lifted, `splitMut`, Optics).
- **Strings K2** (cell-free family borrow). Proved and promoted (`sliceBorrowM_compatX`,
  `sliceBorrowI_compatX`).
- **Non-strict frame lifetimes.** Proved sound and merged (SPEC §4).

---

## Settled

Results later work can rely on. Each is machine-checked unless marked.

- **Data/codata is a real duality.** `μ` on value types, `ν` on computation types; fold β and
  uniqueness at every `FShape` (`fold_beta`, `fold_unique`), unfold β for any step
  (`unfold_next`, `unfold_close`), uniqueness for pure total steps (`unfold_unique`)
  (CoeffectsStrict). "Real on the data/codata row" (Coeffects).
- **Scope is a third axis.** "Owned versus borrowed at `'a` is a resource algebra with a global
  store invariant. It is not an equational structure"; the axes "meet the scope axis only through
  the Fundamental Property" (CoeffectsStrict; the account is a paper argument, its laws are
  checked).
- **Effect/coeffect is a direction, not a duality.** "`FU` is not the coeffect comonad"; effects
  × coeffects has no canonical law here, and "promotion only at values is the correct response,
  not a gap" (`alloc` refutes `!(T A) → T(!A)`, SPEC §2). A `Mut` capability is linear state, an
  effect; an `Imm` demand is the reader comonad (`copy_diag`, `copy_counit`).
- **A handler of a finite-arity signature is the fold of its free model** (`handle_return`,
  `handle_write`, `handle_unique`).
- **A borrow block is a tail-resumptive handler with no operations** (Coeffects; printed rule
  shapes plus `KDem.elab`).
- **The typed world factors through CBPV** (`vX_eq_vC_fun`), and the CBPV core with the full
  resource calculus has FP and adequacy (`fundamentalC`, `adequacyC`); BoLo embeds (`embed`,
  `adequacy_of_derivesWf`).
- **The typed world's choosers and invariants accept `μ` unchanged**, and a borrowed fold
  terminates by witness size (`withload_sized`, `foldImm_compatX`).
- **`ν` and guarded recursion need no step index** (`fixD_compatX` by coinduction); a
  `later`-wrapped step is not a guardedness condition (`naive_not_sem`).
- **Disjoint places borrow at one lifetime by derivation**, statically (`withborM2_wf`,
  `withborS_wf`) and at a run-time length (`sliceBorrowM_compatX`, `sliceBorrowI_compatX`); a
  borrowed family splits (`vP_fam_split`).
- **Records and variants need no model change** (Records); nothing makes a location hold a whole
  record (LeafPlaces).
- **Same-lifetime views through a pointer are excluded by `↭` in the current model**
  (`imm_view_rejected`, `mut_view_rejected`, `frame_view_excluded`); `mut` views cannot sit
  beside their parent (`mut_lens_beside_parent_invalid`, scratch). Whether an extension admits
  them is T4.
- **A closure former's borrowed image is not determined by its type** (`envShape_unlinked`,
  `envValue_unlinked`); `!T` has image `∅`.
- **The per-observation lend needs no new rule**, and a pull-form lending yield is excluded
  (`not_lendingYield_mut`, `not_lendingYield_imm`).
- **Affine drops are elaboration** (`ADerives.elab`); grades are not net-negative as a context
  coordinate and erase at `0` (`cderives_iff_graded`, `prog_runs_any`).
- **Ownership kinds are adjoint modes** at the model (`weaken_sound`, `dup_sound`,
  `mode_immReborrow`).
- **Frame and fresh-run footprints** (`wpTS_footprint`, `wpTS_footprint_fresh`,
  `freshRun_det`); an `unsafe` write through `Imm` cannot meet its contract (`imm_call_keeps`).
- **Borrows instantiate one optic interface with Rezip on every run** (`Optic.runs`,
  `lift_cell`); optics are a parallel, not the abstraction (decision 22).

[#9]: https://github.com/empath-nirvana/borrow-core/issues/9
[#10]: https://github.com/empath-nirvana/borrow-core/issues/10
[#11]: https://github.com/empath-nirvana/borrow-core/issues/11
[#12]: https://github.com/empath-nirvana/borrow-core/issues/12
[#14]: https://github.com/empath-nirvana/borrow-core/issues/14
[#15]: https://github.com/empath-nirvana/borrow-core/issues/15
[#18]: https://github.com/empath-nirvana/borrow-core/issues/18
[#19]: https://github.com/empath-nirvana/borrow-core/issues/19
[#20]: https://github.com/empath-nirvana/borrow-core/issues/20
[#32]: https://github.com/empath-nirvana/borrow-core/issues/32
[#41]: https://github.com/empath-nirvana/borrow-core/issues/41
[#52]: https://github.com/empath-nirvana/borrow-core/issues/52
[#57]: https://github.com/empath-nirvana/borrow-core/issues/57
[#68]: https://github.com/empath-nirvana/borrow-core/issues/68
[#72]: https://github.com/empath-nirvana/borrow-core/issues/72
[#77]: https://github.com/empath-nirvana/borrow-core/issues/77
[#79]: https://github.com/empath-nirvana/borrow-core/issues/79
[#94]: https://github.com/empath-nirvana/borrow-core/issues/94
[#96]: https://github.com/empath-nirvana/borrow-core/issues/96
[#119]: https://github.com/empath-nirvana/borrow-core/issues/119
[#151]: https://github.com/empath-nirvana/borrow-core/issues/151
[#158]: https://github.com/empath-nirvana/borrow-core/issues/158
[#160]: https://github.com/empath-nirvana/borrow-core/issues/160
[#162]: https://github.com/empath-nirvana/borrow-core/issues/162
[#168]: https://github.com/empath-nirvana/borrow-core/issues/168
[#170]: https://github.com/empath-nirvana/borrow-core/issues/170
[#172]: https://github.com/empath-nirvana/borrow-core/issues/172
[#173]: https://github.com/empath-nirvana/borrow-core/issues/173
[#174]: https://github.com/empath-nirvana/borrow-core/issues/174
[#175]: https://github.com/empath-nirvana/borrow-core/issues/175
[#176]: https://github.com/empath-nirvana/borrow-core/issues/176
[#177]: https://github.com/empath-nirvana/borrow-core/issues/177
[#178]: https://github.com/empath-nirvana/borrow-core/issues/178
[#179]: https://github.com/empath-nirvana/borrow-core/issues/179
[#180]: https://github.com/empath-nirvana/borrow-core/issues/180
[#181]: https://github.com/empath-nirvana/borrow-core/issues/181
[#182]: https://github.com/empath-nirvana/borrow-core/issues/182
[#183]: https://github.com/empath-nirvana/borrow-core/issues/183
