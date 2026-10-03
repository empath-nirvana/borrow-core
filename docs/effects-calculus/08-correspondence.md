# 08 · Correspondence: existing Lean, SPEC, surface, lowering

This section relates the calculus of 02-07 to what exists. It does four things:

1. states the three correspondence results it owns, T-CONS, T-ELAB and T-LOWER (§1);
2. gives, for every K, D, L and T id of [00-structure.md](00-structure.md), the declarations
   that realise it today and their fate (§2), and, in the other direction, every effect-related
   Lean artifact with its fate and the section that governs it (§3);
3. lists the SPEC entries the calculus needs and the decisions it supersedes or revises (§4),
   the obligations it puts on the surface (§5) and on the lowering (§6), and what keeps the
   door open for threads (§7);
4. checks the calculus against the "not an approximation" checklist, id by id (§8), and names
   the programs that exercise each construct (§9).

It defines no object beyond the SPEC entry ids `E-*` (listed in §4.2, drafted in §4.4; indexed in 00 §3.5). Every other
object is 00's; every open question it cites, including the three it raises (§10), is boxed in
[99](99-open-questions.md).

Marks are 00 §0.1's. **[Lean]** claims cite `file:line` in this worktree (`main` plus the
audit); a claim about another branch names the branch. **[read]** is a reading of the cited
file. Nothing here was built or run.

---

## 0. The vocabulary of fates

| fate | meaning | needs |
|---|---|---|
| **keep** | the declaration stays, with its statement | nothing |
| **re-index** | the declaration stays and its statement is read at `W`; at `σ = []` it is the declaration itself (T-NIL) | the `W` SPEC entry (§4.2, E-W) |
| **change** | the definition changes | a SPEC entry before kernel work (00 §0.1) |
| **promote** | moved from an experiment into `Core/`, possibly restated | a SPEC entry naming it |
| **rebuild** | the result is wanted, but its carrier is not `CDerives`/`W`; it is proved again over the kernel, the experiment kept as the guide | the SPEC entry of the construct |
| **abbreviate** | the declaration becomes a definition in terms of the general construct, its compatibility lemma a corollary (decision 20) | the general construct |
| **retire** | deleted, in the same change that lands its replacement (decision 20) | the replacement; each retirement below is **conditional** on the re-index of 05 landing (OQ-8 settled, D-W adopted) |
| **evidence** | kept as the model of a sibling calculus; cited, never transported | OQ-5 |
| **relabel** | kept, its documentation corrected | a documents pass |

A fate is a plan, not a judgement of the declaration. In particular "retire" says the
declaration's content moves into `W`; it does not say the declaration was wrong.

---

## 1. The results this section owns

### T-CONS: conservativity

- **Form.** Let `⊢₀` be `CDerives` as built (`Core/Fundamental.lean:60`) and `⊢` the judgement of
  03 (O-JDG). Let `cC` be the relation as built (`Core/Relation.lean:154`) and `𝒞⟦−⟧_W` the
  relation of 05 (D-REL).

  ```
  (T-CONS.1, inclusion)   ∀ Δ Γ e j.  Δ; Γ ⊢₀ e : j  ⟹  Δ; Γ ⊢ e : j
  (T-CONS.2, base case)   ∀ C ρ ls δ e.  𝒞⟦C⟧_{(ρ, ls, [])} δ e  ⟺  cC C ls δ e ρ       (T-NIL)
  (T-CONS.3, statements)  every theorem of Core quantified over ⊢₀ and cC holds with the same
                          statement over ⊢ and 𝒞⟦−⟧_{(−,−,[])}; in particular
                          fundamentalC, adequacyC, fundamentalD, adequacyD, adequacyD_obs,
                          total_every_alloc, total_every_run, total_no_infinite_run,
                          io_every_run, externs_loop_every_run.
  (T-CONS.4, BoLo)        ∀ Δ Γ e T.  DerivesWf Δ Γ e T  ⟹  Δ; cbvCtx Γ ⊢ e : cbv T,
                          and adequacy_of_derivesWf keeps its statement.
  ```

  T-CONS.1 holds rule by rule: every rule of `⊢₀` is a rule of `⊢` or an instance of one. The
  instances are the borrow constants (K-BOR): `withbor1`…`sliceBorrowI` are `bor_k[∅]`, and the
  `*U` constants are `bor_k[Σ]` at a row with `Row.Unwind` (abbreviations, §2.2).
- **Uses.** O-JDG, O-REL, K-BOR, D-REL, T-NIL, T-FP.
- **Today.** The *Baseline* paragraphs of SPEC §14 (`SPEC.md:1472`), §18 (`:2244`), §19
  (`:2780`), §20 (`:3114`), §21 (`:3264`), §22 (`:3437`), §23 (`:3579`) each assert T-CONS.3 for
  their entry, in prose. The theorems: `fundamentalC` (`Core/Fundamental.lean:434`), `adequacyC`
  (`:590`), `adequacyD` (`Core/Demonic.lean:312`), `adequacyD_obs` (`Core/EffPrograms.lean:41`),
  `total_every_alloc` (`Core/Totality.lean:40`), `total_every_run` (`:64`),
  `total_no_infinite_run` (`:223`), `io_every_run` (`Core/Stdio.lean:694`),
  `externs_loop_every_run` (`:768`). T-CONS.4: `embed` (`Core/Embedding.lean:235`),
  `adequacy_of_derivesWf` (`:326`). Status: **new** as a named result.
- **Slices.** T-NIL (05), T-FP (07).
- **Depends on.** D-REL at `σ = []` equal to `cC` by T-NIL: by definition at the clauses that
  read no extension, by a per-row proof at `U`, `share` and `KapRel`, which is unknown (OQ-58);
  K-BOR's abbreviation of the existing constants (03).
- **Open.** OQ-8 (no re-index, hence nothing to conserve, until it is settled), OQ-13 (if rows
  become an object, T-CONS.1 is an inclusion into a larger judgement, unchanged in form).
- **Obligation.** T-CONS.1: **mechanical**, one case per rule; the step most likely to be
  non-mechanical is the abbreviation of `withloadU`, whose compatibility lemma
  (`withloadU_compatX`, `Core/EffBorrow.lean:548`) uses 6.150, which T-FRAME does not yet lift
  (00 §5.1). T-CONS.2: **mechanical** at the clauses that read no extension (by `rfl`);
  **unknown** at `U`, `share` and `KapRel`, where it is OQ-58's `NilAgreesU` at each introduction
  row (05 T-NIL). T-CONS.3: **mechanical** from T-CONS.1, T-CONS.2 and T-FP's
  `σ = []` instance. T-CONS.4: **keep**; it is already proved.

### T-ELAB: the surface means the calculus

- **Form.** For each surface handler schema `s` of §5.1, with elaboration `⟦−⟧ₛ` into kernel
  terms (`Frontend/Elab/Effects.lean`, `Frontend/Sugar.lean`), one of:

  ```
  (T-ELAB.model)    ⟦with h { M }⟧ₛ  =  hnd_n H_h ⟦M⟧ₛ   for a model H_h of Σ_h (K-MODEL),
                    and L-HRET, L-HOP, L-HFWD hold of it as instances (06);
  (T-ELAB.comodel)  ⟦with h { M }⟧ₛ  =  bor_k[Σ'] (c_h, λ'l c. ⟦M⟧ₛ)  for a comodel c_h of Σ_h
                    (K-COMODEL), and T-COMODEL holds of it (05);
  (T-ELAB.typed)    ∀ program P accepted by the frontend.  ∅; [] ⊢ ⟦P⟧ : F 1   (at the platform's
                    row; see OQ-30)
  ```

  T-ELAB.typed is what the certifying checker establishes today per program. T-ELAB.model and
  T-ELAB.comodel are the meaning of a handler: that the elaborated term is the model or comodel
  the declaration names, so that the laws of 06 are the surface's laws. A schema meeting neither
  is a construct the elaborator alone knows, outside the calculus, and is a defect (C-3, C-7;
  §8).
- **Uses.** K-HND, K-CAP, K-MODEL, K-COMODEL, K-BOR, L-HRET, L-HOP, L-HFWD, T-COMODEL, T-REN.
- **Today.** Not built (audit M15). What exists: answering handlers have run laws over their
  emitted terms (`op_tail`, `op_answer`, `handle_fold`, `Core/Handlers.lean:76, 133, 211`),
  which are T-ELAB.comodel's run half for schema A1; the abortive-clauses-after rule is a derived
  rule from kernel rules (`d_handleAbortCapture`,
  `experiments/SecondClass/SecondClass/AbortClause.lean:69`), which is T-ELAB.model's typing
  half for schema C1. Status: **new**.
- **Slices.** K-HND, K-CAP (03); D-MODEL, D-COMODEL (05); L-HRET, L-HOP, L-HFWD, L-HUNIQ, L-RUN (06); T-REN (07); §5 here.
- **Depends on.** T-MODEL, T-COMODEL, T-REN (the copies per assignment are meaning-preserving
  only by T-REN, decision 57).
- **Open.** OQ-1 (whether the comodel case is a derived form of the model case), OQ-6 (how a
  schema is chosen), OQ-25 (handler state), OQ-53 (whether the elaborator is proved or checked).
- **Obligation.** Per schema, **mechanical** once T-MODEL/T-COMODEL exist, except schema C2
  (a resuming handler with a state), where the state-passing answer type `U(S ⊸ F_Σ(S' ⊗ R))`
  (SPEC §21 *Handler clauses*, `SPEC.md:3212`) must be shown to be a model of `Σ` at that carrier:
  **unknown**, because L-HOP at a state-passing carrier is the parameterised-handler law, which
  no Lean statement covers yet.

### T-LOWER: the lowering classes

- **Form.** For each kernel construct, its lowering class, the law that justifies the class, and
  the cost criterion:

  ```
  class            when                                              law           cost
  direct call      an operation every handler of whose name has     L-TAIL        a call, no κ
                   the same closed clause, resuming once in tail
                   position, neither suspending nor raising
  call             an answering operation (a co-operation on a      L-STATE,      a call
                   capability)                                       T-COMODEL
  branch           an abortive operation; a handler of a name       L-ALG0,       a sum test per call
                   whose operations are all abortive                 L-EXC
  finaliser frame  [then]                                           L-ALG0 / L-W  one code for N and D
  state machine    a control operation that may resume later        L-HOP, L-HFWD, the live variables
                                                                    L-ALG         of the point; κ of
                                                                                  static size
  destructor       cancel of a suspended κ                          L-W, L-SIGNAL the state's destructor
  copy             an unr κ resumed more than once                  L-P           the closure IR's copy
  fixed point      bounded_fix                                      L-FIX         two codes, a stack
                                                                                  closure per level
  ```

  The criterion is **cost parity**: a handled program costs what the program a user would write by
  hand costs, measured by allocations, dispatched calls and copies
  (`corpus/kernel-counts.expected`, `corpus/capture-*-hand.bc`). Effect handling is erased: no
  handler stack, no search, no stack switching (SPEC §19 *Lowering*, `SPEC.md:2839`).
- **Uses.** every K id; L-TAIL, L-STATE, L-ALG0, L-EXC, L-W, L-HOP, L-HFWD, L-ALG, L-SIGNAL, L-P,
  L-FIX.
- **Today.** The classes are built (§6); the laws that justify them are not stated over the
  kernel, except `op_tail` as a run fact for the call class (`Core/Handlers.lean:76`). Status:
  the lowering **as built**; the justification **new**; whether it is a theorem is OQ-23.
- **Slices.** The machine-level statement of each class (E0, T-LOWER.branch, T-LOWER.tail,
  T-LOWER.machine, T-LOWER.copy) is fixed in 04 §6, against which this entry's classes are proved;
  §6 here; L-TAIL and L-ALG0 (06); K-STEP (04).
- **Depends on.** The laws above at their unary half (06).
- **Open.** OQ-23, OQ-16 (the copy class exists only if multi-shot is kept), OQ-25 (a handler
  with a state costs a dispatched call per resume today), OQ-54 (threads).
- **Obligation.** At OQ-23's default (a): per class, the kernel law, **mechanical** for the
  branch, finaliser and fixed-point classes (they are the step rules `[unwind]`, `[finalise]`,
  `[boundedFix]` read as equations); **unknown** for the direct-call class, where L-TAIL needs the
  handler known statically (a specialisation fact about the program, not a law of one handler),
  and for the state-machine class, where "the state holds `K`'s live variables" is L-ALG's unary
  form, which 06 states and nothing proves. The cost half is the corpus gate.

---

## 2. Every id against the code

Columns: what realises the id today, its fate, and the section governing it. "—" means not
built. File paths are relative to the worktree root.

### 2.1 Signatures, rows, models and comodels (02)

| id | realised today by | fate | governs |
|---|---|---|---|
| K-SIG | `OpSig` (`Core/Types.lean:147`), one operation per entry; `OpSig.abort` (`Core/EffRules.lean:40`); frontend `EffSig` (`Frontend/Elab/Effects.lean:57`), string-named, kind per effect (`EffSig.answering`, `:63`) | **change**: grouped per effect with optional equations; the frontend `EffSig` becomes the surface form of the one `Sig` (§5.3) | 02, E-SIG |
| K-ROW | `Row := List OpSig` (`Core/EffRules.lean:33`), first match `Row.find` (`:36`); `RowLe` (`:699`); `Row.Uniq` (`:746`), required only at `[then]` (`effThen`, `Core/Fundamental.lean:360`) | **change**: a sum with distinct names; the first-match list is its representation modulo `Row.Uniq` | 02, E-SIG |
| K-NAME | `UInt32` names, `hn0 : n ≠ 0`, `hnS : ∀ o ∈ S, o.n ≠ n` at `effHandle` (`Core/Fundamental.lean:367`); surface sites numbered per `with` (decision 55) | **keep** (static), under OQ-14 | 02 |
| K-INT | `Row.tab` (`Core/EffRules.lean:47`), `effTab_effOf` (`:49`), `OpSig.ent` (`:43`) | **keep**; `Row.tab` is `⟦Σ⟧δ` | 02 |
| K-THEORY | — (every effect a free theory) | **new** (OQ-22) | 02 |
| K-REN | — in Core; the sibling calculus has name renaming (`experiments/EffModelRel/EffModelRel/Rename.lean`); location renaming of runs in `experiments/TwoRun/TwoRun/Rename.lean:419` (`steps_rename`), which is renaming of `Loc`, not of names | **new**; TwoRun's renaming of runs is the guide for the run half | 02, E-REN |
| K-MODEL | `retTy`, `clausesTy`, `clauseTy`, `kTy` (`Core/EffRules.lean:994, 989, 984, 976`) | **keep** | 02 |
| K-COMODEL | — as a kernel object; the elaborated form `h__op(c: mut 'l S, x) -> mut 'l S * B` (SPEC §18 *Elaboration*, `SPEC.md:2118`); Ξ's capability, `codeTy` (`experiments/HandlersAsBorrows/HandlersAsBorrows/Env.lean:32`) | **new** as a kernel object (OQ-1, OQ-19); HandlersAsBorrows is the guide (**rebuild** over `CDerives`, §3.3) | 02, E-COMODEL |

### 2.2 Terms and typing (03)

| id | realised today by | fate | governs |
|---|---|---|---|
| K-FTY | `CTy.eff`, `CTy.effOf` (`Core/Types.lean:155`) | **keep** | 03 |
| K-OP | `effPerform` (`Core/Fundamental.lean:343`); `perform_compatC` (`Core/EffRules.lean:781`) | **re-index** (compatibility at `W`) | 03, 07 |
| K-RAISE | `effRaise` (`Core/Fundamental.lean:348`); `raise_compatC` (`Core/EffRules.lean:797`); `raiseE` (`Paper/S3_Dynamics/Definitions.lean:346`) | **re-index**; payload `NoOwn` under OQ-24 | 03 |
| K-LET | `effLet` (`Core/Fundamental.lean:353`); `let_compatC` (`Core/EffRules.lean:896`) | **re-index**; its side condition re-derived from L-ALG (graded) | 03, 06 |
| K-THEN | `effThen` (`Core/Fundamental.lean:360`); `then_compatC` (`Core/EffRules.lean:928`); `thenE` (`:923`) | **re-index**; finaliser row under OQ-7 | 03 |
| K-HND | `effHandle` (`Core/Fundamental.lean:367`); `handle_compatC` (`Core/EffRules.lean:1092`), a case analysis (audit M11); `hndTerm` (`:997`) | **re-index**; its compatibility re-derived from T-MODEL (initiality) | 03, 05 |
| K-KONT | `kTy` (`Core/EffRules.lean:976`); `kappa` (`Paper/S3_Dynamics/Definitions.lean:438`); `vC_kTy_of_kapRel` (`Core/EffRules.lean:1053`) | **keep** (types); relation **re-index** | 03 |
| K-CAP | — in Core; Ξ's `handle` as `withbor` form (2) (`translate_typed`, `experiments/HandlersAsBorrows/HandlersAsBorrows/Translate.lean:190`) at `DerivesWf`, not `CDerives` | **rebuild** over `CDerives`; the route is `translate_typed` composed with `embed` (`Core/Embedding.lean:235`), not built | 03, E-COMODEL |
| K-SWAP | `withswap` rule (`Core/Fundamental.lean:254`), type (`Core/Types.lean:1905`); `withswap_compatX` (`Core/Fundamental.lean:503`) | **keep** at a pure callee (R-PURESWAP); OQ-20 | 03 |
| K-BOR | pure: `withbor1`, `withbor2`, `withbor3`, `withload`, `sliceBorrowM`, `sliceBorrowI` (`Core/Fundamental.lean:239, 244, 248, 251, 201, 208`); unwinding twins `withbor1U` … `sliceBorrowIU` (`:258, 264, 270, 276, 281, 288`), gated by `Row.Unwind` (`Core/EffBorrow.lean:133`), compat lemmas `Core/EffBorrow.lean:275, 356, 446, 548, 645, 726`; schema `shiftTy` (`experiments/Shifts/Shifts.lean:17`) | **change**: one constant per printed constant at every `TableOK` row; the pure constants and the `*U` twins **abbreviate** it | 03, E-BOR |
| K-FIX | `boundedFix` rule (`Core/Fundamental.lean:196`), `boundedFix_compatX` (`Core/BoundedFix.lean:91`), `fixSelf_valid` (`:57`) | **re-index** | 03 |
| K-NU | `nuIn`, `nuOut`, `unfoldN` (`Core/Fundamental.lean:331-338`); `affEffBody` (`Core/Aff.lean:155`); `cC_nu_iff` (`Core/NuRel.lean:155`) | **re-index**; effectful `Aff`'s `close` under OQ-7 | 03 |
| K-DIV | a reading of `Loop` (SPEC §14 *Types*, `SPEC.md:1200`); no rule | **keep** under OQ-15 | 03 |
| K-HOST | externs and capabilities (SPEC §11, `SPEC.md:741, 783`); `io_every_run` (`Core/Stdio.lean:694`); `Num[T]` as an ambient handler (decision 54), not built | **change** under OQ-30 | 03, E-HOST |
| K-GEN | branch `lift-stage1`: `[gen]` at `Tout = ∅` (`Core/Gen.lean`), `ewp_gen` (L14.3), `gen_compatC` (T14.6, T14.4); cites `[spec §24]`, unwritten | **rebuild** under E-GEN at OQ-28's chosen option (03 K-GEN) | 03, E-GEN |
| K-HDIV | — (SPEC §21 *Open*: no handler around a div computation) | **new**, in the calculus (U5); per-observation form lands with K-NU, spanning form after OQ-67 (R-HDIV) | 03, E-W |
| K-ALLOC | the allocator as the machine's oracle (SPEC §13) | **new**, in the calculus (U20); presentation OQ-30; lift after OQ-68 (R-ALLOCORACLE) | 03, E-HOST |
| K-SCOPE, K-CARRIER, K-BORANS, K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ, K-SWAPΣ, K-SELFROW, K-FOLDΣ, K-GENNAME, K-NEGREC | — (K-FOLDΣ: the pure folds and counted loops, `Core/Fundamental.lean:183-191, 311-327`, are its `Σ = ∅` instance) | not adopted; each **new** if its question is settled for it (03 §9) | 03 |
| K-GRADE | implicit in `[let]` (`let_compatC`); explicit in `Grade` (`experiments/Grades/Grades/Algebra.lean:58`), `GDerives` (`…/Judgment.lean:40`), `cderives_iff_graded` (`:349`), `fundamentalG` (`…/Soundness.lean:327`) | **promote** the grade reading as the statement of `[let]`'s side condition; `GDerives` stays an experiment (its equivalence with `CDerives` is the evidence the reading is faithful) | 03 |

### 2.3 The machine (04)

| id | realised today by | fate | governs |
|---|---|---|---|
| K-CTX | `HasHnd`, `Catches`, `hndNames` (`Paper/S3_Dynamics/Definitions.lean:386, 397, 410`); `hasHnd_comp`, `catches_comp`, `hndNames_comp` (`Core/EffDefs.lean:77, 85, 93`); `Kont.shift_zero` (`Core/EffRules.lean:480`) | **keep** | 04 |
| K-STEP | `Head` constructors `[boundedFix]` … `[finalise-cancel]` (`Paper/S3_Dynamics/Definitions.lean:495-526`) | **keep** | 04 |
| K-CANCEL | `ccatchE`, `cfinE` (`Paper/S3_Dynamics/Definitions.lean:337, 340`); `cancelTab` (`Core/EffDefs.lean:131`); `ewp_ccatch` (`Core/EffRules.lean:580`), `cancel_frame` (`:168`), `ewp_cfin` (`:284`); programs `Core/EffCancel.lean:56, 59` | **keep**; SPEC §19's `cancel_compatC` (`SPEC.md:2764`) names no declaration, and is corrected to `ewp_ccatch`/`cancel_frame` (audit M12) | 04 |
| K-RUN | `ARun` (`Core/EffDefs.lean:36`, in `wpG`); `head_det_eff` (`Core/Steps.lean:596`); totality `Core/Totality.lean:40-223` | **keep** | 04 |

### 2.4 Model definitions (05)

| id | realised today by | fate | governs |
|---|---|---|---|
| D-W | `ρ`, `ls` (`Core/EffDefs.lean:27`); `σ` only inside `wpG`'s quantifier as `ps` (`:28-29`); stacked line: `LStack` (`experiments/GhostEnd/GhostEnd/Stacked.lean:107`), `αs`, `ReLend` (`:158`) | **change**: `σ` a component; `LStack`/`αs` retire into it | 05, E-W |
| D-ORD | `Ext` (`Core/FrameRecords.lean:172`), `Ext.refl`/`Ext.trans` | **change** (OQ-8, OQ-9) | 05, E-W |
| D-ARISE | `TW` (`Core/World.lean:110`), `Tagged` (`:171`); `TabAt` (`experiments/GhostEnd/GhostEnd/Table.lean:39`), `wpG_tabAt` (`:87`); `TabAtS` (`…/Stacked.lean:290`); branch `borrow-callbacks`/`gfp-arising`: `tabAtS_comp`, `wpG_tabAtS_one` (`…/Arising.lean:83, 112`) | **change**: `TabAtS` from a guard to a `TW` invariant; `TabAt`, `wpG_tabAt`, `tabAtS_comp`, `wpG_tabAtS_one` **promote** | 05, E-W |
| D-WPG | `wpG` (`Core/EffDefs.lean:27-40`); `wpTS` (`Core/World.lean:186`), `wpTS_iff_wpG` (`Core/EffWp.lean:43`) | **change** at stops only (D-STOP) | 05 |
| D-STOP | the clause `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)` at every final term (`Core/EffDefs.lean:40`) | **change**: a kernel definition change; SPEC entry first (OQ-9, OQ-10) | 05, E-W |
| D-TABLE | `Table`, `Table.Mono`, `Table.Abortive`, `Table.bot` (`Core/EffDefs.lean:50, 53, 58, 65`) | **keep** | 05 |
| D-OPTAB | `opTable` (`Core/EffDefs.lean:157`); `opTable_mono` (`Core/EffWp.lean:951`) | **re-index** | 05 |
| D-CANCELTAB | `cancelTab`, `errOk` (`Core/EffDefs.lean:131, 122`); `cancelTab_abortive` (`Core/EffWp.lean:1013`) | **keep** | 05 |
| D-TABLEOK | the instances: `Table.Abortive` (`Core/EffDefs.lean:58`); `LinResume` (`experiments/GhostEnd/GhostEnd/Body.lean:141`); `ResumeAff` (`…/Drop.lean:44`); `OpTab.AbortOnly`, `OpTab.Local` (`Core/EffRules.lean:247, 250`) | **new**; each instance a corollary | 05, E-BOR |
| D-EWPP | — (`wpTSD`, `Core/Demonic.lean:223`, is total-correctness every-run) | **new**, only under OQ-15 (b); a second wp family recorded as a defect (OQ-63) | 05 |
| D-EWP | `ewpStep`, `ewpTS` (`Core/EffDefs.lean:68, 73`); `ewp_ind`, `ewp_fold`, `ewp_unfold` (`Core/EffWp.lean:754, 759, 765`); stacked: `OpenS`, `bodyS`, `stopS`, `ghostS` (`…/Stacked.lean:221, 209, 200, 188`) | **re-index**; `OpenS` at depth `|σ|` is the guide (`bodyS_nil_iff`, `…/Stacked.lean:476`) | 05 |
| D-SHARE | `contShare` (`Core/EffDefs.lean:144`) | **re-index**; quantifier at `:147` under OQ-8 | 05 |
| D-KAP | `KapRel` (`Core/EffRules.lean:569`); branch `lift-stage1`: `KapRel.mono`, `KapRel.ext` (`Core/Gen.lean:125, 133`) | **re-index** | 05 |
| D-OWED | `cancelOwed` (`Core/EffDefs.lean:138`) | **re-index**; open frames OQ-9 | 05 |
| D-REL | `vCE`, `cC`, `cB`, `effTab`, `effRet` (`Core/Relation.lean:119, 154, 192, 170, 176`); five relation families beside it: `vRL` (`experiments/GhostEnd/GhostEnd/Bridge.lean:221`), `vRLg` (`…/RLCompat.lean:508`), `vRLs` (`…/Stacked.lean:237`), `vRLa` (branch `gfp-arising`, `…/Arising.lean:173`), `vRLk` (branch `borrow-callbacks`, `…/Extend.lean:62`) | **change** (re-indexed); the five families **retire** into it | 05, E-W |
| D-SEM | `SemC`, `SemV` (`Core/Relation.lean:228, 232`); `gDenC` (`:224`) | **re-index** | 05 |
| D-MODEL | — | **new** | 05, E-MODEL |
| D-COMODEL | — | **new** (OQ-1, OQ-19) | 05, E-COMODEL |
| D-DTOR | `dtorE`, `HasDtor` (`Core/Dtor.lean:132, 176`); the `[then]` frame (`then_compatC`); `ubindK` (`Core/EffRules.lean:338`) | **change**: stated once | 05 |
| D-BIN | — on Core; the sibling calculus's `LR` (`experiments/EffModelRel/EffModelRel/Rel.lean:295`) | **new**, conditional on OQ-4; `LR` is **evidence** | 05 |

### 2.5 Laws (06)

Every law below has, today, at most a step rule or a run fact over the kernel, and its algebraic
form only in the sibling calculus (`experiments/EffModelRel`), whose standing is OQ-5. "evidence"
in the fate column refers to that.

| id | over the kernel today | elsewhere | fate |
|---|---|---|---|
| L-ALG | `[op]` step; side conditions of `let_compatC` (`Core/EffRules.lean:896`), `then_compatC` (`:928`), `kTy` (`:976`), `contShare` (`Core/EffDefs.lean:144`) | `alg_bind`, `alg_app`, `alg_iapp` (`experiments/EffModelRel/EffModelRel/Laws.lean:67, 76, 96`) | **new** over the kernel; the four encodings re-derived from it |
| L-ALG0 | `[finalise]`; `then_compatC` | `alg_ab_bind`, `alg_ab_app`, `alg_dtor` (`…/Laws.lean:102, 107, 114`) | **new** |
| L-GEN | — | — | **new** |
| L-HRET | `[ret]` step | `h_ret` (`…/Laws.lean:148`) | **new** over the kernel |
| L-HOP | `[op]` step (`Paper/S3_Dynamics/Definitions.lean:503-505`) | `h_op` (`…/Laws.lean:164`) | **new** |
| L-HFWD | the forwarding case of `handle_compatC` (`Core/EffRules.lean:1092`) | `h_fwd` (`…/Laws.lean:202`) | **new** |
| L-HUNIQ | — | `handle_unique` (`experiments/CoeffectsStrict/CoeffectsStrict/Handler.lean:59`), one effect, total clauses; `handle_fold` (`Core/Handlers.lean:211`) for answering handlers | **new**; binary (OQ-4) |
| L-HFUSE | — | — | **new**; binary |
| L-HCORR | vacuous | — | **new** under OQ-22 |
| L-EXC | `[unwind]`, `[finalise]`; programs `toResult` (`Core/EffPrograms.lean:107`) | — | **new** |
| L-STATE | `op_tail`, `op_answer`, `handle_fold` (`Core/Handlers.lean:76, 133, 211`): run facts over emitted terms | — | **keep** the run facts as T-ELAB's run half; the law **new** |
| L-YIELD | programs `takeProg` (`Core/EffPrograms.lean:787`), `producer` (`:766`) | — | **new** |
| L-ND | — | — | **new**, only if OQ-16 keeps `unr` |
| L-SUM | programs `logOutside`, `failOutside` (`Core/EffPrograms.lean:220, 277`), `nLogOutside`, `nFailOutside` (`:484, 487`) | `absorb_pure` (`experiments/EffModelRel/EffModelRel/Tensor.lean:204`), `absorb_writer` (`…/Examples.lean:115`) | **new** |
| L-TENSOR | — | `tensor` (`…/Tensor.lean:91`) | **new**; unary half the disjoint-capability frame fact |
| L-SIGNAL | the name `⊥ = 0`; `cfin` (K-CANCEL) | — | **new** |
| L-W | `[cancel]` step; `ewp_ccatch`, `cancel_frame` (`Core/EffRules.lean:580, 168`); `ewp_kappa_cancel` (`:529`) | — | **new** as an equation; the unary half exists |
| L-C | `kTy` with T-FP | — | **keep** (a typing invariant) |
| L-P | `[let]` at `unr` (`vP_empty_of_persistent`, `Core/Persistent.lean:105`) | `lam_bang_persistent` (`experiments/HandlersControl/HandlersControl/Capture.lean:42`), at `DerivesWf` | **keep**; `lam_bang_persistent` **rebuild** at `CDerives` |
| L-BETA | `ewp_kappa_resume` (`Core/EffRules.lean:493`), unary | TR §13.2 | **new** binary half |
| L-ETA | — | TR §13.3 | **new**; OQ-27 |
| L-HIDE | `wpTS_M_antiFrameX` (`Core/EffWp.lean:567`), `ewpTS_M_antiFrameU` (`:854`) | `ewpTS_M_antiFrameR` (`experiments/GhostEnd/GhostEnd/Frames.lean:89`) | **keep**; resuming half **promote** |
| L-INTER | — | TR §13.5 | **new**; open at affine |
| L-NAH | — | `no_accidental_handling` (`experiments/EffModelRel/EffModelRel/Laws.lean:362`) | **new**, from T-REN |
| L-REN | — | — | **new** |
| L-NU | — | `idem_nu`, `new_nu`, `nu_nu` (`…/Laws.lean:242, 246, 262`); `nu_op_fails_multishot` (`…/Examples.lean:223`); `O1` (`…/Ownership.lean:93`) | **new**, only under OQ-14 (b) |
| L-BOR | `ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU` (`Core/EffWp.lean:828, 842, 854`); `ewp_unwind`, `ewp_end`, `ewp_box_end` (`Core/EffBorrow.lean:54, 97, 118`) | resuming halves: `ewpTS_M_frameR` (`experiments/GhostEnd/GhostEnd/Relend.lean:117`), `ewpTS_I_frameR` (`…/ImmLend.lean:175`), `withborR_compat` (`…/Drop.lean:108`) | abortive half **keep**; resuming half **promote** under D-STOP |
| L-FIX | `[boundedFix]` step; `cC_boundedFix` (`Core/BoundedFix.lean:49`) | `boundedFixEnv_compatX`, `boundedFixRec_compatX` (`experiments/SecondClass/SecondClass/Restated.lean:56, 79`), instances | **keep** |
| L-DIV | — | `unfold_next`, `unfold_close`, `unfold_unique` (`experiments/CoeffectsStrict/CoeffectsStrict/Unfold.lean:55, 67, 155`), over Core's `cC` | **promote** under OQ-15 (a) |
| L-FOLD | — at a row | `fold_beta`, `fold_unique` (`experiments/CoeffectsStrict/CoeffectsStrict/Fold.lean:76, 207`), pure algebras over Core | **new**, only under OQ-62 (b) |
| L-DISCARD, L-COPY, L-COMMUTE | — | Kammar-Plotkin POPL 2012, not read (OQ-64) | **new** |
| L-TAIL | `op_tail` (`Core/Handlers.lean:76`) for answering operations; for control operations, the lowering's `tailResumptive` (`Backend/Clos/Capture.lean:631`) with no law | — | **new** |

### 2.6 Metatheorems (05, 07)

| id | realised today by | fate |
|---|---|---|
| T-MONO | `Ext.refl`/`Ext.trans`; GhostEnd's named gap "gRLk at σ ⇒ at τ ++ σ" (branch `borrow-callbacks`, `…/Extend.lean`, docstring) | **new** |
| T-NIL | `vRLs_nil`, `cRLs_nil`, `gRLs_nil` (`experiments/GhostEnd/GhostEnd/Stacked.lean:501, 540, 588`) and `vRLa_nil`, `cRLa_nil` (branch `gfp-arising`, `…/Arising.lean:260, 300`) as `propext` equalities; none for `vRLk` | **new**: by `rfl` at the clauses that read no extension, per row at `U`, `share`, `KapRel` (OQ-58); the `*_nil` lemmas retire with their families after 05 §9's equivalences |
| T-STOP | `ewp_bot` (`Core/EffWp.lean:772`), `wpTS_iff_wpG` (`:43`) | **change** with D-STOP |
| T-ARISE | `wpG_tabAt` (`experiments/GhostEnd/GhostEnd/Table.lean:87`); `wpG_tabAtS_one` (branch `gfp-arising`, `…/Arising.lean:112`) | **promote** and generalise to every stack |
| T-FRAME | abortive: `Core/EffWp.lean:828-854`; resuming: `ewpTS_M_frameR`, `ewpTS_I_frameR`, `ewpTS_M_antiFrameR` (`experiments/GhostEnd/GhostEnd/Relend.lean:117`, `…/ImmLend.lean:175`, `…/Frames.lean:89`), `stack_step_other`, `stack_step_reborrow`, `stack_step_imm` (`…/StackStep.lean:392, 563, 1003`), `opTable_extR` (`…/Frames.lean:32`), `ptoImm_dup` (`:110`), `freeze_at` (`…/Freeze.lean:50`); 6.150 not lifted | **promote**, one induction on depth; the `AllCross` premise (`…/StackStep.lean:182`) removed |
| T-SUMOK | — (`OpTab.ext`, `Core/EffDefs.lean:117`, exists) | **new** |
| T-MODEL | `ewp_handle` (`Core/EffRules.lean:615`), a case analysis | **change**: restated as initiality |
| T-COMODEL | — | **new** |
| T-DEF | the relation's structural recursion (`Core/Relation.lean:119-200`); `nuRel` as a greatest fixed point (`Core/NuRel.lean:29`); `no_negative_domain` (`experiments/EffModelRel/EffModelRel/Obstruction.lean:35`) names where a recursive domain would be needed | **keep**; OQ-31 |
| T-COMPAT | per rule, at `σ = []`, the `*_compatC`/`*_compatX` lemmas called from `fundamentalC` (`Core/Fundamental.lean:488-529`) | **re-index** |
| T-FP | `fundamentalC` (`Core/Fundamental.lean:434`); `gfpAt_nil` (`experiments/GhostEnd/GhostEnd/Stacked.lean:613`), `gfpAtA_nil` (branch `gfp-arising`, `…/Arising.lean:374`) restate it; `GFP` stated, not proved (`…/Stacked.lean:312`) | **re-index** |
| T-ADEQ | `adequacyC`, `adequacyD`, `adequacyD_safe`, `adequacyD_val` (`Core/Fundamental.lean:590`; `Core/Demonic.lean:312, 325, 334`) | **keep** (T-CONS.3) |
| T-SAFE | `ewp_bot` with T-ADEQ | **keep**; named corollary **new** |
| T-LEAK | `NoOwn ρp` in `wpG` (`Core/EffDefs.lean:38`) | **keep**; named corollary **new** |
| T-FIN | — as a corollary | **new** (audit m10) |
| T-LIN | `kTy` with T-FP | named corollary **new** |
| T-DET | `head_det_eff` (`Core/Steps.lean:596`) | **keep** |
| T-REN | — | **new**; decision 57's "renaming lemma" |
| T-NAH | — | **new** |
| T-ABS | — | **new**; binary |
| T-TOTAL | `total_every_alloc`, `total_run_prefix`, `total_every_run`, `total_no_infinite_run` (`Core/Totality.lean:40, 56, 64, 223`) | **keep** |
| T-2RUN | `freshRun_det` (`experiments/TwoRun/TwoRun/Fresh.lean:255`), `run_sim` (`…/Sim.lean:253`), `fresh_run_image` (`:274`), `wpTS_footprint_fresh` (`:286`); limits `not_readFootprint` (`…/Read.lean:185`), `ReadFootprintTyped` stated, not derived (`:81`) | **promote** the determinism-up-to-renaming results under OQ-4 (b); the read footprint stays open |
| T-BINFP | `fundamental` (`experiments/EffModelRel/EffModelRel/Fundamental.lean:278`), sibling | **new** on Core, conditional on OQ-4 |
| T-SOUND | `soundness` (`experiments/EffModelRel/EffModelRel/Adequacy.lean:258`), sibling | **new** on Core, conditional on OQ-4 |

---

## 3. Every effect-related artifact, and its fate

The other direction: each artifact, with its fate and the id or section that governs it. "Core"
artifacts are on `main`; the branch is named otherwise.

### 3.1 Core

| artifact | content | fate | governs |
|---|---|---|---|
| `Core/EffDefs.lean` | `wpG`, `valPost`, `Table`, `ewpTS`, `OpEnt`, `OpTab`, `errOk`, `cancelTab`, `cancelOwed`, `contShare`, `opTable` (`:27-157`) | **keep** the file; `wpG` **change** at the stop (`:40`); the rest **re-index** | D-WPG, D-STOP, D-TABLE, D-OPTAB, D-SHARE, D-OWED, D-EWP |
| `Core/EffRules.lean` | rows (`:33-47`, `:699-765`), table order lemmas (`:126-166`), cancel and finaliser frames (`:168-450`), `κ` (`:493-553`), `KapRel` (`:569`), `ewp_handle` (`:615`), the compatibility lemmas of the six §19 rules (`:774-1092`), `kTy` and clause types (`:976-994`) | **keep**; rows **change** with K-ROW; `ewp_handle` **change** to initiality (T-MODEL); `handle_compatC` re-derived | K-ROW, K-INT, K-MODEL, T-MODEL, T-COMPAT |
| `Core/EffWp.lean` | `wpG` facts; the three printed frames over `wpG` (`wpG_I_frameX` `:75`, `wpG_M_frameX` `:363`, `wpG_M_antiFrameX` `:567`); `ewp` induction (`:748-811`); abortive lifts (`:828-854`); `wpG_bind`, `wpG_ramify`, `wpG_frame` (`:878, 978, 1005`) | **keep**; the abortive lifts become instances of T-FRAME | T-FRAME, L-BOR, L-HIDE |
| `Core/EffBorrow.lean` | `Table.withFr` (`:44`), `ewp_unwind` (`:54`), `ewp_end` (`:97`), `Row.Unwind` (`:133`), the unwinding types (`:177-209`, `:525`, `:625-630`), six compat lemmas (`:275-726`), `cbEnds` (`:637`) | **abbreviate**: the types and compat lemmas become K-BOR at a `Row.Unwind` row; `Row.Unwind` becomes a corollary of `TableOK` | K-BOR, D-TABLEOK |
| `Core/EffCancel.lean` | two cancel programs (`prog` `:56`, `prog₃` `:59`) and their runs (`:103, 113`) | **keep** (acceptance) | K-CANCEL, §9 |
| `Core/EffPrograms.lean` | §19's acceptance programs, derivations and evaluations (`:41-1088`) | **keep** (acceptance) | §9 |
| `Core/EffExamples.lean` | two handled programs at `lin` and `aff` (`prog` `:35`, `progC` `:67`) | **keep** | §9 |
| `Core/Handlers.lean` | answering laws `op_tail`, `op_answer`, `handle_fold` (`:76, 133, 211`); abort laws `abort_passes`, `return_resumes`, `loop_abort` (`:153, 167, 229`) of decision 52's sum encoding | answering laws **keep** as T-ELAB.comodel's run half; abort laws **relabel** as laws of a withdrawn encoding (decision 52) or delete; the module header (`:5-30`, "a handler is defined by its elaboration … decision 48") **relabel** | L-STATE, T-ELAB |
| `Core/Aff.lean`, `Core/AffRules.lean`, `Core/AffPrograms.lean` | the affine closure as codata (`affC` `Core/Aff.lean:36`, `affBox` `:43`, `cC_aff_iff` `:72`, `aff_coind` `:83`, `affEffBody` `:155`); derived rules (`Core/AffRules.lean:36-200`) | **keep**; the effectful `Aff` (`affEffBody`) under OQ-7 | K-NU |
| `Core/Nu.lean`, `Core/NuRel.lean` | coiteration and the `ν` clause (`unfoldTy` `Core/Nu.lean:41`, `unfoldV` `:139`; `nuRel` `Core/NuRel.lean:29`, `cC_nu_iff` `:155`, `effTab_instT` `:115`, `effRetE_unroll` `:120`) | **re-index** | K-NU, K-DIV |
| `Core/BoundedFix.lean` | `bounded_fix` (`:35-91`) | **re-index** | K-FIX, L-FIX |
| `Core/Totality.lean` | totality (`:40-223`) | **keep** | T-TOTAL |
| `Core/Dtor.lean` | destructors (`:104-330`) | **keep**; D-DTOR states the destructor of a context from it | D-DTOR |
| `Core/Stdio.lean` | externs, capabilities, `io_every_run` (`:694`), `externs_loop_every_run` (`:768`) | **keep**; under OQ-30 the capabilities become comodels with host carriers | K-HOST |
| `Core/Embedding.lean` | `embed` (`:235`), `adequacy_of_derivesWf` (`:326`) | **keep** | T-CONS.4; the route for K-CAP |
| `Core/Relation.lean`, `Core/World.lean` | the relation (`:119-232`); `TW` (`Core/World.lean:110`), `wpTS` (`:186`) | relation **change** (re-index); `TW` **keep** (its `ps`/`rs` are `σ`, O-W) | D-REL, D-ARISE |
| `Paper/S3_Dynamics/Definitions.lean` | §19's machine: `ubindE`, `ccatchE`, `cfinE` (`:334-340`), context predicates (`:386-417`), `kappa` (`:438`), head steps (`:495-526`) | **keep** | K-CTX, K-STEP, K-KONT, K-CANCEL |
| branch `lift-stage1`: `Core/Gen.lean`, `Core/AffTy.lean` | `[gen]`: `genOp`, `genE`, `Qgen` (D14.4), `ewp_gen` (L14.3, `Core/Gen.lean:199`); T14.4, T14.6 and the `CDerives` rule not written (the branch is marked not for merge, #274) | **rebuild** under a SPEC entry: `[gen]` is K-HND at `Tout = ∅` with the continuation read at `[@c] U(Aff^c A B)` (K-NU); whether it is a rule or a derived form is OQ-28 (the file's docstring: "`κ : U(…)` has no outlives rule, so `[]I` cannot box it; that is why `[gen]` is a rule"). The file cites `[spec §24]`, which no SPEC on any branch has: a SPEC gap (§11) | K-HND, K-NU, OQ-28, E-GEN |

### 3.2 Phase A and phase B (#235): the sibling calculus

| artifact | content | fate | governs |
|---|---|---|---|
| `experiments/EffModel` | executable model of adjoint modes, models, comodels, running as tensor, `ν` instances (`Syntax.lean:20-213`, `Eval.lean`, `Laws.lean`), laws as `#guard`s | **evidence** (OQ-5) | 06 citations only |
| `experiments/EffModelRel` | binary relation `LR` (`Rel.lean:295`), FP (`Fundamental.lean:278`), `soundness` (`Adequacy.lean:258`), laws (`Laws.lean:67-362`), tensor (`Tensor.lean:91`), the ν/op refutation (`Examples.lean:223`), `O1` (`Ownership.lean:93`), unary moded relation (`Unary.lean:118`), cell model (`Cell.lean`) | **evidence** (OQ-5); each law **rebuild** over the kernel as its L id (§2.5); `LR`'s worlds (partial bijections of names with pending and garbage statuses) are the guide for D-BIN under OQ-4 (a) | 06, D-BIN |

### 3.3 Handlers as borrows, control, shifts

| artifact | content | fate | governs |
|---|---|---|---|
| `experiments/Shifts` | `shiftTy` (`Shifts.lean:17`), the borrow constants as one schema (`withbor1_shift` … `withload_shift`, `:22-31`), `axWithborMITy` (`:50`) | **promote** as the form of K-BOR: one constant per printed constant is `shiftTy` at a callback row | K-BOR, E-BOR |
| `experiments/HandlersAsBorrows` | Ξ's answering handlers as `withbor` form (2) at `DerivesWf`: `translate_typed` (`Translate.lean:190`), `effect_safety` (`Safety.lean:55`), `effect_safety_open` (`:71`), `capability_not_outlives` (`:87`), `handle_is_shift` (`:115`); a capability stored in a cell (`d_sepProg` `Separating.lean:134`); an aliased capability refused (`twoBlocks_refused` `Sharing.lean:196`) | **rebuild** over `CDerives`: K-CAP's typing rule is `translate_typed`'s target composed with `embed` (`Core/Embedding.lean:235`); `handle_is_shift` is the fact that places K-CAP in K-BOR's schema; `capability_not_outlives` is the reason a capability cannot leave its handler (the comodel's scope). Kept as the guide | K-CAP, K-COMODEL, OQ-1, OQ-3 |
| `experiments/HandlersControl` | state behind control (`progP_eval` `Behind.lean:204`; `no_uniform_comp` `:53`); re-entry as linearity of the state token (`memoPair_eval` `Reentry.lean:277`, `spanFwd_refused` `:308`); capture modes (`lam_bang_persistent` `Capture.lean:42`, `multiShot_refused` `:70`, `forget_not_lolli` `:150`); the box as the bound of a stored continuation (`box_lolli_outlives_iff` `Outlives.lean:35`, `crossProg` `:65`) | **rebuild** at `CDerives`: `lam_bang_persistent` is L-P's typing half; `box_lolli_outlives_iff` is OQ-28 (a)'s rule at the paper level; `spanFwd_refused` is the re-entry discipline K-NAME needs; the control-handler-as-borrow question is OQ-3 | L-P, OQ-3, OQ-28, K-NAME |
| `experiments/SecondClass` | `d_handleAbortCapture` (`AbortClause.lean:69`); `handleAt_compatC` (`Prompts.lean:75`), handling at a run-time name given freshness; `recLog_derives` (`RecLog.lean:126`); `boundedFixEnv_compatX`, `boundedFixRec_compatX` (`Restated.lean:56, 79`) | `d_handleAbortCapture` **promote** into Core (it is built from kernel rules; it is T-ELAB.model's typing half for schema C1); `handleAt_compatC` is the guide for OQ-14 (b); the `bounded_fix` instances **keep** as evidence of K-FIX at records | T-ELAB, OQ-14, K-FIX |

### 3.4 Two runs, grades, coeffects

| artifact | content | fate | governs |
|---|---|---|---|
| `experiments/TwoRun` (#39) | `steps_rename` (`Rename.lean:419`), `freshRun_det` (`Fresh.lean:255`), `run_sim` (`Sim.lean:253`), `fresh_run_image` (`:274`), `wpTS_footprint_fresh` (`:286`); limits `not_everyRunFootprint` (`Refute.lean:133`), `not_readFootprint` (`Read.lean:185`) | **promote** under OQ-4 (b): the route by which a law whose binary half reduces to determinism is proved without `≈`. Its README names the read footprint as the missing step for the two-run laws; that is what OQ-4 (b)'s per-law check must meet | T-2RUN, OQ-4 |
| `experiments/Grades` (#23) | `Grade` (`Algebra.lean:58`), `GDerives` (`Judgment.lean:40`), `cderives_iff_graded` (`:349`), `fundamentalG` (`Soundness.lean:327`), `semC_weak` (`:161`), erasure (`Erasure.lean:136`) | **promote** the reading (O-QUAL as a grade; `[let]`'s side condition as scaling); `GDerives` stays an experiment | O-QUAL, K-GRADE, L-ALG, OQ-17 |
| `experiments/Coeffects` | `KDem` (`Judgment.lean:39`), `KDem.elab` (`:61`), `KDem.sem` (`:72`), `provide_wf` (`:79`), `d_seqD` (`Demand.lean:163`), `d_parI` (`Imm.lean:57`), `main_every_run` (`Programs.lean:134`) | **evidence**: its finding, "a borrow block is a tail-resumptive handler with no operations" (README), is the K-CAP/K-BOR identity; no kernel change | K-CAP |
| `experiments/CoeffectsStrict` | laws on runs over Core: `fold_beta`, `fold_unique` (`Fold.lean:76, 207`), `unfold_next`, `unfold_close`, `unfold_unique` (`Unfold.lean:55, 67, 155`), `handle_write`, `handle_unique` (`Handler.lean:50, 59`), `bang_idem`, `box_idem` (`Context.lean:70, 96`) | **promote** `unfold_*` as L-DIV's codata laws (OQ-15 (a)); `handle_write`/`handle_unique` are the pattern for L-HUNIQ at one effect | L-DIV, L-HUNIQ |

### 3.5 The stacked line (GhostEnd, Restrat; #258-#287)

Every retirement here is conditional on the re-index (05 landing with OQ-8 settled). Until then
GhostEnd is frozen and nothing is deleted (decision 20; audit §6 step 2). Before any deletion,
the helpers `Stacked.lean` reaches through its import chain are pulled out first (audit §3.5).

| artifact | content | fate |
|---|---|---|
| `GhostEnd/Relend.lean`, `ImmLend.lean`, `Frames.lean`, `Freeze.lean` | `Relend` (`Relend.lean:57`), `ewpTS_M_frameR` (`:117`); `RelendI` (`ImmLend.lean:128`), `ewpTS_I_frameR` (`:175`); `AntiRelend` (`Frames.lean:68`), `ewpTS_M_antiFrameR` (`:89`), `opTable_extR` (`:32`), `ptoImm_dup` (`:110`); `freeze_at` (`Freeze.lean:50`) | **promote** (T-FRAME's resuming halves) |
| `GhostEnd/Stacked.lean`, `StackStep.lean` | `OpenS`, `bodyS`, `stopS`, `ghostS` (`Stacked.lean:221, 209, 200, 188`), `RelendableS`, `RelendableN` (`:163, 170`), `TabAtS` (`:290`), `bodyS_nil_iff` (`:476`); `stack_step_*` (`StackStep.lean:392, 563, 1003`) | **promote** `OpenS` and the stack steps as T-FRAME's depth induction; `AllCross` (`StackStep.lean:182`) **retire** (it is discharged only by constant `true`, audit M8); `LStack`, `ReLend` (`Stacked.lean:107, 158`) **retire** into `σ` |
| `GhostEnd/Table.lean`; branch `gfp-arising` `Arising.lean` | `TabAt` (`Table.lean:39`), `wpG_tabAt` (`:87`); `tabAtS_comp` (`Arising.lean:83`), `wpG_tabAtS_one` (`:112`), `wpG_below_not_arises` (`:139`) | **promote** as T-ARISE |
| `GhostEnd/Values.lean`, `Payload.lean` | `LOk` (`Values.lean:48`), `lok_thaws` (`:381`); `payload_strict` (`Payload.lean:50`), `PayFree` (`:70`) and its facts | **promote** (audit §3.5) |
| `GhostEnd/Drop.lean` | `ResumeAff` (`:44`), `opTableO` (`:49`), `ewp_then_owner` (`:70`), `withborR_compat` (`:108`), `handleR_spans_yields` (`:284`), `spans_two_affine_yields` (`:318`) | **promote** `ResumeAff`/`opTableO` as a `TableOK` instance (the affine case of M8's remedy) |
| `GhostEnd/Body.lean`, `Loop.lean` | `Open` (`Body.lean:63`), `LinResume` (`:141`), `open_bind` (`:216`); `open_boundedFix` (`Loop.lean:33`) | `LinResume` becomes a `TableOK` instance; `Open` **retire** (subsumed by `OpenS`) |
| `GhostEnd/Bridge.lean`, `RLCompat.lean` | `vRL`, `cRL` (`Bridge.lean:221, 231`), `KapRelR` (`:114`), `URelend` (`:133`); `Relendable` (`RLCompat.lean:77`), `gRL` (`:256`), `RelendableG` (`:498`), `vRLg`, `cRLg` (`:508, 518`), `thunkF_RL_fails_below_at` (`:471`) | `vRL`, `vRLg` **retire** after 05 §9's inclusions (i) and (i'), stated with their real index `(S, x, T, δ, l)` and lifetime `α` and restricted to the fragment they read (`.thunk` over `.ret`/`.arr` bodies at the external row `S`, and `.tensor`): `cRL`/`cRLg` read `True` at `&`, `⊤`, `∀`, `ν` and the `.eff` chain, so a full `↔` with D-REL is excluded by their definitions, not unknown; `vRLg_nil` is stated with (i'). `KapRelR`, `URelend`, `RelendableG` **retire**; `thunkF_RL_fails_below_at` **keep** as the configuration that motivates the guard (it is a machine-checked fact about the single-lend relation) |
| `GhostEnd/Stacked.lean` | `vRLs`, `cRLs`, `gRLs` (`:237, 252, 284`), `GFPAt`, `GFP` (`:305, 312`), `gfpAt_nil` (`:613`) | `vRLs` **retire**; `GFP`'s statement **rebuild** as T-FP at `W` with the full row skeleton (audit M6) |
| branch `gfp-arising`: `Arising.lean` | `guardS` (`:169`), `vRLa`, `cRLa` (`:173, 189`), `GFPAtA` (`:234`), `gfpAtA_nil` (`:374`), the rows `force_RLa`, `thunkF_RLa`, `thunkE_RLa`, `lam_RLa`, `allI_RLa` (`:382-815`) | `vRLa`, `guardS` **retire**; the row proofs are the guide for T-COMPAT's `thunk`, `lam`, `allI` rows (OQ-8 (iv)) |
| branch `borrow-callbacks`: `Extend.lean` | `vRLk`, `cRLk`, `effRetK` (`:62, 81, 100`), `all_elimK` (`:110`), `callback_ext` (`:131`), `callback_ext_one` (`:167`) | **retire** `vRLk` once OQ-8 is settled; `callback_ext` is criterion (iii) of OQ-8 and is kept as the test any candidate placement must pass. No `vRLk_nil` exists |
| branch `gfp`/`gfp-arising`/`borrow-callbacks`: `Below.lean` | `not_gfpAt_below` (`:196`), `not_gfp` (`:282`) | **not merged under a `not_` name** (audit §3.5): its witness does not arise (#285); restated with the arising hypothesis, it is a configuration about `GFPAt` |
| `GhostEnd/Typed.lean`, `TypedD.lean`, `ClosureBody.lean`, `Callee.lean`, `Closures.lean`, `General.lean`, `Open.lean`, `Kernel.lean`, `Descend.lean`, `Nested.lean` | `StopSafe` (`Typed.lean:166`), `RBody` (`:180`), `FrameThaws` (`:361`), `Row.Resume` (`Open.lean:40`), `RBodyT` (`TypedD.lean:35`), `RBodyC` (`ClosureBody.lean:118`), `CloL` (`Callee.lean:45`), `TV`, `TVG` (`Closures.lean:53, 84`), `FrameThawsD` (`Values.lean:365`), `RBodyOfTyped` (`General.lean:53`), `O151AsStated` (`Open.lean:76`), `KernelInvariant` (`Kernel.lean:47`), `OpenD` (`Descend.lean:125`), `NestRelend`, `NestRelend₂` (`Nested.lean:103, 285`) | **retire** (audit §3.5); the spanning programs (`branch_spans_yields`, `loop_spans_yields`, `tuple_spans_yield`, `closure_spans_yield`, `callee_spans_yields`; `Branch.lean:177`, `Loop.lean:153`, `Tuple.lean:93`, `Capture.lean:76`, `Callee.lean:241`) **rebuild** as acceptance programs at `W` |
| `GhostEnd/Segment.lean` | `segment_fundamental` (`:30`) | **retire** (a restatement of `fundamentalC`) |
| `GhostEnd/Witness.lean` | `relent_holds` (`:81`) | **keep** with Restrat's counterexample cell |
| `experiments/Restrat` | `Audit.lean` (`run_meta` scan, `:121`); `mut_not_natural` (`MutCounterexample.lean:148`); `VDenNatural`, `not_vDenNatural`, `WpNatural`, `frame_outside_image` (`Open.lean:26, 30, 37, 43`); `restrat_segment` (`Segment.lean:73`); carrier action (`Carrier.lean:114-138`) | **retire** everything except `Audit.lean` and the counterexample cell (audit §3.5); `not_vDenNatural` is restated "over all valid resources" (audit m7), since its witness is not shown to arise. The re-stratification route is OQ-9 (b) (capture rebasing); if OQ-9 settles on (b), Restrat's carrier action is the guide and is **rebuilt**, not retired |

### 3.6 The carrier ancestor

`experiments/CBPVWorld` (README "the typed world re-typed at CBPV types") is the effect-free
ancestor of Core's relation; it contains no effect construct (no `perform`, `opTable` or `ewp`:
read of `CBPVWorld/*.lean`). Its embedding of `DerivesWf` (`CBPVWorld/Embedding.lean:232`) is the
one Core carries as `Core/Embedding.lean:235`. Fate: **keep** as an experiment; it bears on the
calculus only through T-CONS.4.

---

## 4. SPEC entries and decisions

### 4.1 The existing entries

| entry | section | what the calculus does to it |
|---|---|---|
| 13, divergence as an effect | §14 (`SPEC.md:1190`) | **kept** under OQ-15 (a): `div` stays a reading of `Loop` (`SPEC.md:1200-1217`) and K-DIV adds no rule. `Loop_Σ` (effectful observations) becomes a K-NU instance at a row. §14 *Open*'s "`div_fuel` is `driveE` by construction, not by a proved equation" (`:1492`) is an L-DIV obligation. Under OQ-15 (b) the entry is **revised**: a row entry and a partial-correctness `ewp`. |
| 17, effects and handlers (surface) | §18 (`SPEC.md:2064`) | **revised**. *Elaboration* (`:2118`) is restated as T-ELAB per schema (§5.1). *Laws* (`:2194`) is replaced by T-ELAB.model/comodel; its abort laws are labelled as a withdrawn encoding. *Declarations*' "an effect is one kind or the other" (`:2088`) is OQ-55. *Not provided* (`:2169`) is re-read against §8: each rejected form either is a named restriction (00 §7.2) or is an elaboration gap with an issue. |
| 18, native capture | §19 (`SPEC.md:2270`) | **revised** by E-SIG (rows as sums), E-W (the stop), E-BOR (row-generic borrows), E-MODEL (handler laws, `ewp_handle` as initiality). *Theorems* (`:2726`): `cancel_compatC` (`:2764`) corrected to `ewp_ccatch`/`cancel_frame`. *Lowering* (`:2839`) is restated as T-LOWER. *Open* (`:2960`): T1 (`:2966`) becomes OQ-2/OQ-9; generative names (`:2962`) OQ-14; finaliser policies (`:2968`) OQ-21; parameterised handlers (`:2971`) OQ-25; shallow handlers (`:2975`) OQ-26. |
| 19, recursion as an effect | §20 (`SPEC.md:2985`) | **kept** (K-FIX); the exhaustion effect "found by its structure" (`:3046`) and the heap driver "recognized by that type" (`:3068`) are shape recognition, OQ-6. Recursion through a site (`:3058`) is R-STATIC. |
| 20, fixed point of a generator | §21 (`SPEC.md:3134`) | **kept**: its principle ("effectful code is `!` code, and its environment is passed to it at each call", `:3153`) is the elaboration of K-HND's clauses, and its handler-with-a-state is T-ELAB's schema C2. *Open*'s "a handler around a div computation is not provided for any effect" (`:3272`) is replaced by K-HDIV (03 §9.2), in the calculus, its spanning form's lift deferred by R-HDIV (OQ-67). Layers (`:3190`) are recognised by type: OQ-6. |
| 21, the affine closure | §22 (`SPEC.md:3288`) | **kept** (K-NU); its effectful form (`affEffBody`, `Core/Aff.lean:155`) is under OQ-7. |
| 22, non-strict outlives | §23 (`SPEC.md:3463`) | **kept**; it is the outlives judgement OQ-28 extends to `U C` (or to boxed continuations). |

No SPEC entry numbered 23 exists on any branch (`main`, `lift-stage1`, `borrow-callbacks`,
`gfp-arising`): §23 is the last section. `Core/Gen.lean` (branch `lift-stage1`) cites
`[spec §24]`; that section is unwritten (§11).

### 4.2 The entries the calculus requires

Each is written before the kernel work it governs. Names are working names; numbers are assigned
when they land.

| entry | content | ids | gated by |
|---|---|---|---|
| **E-SIG** | one signature object; rows as sums (the first-match list modulo `Row.Uniq`); `opTable ⟦Σ⟧` as the one interpretation; optional equations | K-SIG, K-ROW, K-INT, K-THEORY | OQ-22 for equations |
| **E-W** | the world `W = (ρ, ls, σ)`, its order, `TabAt` as a `TW` invariant once T-ARISE.0 holds (OQ-45; a guard until then), **the relativised stop** (the kernel definition change of `Core/EffDefs.lean:40`), the re-indexed relation, with `vC`/`cC` equal to its `σ = []` instance by T-NIL, per introduction row (OQ-58) | D-W, D-ORD, D-ARISE, D-STOP, D-WPG, D-REL, D-SEM, T-MONO, T-NIL, T-STOP, T-ARISE | OQ-8, OQ-9, OQ-10, OQ-44 (what `σ` holds), OQ-45 (the guard), OQ-57 (`τ` beside `W`), OQ-58 (Core as the `σ = []` instance): all settled by Lean first; OQ-8 and OQ-58 have no default |
| **E-BOR** | one borrow constant per printed constant at every `TableOK` row; today's constants and `*U` twins as abbreviations; `TableOK` closed under sum; 6.64-6.66 and 6.150 lifted once | K-BOR, D-TABLEOK, T-FRAME, T-SUMOK, L-BOR | at abortive tables: none; at resuming tables: E-W |
| **E-MODEL** | `IsModel_Σ`; every computation type a model; `ewp_handle` as initiality; graded algebraicity; the handler laws over the kernel (unary halves) | D-MODEL, T-MODEL, L-ALG, L-ALG0, L-HRET, L-HOP, L-HFWD | OQ-11 for the `σ` of the statements |
| **E-COMODEL** | capabilities as comodels of the same `Sig`; `IsComodel_Σ`; `withswap` as carrier; the capability rule from HandlersAsBorrows | K-COMODEL, K-CAP, K-SWAP, D-COMODEL, T-COMODEL, L-STATE | OQ-1, OQ-19, OQ-20 |
| **E-REN** | renaming of names on terms, types, derivations and the relation; copies per assignment meaning-preserving; no accidental handling | K-REN, T-REN, L-REN, T-NAH | OQ-13, OQ-14 |
| **E-GEN** | K-GEN: `[gen]` (the §24 `Core/Gen.lean` cites) or the outlives rule at `U C` | K-GEN, K-HND, K-NU | OQ-28, OQ-46 |
| **E-BIN** | the binary relation | D-BIN, T-BINFP, T-SOUND, the binary halves of 06 | OQ-4 |
| **E-HOST** | host carriers: I/O capabilities as comodels; allocation (K-ALLOC); `Num[T]` (decision 54) | K-HOST, K-ALLOC | OQ-30, OQ-68 |
| **E-LOWER** | §19 *Lowering* restated as T-LOWER's classes with their laws | T-LOWER, L-TAIL | OQ-23 |

### 4.3 Decisions superseded or revised

| decision | (`docs/decisions.md`) | effect of the calculus |
|---|---|---|
| 48 | `:603` | **superseded** where it says "Effect rows never enter the core" (`:606`): rows are in the kernel (§19 already; the user's standing position that effects are core). PR #234 (`decision-48-wording`) corrects this line and is open. Its acceptance clause (per-class laws, counts, reports, "in place of an erasure theorem", `:608-610`) is OQ-23's option (a), kept as the default and stated as T-LOWER. Its staging S1-S5 (`:611-616`) is superseded by the order of 00 §6 and the issue plan. |
| 52 | `:649` | **superseded** by 55 (errors are `Fail` with `ctl raise`, not "a computation type, not a capability", `:657`); the abort laws it names live on as relabelled declarations (`Core/Handlers.lean:153-229`). |
| 53 | `:666` | **superseded**: its acceptance laws (`:667-669`) cover none of the current control schemas; T-ELAB replaces them. |
| 54 | `:675` | **kept** (tentative, the user's). It imposes K-HOST obligations: operators perform `Num[T]`, handled by an ambient outermost platform handler erased to the machine instruction (`:682`). In the calculus that handler is a host comodel (OQ-30), and its erasure is T-LOWER's call class at a known handler (L-TAIL). Its iteration bullet (`:676`) is L-YIELD and K-HND. |
| 55 | `:685` | **kept**, provisional; its kind split (`:686`) is OQ-55; its textual core (`:693`) gives the `*U` constants surface names that become K-BOR at a row. |
| 57 | `:706` | **revised in part**. "No row variables in the kernel" (`:707`) is OQ-13's default (a), unchanged. "A renaming lemma would let the checker derive once" (`:709`) becomes T-REN (E-REN), an obligation, not an aside. "Operations that take computations … are out of scope" (`:713`) is OQ-12's default (a), kept as R-FO, now a named restriction rather than a scope statement. Site freshness checked by the elaborator only (`:710`) is T-ABS's place (07). |
| 58 | `:715` | **kept** (K-FIX, L-FIX). Its "found by its structure" (`:733-734`) is OQ-6. "Partial correctness … considered and not taken" (`:731`) is OQ-15 (b)'s alternative, kept open there. |
| 59 | `:744` | **kept**. Its principle is the elaboration of clauses; `d_handleAbortCapture` is **promoted** (§3.3); its "Not built" list (`:766-770`) maps to OQ-25 (native handler parameter), K-HDIV with R-HDIV deferring its lift (recursion whose body loops, OQ-67), R-STATIC (recursion through a site). |

### 4.4 The entry drafts

Each entry is drafted in D-STOP's form (05 §4): *Current*, *Proposed*, *Why*, *What it does not
reach*, *Conservativity*. Where an entry is gated on an open question, the text is written at that
question's default, and the delta for each other option is stated. These drafts are the SPEC text
the kernel work cites; the issue plan lands each before the work it governs. E-W's stop clause is
D-STOP's draft (05 §4), not repeated.

> **E-SIG (draft): one signature, rows as sums.**
>
> *Current.* An operation is an `OpSig` keyed by `(n, i)` (`Core/Types.lean:147-152`); a row is
> `List OpSig` read by first match (`Row.find`, `Core/EffRules.lean:36`); `[then]` alone asks
> `Row.Uniq` (`effThen`, `Core/Fundamental.lean:360-365`); `thunkF` and `bangThunkF` introduce
> `U(F A)` only (`Core/Fundamental.lean:71, 125`), and `thunkV` excludes `F`-headed types, so no rule
> introduces `U(F_Σ A)` at a nonempty row (03 K-FTY). No equations.
>
> *Proposed.* (1) A signature `E = {op_i : A_i ↠^{q_i} B_i}` is one object, with optional
> equations `Eq(E)` (02 K-SIG, K-THEORY); `[sig]` as 02 writes it. (2) A row is a finite sum of
> named signatures with distinct names (02 K-ROW); its representation is today's list modulo
> `Row.Uniq`, every rule that builds a row normalising it (OQ-36 (a), canonical rows). (3)
> `opTable ⟦Σ⟧δ` is the one interpretation of a row (K-INT). (4) `effThen`'s premise `hUq` is deleted
> (true of every row). (5) `[thunkΣ]`, `[bangThunkΣ]`: `thunkF`, `bangThunkF` at every row (03 K-FTY).
>
> *Why.* Two signature objects (kernel `OpSig`, frontend `EffSig`) and first-match rows are the
> audit's C1 and §2.2; `U(F_Σ A)` is needed by effectful closures (01 §3.2) and is today written
> `U(1 ⊸ F_Σ A)`.
>
> *What it does not reach.* Row abstraction (R-NOROWVAR, OQ-13); self-referential signatures
> (R-NOSELFROW, OQ-61); scoped operations (R-FO, OQ-12); closedness of operation types in
> lifetimes (OQ-35, default: no premise).
>
> *Conservativity.* Every existing derivation maps to one at a normalised row with the same meaning
> (`cC_effOf` reads only the table, `Core/EffRules.lean:73-76`; 02 K-ROW's ROW-2, ROW-4); `[thunkΣ]`
> at `Σ = ∅` is `thunkF`. Deltas: OQ-36 (b) replaces normalisation by a conversion rule and its
> congruence lemma; OQ-22 (b) drops equations; OQ-35 (a) adds `Closed E` to `[sig]` and `[handle]`.

> **E-W (draft): the world, its order, the re-indexed relation.**
>
> *Current.* The relation is indexed by `ls` (`vCE`, `cC`, `Core/Relation.lean:119, 154`); the
> world order is `Ext` (`Core/FrameRecords.lean:172`); the lend stack exists only inside `wpG`'s
> frame quantifier (`Core/EffDefs.lean:28-29`) and in five relation families beside the kernel;
> `TabAtS` is a guard (`Stacked.lean:290`).
>
> *Proposed.* D-W: `W = (ρ, ls, σ)` with `Wf`. D-ORD: `(ls, σ) ⊑_ρ (ls', σ')` with conditions
> (1)-(5), `Relend` equality (OQ-9 (a)'s reading, which the default stop leaves unused). D-WPG:
> `wpG_W(τ)` with the premise `∀ e ∈ σ, e.imm → frameOf e ∈ ps`, `τ` an explicit index (OQ-57 (a),
> recorded as a defect). D-STOP: 05 §4's draft. D-TABLE: tables receive `(ls', σ)` and `τ'`. D-EWP:
> one least fixed point indexed by `τ`. D-REL: one clause per former at `W` at the candidate OQ-8
> settles on. D-SEM at every `W` with `TabAt_W` a premise. D-ARISE: `TabAt_W` a guard until
> T-ARISE.0 is proved, then a `TW` invariant (OQ-45).
>
> *Why.* One world for the relation, the laws and the metatheory (C-5); the five families retire
> into it (05 §9); the lend stack becomes data of the world instead of a relation parameter.
>
> *What it does not reach.* Which quantifier placement (OQ-8, no default: the entry does not land
> before it is settled); what `σ` holds of 6.65 lends (OQ-44, default GhostEnd-form entries); the
> stored payload's world (OQ-46, default longer-lived entries); `σ` under a fork (OQ-54).
>
> *Conservativity.* T-STOP and T-NIL: at `σ = []`, `τ = []` and the default stop, every definition
> that reads no extension of the world is today's by `rfl`; `vC`/`cC` equal the `σ = []` instance
> by T-NIL, per introduction row, which is **unknown** at `U`, `share` and `KapRel` (OQ-58, no
> default). If OQ-58 fails (its option (b)), the entry redefines Core's `vCE` thunk clause as the
> new clause and every Core theorem is re-proved through T-FP at `W`. Deltas: OQ-9 (b) keeps the
> stop, sets `Relend = ReLend`, and takes the "-rebase" `U` clause (05 §7); OQ-57 (b) replaces the
> `τ` index by a `closer` field of each entry; OQ-45 (b) drops the guard.

> **E-BOR (draft): one borrow per printed constant at every `TableOK` row.**
>
> *Current.* A pure rule and an unwinding twin per constant (`Core/Fundamental.lean:239-294`), the
> twins gated by `Row.Unwind` (`Core/EffBorrow.lean:133`), each with its own compatibility lemma.
>
> *Proposed.* `bor_k[Σ]` for each printed constant `k`, at any callback row in `BorOK_x Σ`, with the
> finaliser premise at `Σ.Weak` (03 K-BOR). D-TABLEOK as 05 writes it. T-FRAME: 6.64-6.66 and 6.150
> lifted once to `ewp_W` at every `TableOK_x` table. T-SUMOK. The pure constants are `bor_k[∅]`
> and the `*U` twins are `bor_k[Σ]` at `Row.Unwind x`, both as abbreviations.
>
> *Why.* C-6 (one borrow per printed constant); a callback at `Fail ⊕ Yield` fits no class today
> (audit C4).
>
> *What it does not reach.* At the defaults R-T1 and R-CLOSEDOP, `BorOK_x Σ` is today's
> `Row.Unwind x`: only abortive operations cross a borrow, with closed operation types. Resuming
> rows need E-W and OQ-9; lifetime-polymorphic operations are OQ-56; finalisers that perform are
> R-FINAB (OQ-7).
>
> *Conservativity.* At R-T1 and R-CLOSEDOP every existing derivation is an instance (the
> abbreviations are closed `CDerives` coercions, 03 K-BOR *Obligation*). Deltas: removing R-T1
> (OQ-2 (b)) needs E-W and T-FRAME at resuming tables; OQ-56 (b) adds `[perform∀]` and the
> lifetime-polymorphic clause type (03 K-BOR); OQ-7 (a) widens `d` to `F_Σ 1`.

> **E-MODEL (draft): handlers as models; the handler laws over the kernel.**
>
> *Current.* `ewp_handle` (`Core/EffRules.lean:615`) is a five-case analysis with hypotheses
> `hret`, `hop`; no `IsModel`; the handler laws exist over the kernel only as steps and run facts,
> and algebraically only in the sibling calculus.
>
> *Proposed.* D-MODEL (`IsModel`, named from `ewp_handle`'s hypotheses at `W`); T-MODEL: (M1) every
> computation type is a model, (M2) `ewp_handle` as initiality of the least fixed point among
> models, (M3) graded algebraicity; the unary halves of L-ALG, L-ALG0, L-HRET, L-HOP, L-HFWD,
> L-HUNIQ (with its added hypothesis (H0)), L-HBIND, L-W, stated over D-EWP at `W`.
>
> *Why.* The sign-off: handler laws stated and proved over the kernel relation (00 §0.3); one
> `IsModel` lemma replaces the four encodings of algebraicity (audit M11, M12).
>
> *What it does not reach.* Binary halves (OQ-4, default: stated, marked not proved); carriers
> other than `F_Σ R` (R-RETCARRIER, OQ-37); shallow handlers (R-DEEP, OQ-26); a handler between two
> lenders (R-MID, OQ-3).
>
> *Conservativity.* `ewp_handle`'s statement is (M2) with its hypotheses renamed; no derivation
> changes. Deltas: OQ-37 (a) states D-MODEL at a target `𝒞⟦C⟧_W`; OQ-3 (a) gives the handler a
> lifetime and a world entry; OQ-11 (c) marks laws proved only at `σ = []`.

> **E-COMODEL (draft): capabilities as comodels of the same signature.**
>
> *Current.* Answering effects are `withswap` calls checked by no table (audit C2); the capability is
> derived in the elaborator (SPEC §18 *Elaboration*); HandlersAsBorrows proves the translation typed
> and safe over `DerivesWf`.
>
> *Proposed.* K-COMODEL (02): co-operations `c_i : U(S ⊗ A_i ⊸ F(S ⊗ B_i))` typed from `Σ`; K-CAP
> (`[cap-install]`, `[cap-call]`) as derived rules over `withbor2` and `withswap`; D-COMODEL
> (`IsComodel` over `opTable ⟦n:E⟧`); T-COMODEL; L-STATE, L-RUN's unary halves.
>
> *Why.* One signature, two implementations (C-3); a capability's protocol checked against the same
> `opTable` entry as a handler's.
>
> *What it does not reach.* At the defaults: OQ-1 (b), both primitive, one protocol; OQ-19 (a),
> state access only, no runner construct; OQ-20 (a), a pure callee, so a capability cannot fail
> (R-PURESWAP); OQ-29 (a), no borrowed answers.
>
> *Conservativity.* No kernel rule changes at the defaults: K-CAP's rules are derived. Deltas: OQ-1
> (a) makes the capability a tail-resumptive `[handle]` and puts its effect in rows; OQ-20 (c) adds
> `withswap[Σ]` (03 §9.11); OQ-20 (b) adds no constant (a derived term over `withswap`, 03 §9.11).

> **E-REN (draft): renaming of names.**
>
> *Current.* No renaming of names in Core; decision 57 records that copies per name assignment are
> typing artefacts a renaming lemma would justify (`docs/decisions.md:709`).
>
> *Proposed.* K-REN (02) on rows, types, terms, contexts, heaps, derivations and worlds (`π·W`);
> T-REN (statics, machine, relation at `π·W`), L-REN, T-NAH.
>
> *Why.* Copies per assignment are then meaning-preserving when they differ by a renaming; no
> accidental handling holds over the kernel.
>
> *What it does not reach.* Copies at structurally different rows (R-NOROWVAR: separately checked,
> no relating theorem; OQ-13 (a') would add a meta-level substitution lemma); generative instances
> (R-STATIC, OQ-14); site freshness as a kernel premise (OQ-38, default: the elaborator's).
>
> *Conservativity.* Adds lemmas only. Deltas: OQ-13 (b) replaces renaming by substitution at
> `[rowE]`; OQ-38 (a) adds `n ∉ names(Γ₂) ∪ names(A)` to `[handle]`.

> **E-GEN (draft): a stored continuation.**
>
> *Current.* `κ` has no `CDerives` rule and `U C` no outlives rule; `[gen]` exists on branch
> `lift-stage1` (`Core/Gen.lean`) at `Tout = ∅`, citing an unwritten `[spec §24]`.
>
> *Proposed (OQ-28 default (a)).* K-GEN option (a): `[gen]` as a rule at a row `Σ`, answer
> `F_Σ((B_y ⊕ 1) ⊗ [@c] U(Aff^c_Σ A (B_y ⊕ 1)))` (03 K-GEN), with `gen_compatC`.
>
> *Why.* A continuation that holds a borrow must be bounded by it when stored (OQ-28), and the box
> cannot be introduced at `U C` otherwise.
>
> *What it does not reach.* The world a stored payload is read at (OQ-46); a continuation stored
> across a lend opened inside it needs R-T1 lifted.
>
> *Conservativity.* A new rule; no existing derivation changes. Delta: OQ-28 (b) replaces the rule
> by an outlives rule at `U C` and `K_q`, which changes SPEC §23's outlives judgement to read a
> derivation, and derives `[gen]`.

> **E-BIN (draft): the binary relation.** Conditional on OQ-4, whose default (b) does not build it.
>
> *Current.* None on Core (audit T16).
>
> *Proposed (only under OQ-4 (a)).* D-BIN: `≈` over pairs of worlds along a partial bijection of
> locations, the clauses of D-REL read on two runs; T-BINFP, T-SOUND.
>
> *Why.* The binary halves of the laws not reachable by T-SI2 (06 §10).
>
> *What it does not reach.* At the default (b), nothing is built: binary halves are stated and marked.
>
> *Conservativity.* Adds a relation and lemmas; no kernel definition changes. Delta: OQ-4 (c)
> withdraws the entry.

> **E-HOST (draft): host carriers and allocation.**
>
> *Current.* Host operations are pure constants (`Core/Fundamental.lean:160-161`); I/O is a bundle of
> capabilities (SPEC §11); allocation is the machine's oracle (SPEC §13).
>
> *Proposed.* Each host effect a signature whose implementation is a host comodel (K-HOST); K-ALLOC
> at OQ-30's default (b'), allocation a heap capability, colouring no function type; `Num[T]`
> (decision 54) as a host comodel erased to the instruction.
>
> *Why.* Alloc is an effect (U20, decided); I/O is per-effect capabilities (U20).
>
> *What it does not reach.* The lift of K-ALLOC waits on OQ-68 (R-ALLOCORACLE until then); the BoLo
> world as one comodel (OQ-34, default not adopted); adequacy at a row (OQ-51, default `F 1`).
>
> *Conservativity.* Until OQ-68, allocation stays the oracle and every derivation is unchanged.
> Delta: OQ-30 (b) puts `Alloc[T]` in rows.

> **E-LOWER (draft): the lowering classes.**
>
> *Current.* SPEC §19 *Lowering* describes the classes; decision 48's acceptance (per-class laws,
> counts, reports).
>
> *Proposed (OQ-23 default (a)).* T-LOWER's classes with their laws (§6): direct call (L-TAIL),
> branch (L-ALG0), state machine (L-HOP, L-ALG), copy (L-P), and the classes of the constructs §6
> adds; cost parity against `corpus/kernel-counts.expected` as the criterion.
>
> *Why.* Effect handling is erased (U6); the compiler is never stale.
>
> *What it does not reach.* OQ-42's default leaves three constructs unlowered, a restriction of U6
> and "compiler never stale" (§6, OQ-42); lowering correctness as a theorem is OQ-23 (b).
>
> *Conservativity.* No kernel definition changes. Delta: OQ-42 (a) adds a run-time mask; OQ-23 (b)
> adds a compiler-correctness theorem.

---

## 5. The surface

### 5.1 Handler schemas

Each schema, its elaboration site, the kernel construct it must be, and its T-ELAB obligation.

| schema | elaborated by | kernel construct | T-ELAB obligation |
|---|---|---|---|
| A1: answering handler, state made at the block | §18 table (`SPEC.md:2127-2130`): a `withbor` of the state's cell, clauses `withswap` | K-CAP (a comodel lent by K-BOR) | T-ELAB.comodel; run half exists (`op_tail`, `op_answer`, `handle_fold`, `Core/Handlers.lean:76, 133, 211`); protocol half (T-COMODEL) **unknown** under OQ-1 |
| A2: answering handler, state lent from a cell `with h(&mut c₀)` | same, `borrow mut c₀` (`SPEC.md:2129`) | K-CAP at `withbor3`'s form | as A1 |
| C1: control handler, every operation abortive ("abort-after") | `withCtl` (`Frontend/Elab/Effects.lean:1398`), branch at `:1473`, report at `:1520` | K-HND whose clauses run after it: `d_handleAbortCapture` (`experiments/SecondClass/SecondClass/AbortClause.lean:69`) | T-ELAB.model: L-HRET, and L-HOP at arity 0 (the clause on the payload); **mechanical** from `d_handleAbortCapture` once promoted |
| C2: control handler with a state ("stateful") | `withCtl`, `stateful` at `Frontend/Elab/Effects.lean:1541` | K-HND at the carrier `U(S ⊸ F_Σ(S' ⊗ R))` (SPEC §21, `SPEC.md:3233`) | T-ELAB.model at a state-passing carrier: **unknown** (§1, T-ELAB); OQ-25 |
| C3: control handler, plain | `withCtl`, from `Frontend/Elab/Effects.lean:1599` | K-HND with `!` clauses (`effHandle`, `Core/Fundamental.lean:367`) | T-ELAB.model: the H-laws as instances; **mechanical** once T-MODEL exists |
| F: `for` over a generator (for-site) | `forSite` (`Frontend/Elab/Effects.lean:1666`), assembled by `forYield` (`Frontend/Sugar.lean:3871`) | K-HND for an iteration effect, the loop variables threaded through the operation (SPEC §15) | T-ELAB.model with the threaded state as the carrier, as C2; `break`/`return` as cancel: L-W. **unknown** for the same reason as C2 |
| P: stored generator (pull-site) | `pullSite` (`Frontend/Elab/Effects.lean:1706`), `pullView` (`Frontend/Sugar.lean:4075`) | K-HND whose clause keeps `κ` as the rest of `ν` codata `pull A B R` (decision 56, `docs/decisions.md:701`); the shallow-handler reading (audit §3.5) is OQ-26 | T-ELAB.model with `κ` stored: K-KONT's storage rule (OQ-28); the `[gen]` rule (E-GEN) is the kernel form |
| R: recursive group | `recGroupsOf`, `defineGroup` (`Frontend/Elab/Effects.lean:2111, 2158`), `groupCopy` (`:1846`) | K-FIX at the record of members (SPEC §21) | not a handler; T-ELAB.typed only, plus L-FIX |
| L: layer | `layerCopy` (`Frontend/Elab/Effects.lean:1794`) | K-FIX at a transformed generator | T-ELAB.typed; recognised by type (OQ-6) |
| D: heap driver `deep` | `recMachine`, `rmWalk` (`Frontend/Sugar.lean:2841, 2739`), `deepCopy` (`Frontend/Elab/Effects.lean:1951`) | K-NU (a `Loop` over a frame buffer) | T-ELAB.typed; recognised by type (OQ-6) |
| copies per assignment | `copyFor` (`Frontend/Elab/Effects.lean:1763`), `copyOf` (`:2015`; `Frontend/Sugar.lean:4570`), `makeInst` (`Frontend/Sugar.lean:4244`) | monomorphisation over static names (R-NOROWVAR) | T-REN makes them meaning-preserving (E-REN) |

### 5.2 Glue to replace

| item | where | stands in for | replaced by |
|---|---|---|---|
| shape recognisers `iterEff`, `exhEff?` (takes the first declared match), `driver?`, `isLayerTy` | `Frontend/Elab/Effects.lean:229, 240, 250, 260` | typed role declarations | OQ-6 (default: shape recognition, ambiguity rejected; `exhEff?`'s first match is then an error) |
| the binder `io_bt` | `Frontend/Parser.lean:832, 1146-1149, 1213-1216`; `Frontend/Sugar.lean:1938, 3705`; `Frontend/Elab/Effects.lean:1387, 1404` | a typed field on the desugared block, or a reborrow of outer places at the `with` (audit m4) | a typed field (surface work under #188) |
| ambient `stdin`/`stdout`/`stderr` by name | `Frontend/Parser.lean:1142, 1210`; `Frontend/Sugar.lean:72` (`capNames`) | platform bundles (#156) | K-HOST comodels in a bundle (OQ-30) |
| two row computations, E1 by name and E2 by `(n, i)` | `rowV`, `rowC` (`Frontend/Elab/Effects.lean:418, 454`); `opsC`, `opsV`, `fnRowOf` (`Frontend/Sugar.lean:2530, 2545, 2478`) | one row function | one shared function computing `Σ` (02's requirement on 08; audit §2.2), with a lemma that the elaborated term's row is it |
| the `fn`/`ctl` kind per effect | `EffSig.answering` (`Frontend/Elab/Effects.lean:63`) | one signature with two implementations | OQ-55 |

### 5.3 Obligations of the surface issues

| issue | obligation the calculus puts on it |
|---|---|
| #188 (surface and corpus onto native handlers) | every handler schema meets T-ELAB; no library effect name in `Frontend/` (its acceptance) is C-7; the frontend `EffSig` is the surface of E-SIG's `Sig`, and the elaborated row is computed once (§5.2) |
| #155 (S2a, named capabilities and lexical resolution) | two instances of one effect in a row: K-ROW's distinct names already admit them; resolution between them is K-NAME's static resolution; generative instances only under OQ-14 (b) |
| #156 (S2b, I/O and platform bundles) | K-HOST under OQ-30: a bundle is a record of comodel capabilities; `main`'s ambient capabilities are the outermost host carriers |
| #160 (S4b, projection operations) | an operation answering a borrow into handler state is OQ-29 (default R-NOBORANS) |
| #161 (S4c, stored effectful callbacks) | in the calculus by design (00, header): a thunk `U(A ⊸ F_Σ B)` stored and called is K-FTY; what blocks the surface is rows as a meta-index (OQ-13, whose Blocks include the reconciler chain's generic combinators, §9.1) and, for a stored callback holding a lend, OQ-2/OQ-28 |
| #215 (linear abortive payloads) | OQ-24 |

---

## 6. The lowering

Effect handling is erased at run time; the lowering is two passes over the closure IR,
`Backend/Clos/Capture.lean` then `Backend/Clos/Unwind.lean` (SPEC §19 *Lowering*,
`SPEC.md:2841`). Each row gives the construct, its class (T-LOWER), the law that justifies the
class, and where it is built.

| construct | class | law | built in |
|---|---|---|---|
| K-RAISE, a handler of an all-abortive name | branch per call; the handler a `catch` | L-ALG0, L-EXC | `abortiveSite` (`Backend/Clos/Capture.lean:192`); `Prog.unwind` (`Backend/Clos/Unwind.lean:375`), `propagateOn` (`:190`), `UFacts.raises` (`:123`) |
| several abortive payload types | one payload variant | — (a representation) | `wrapRaise` (`Backend/Clos/Capture.lean:136`) |
| K-THEN | `fin D M`, `N` and `D` one code | L-ALG0 (D-DTOR) | `finalise` (`Backend/Clos/Unwind.lean:206`); `markUbinds` (`Backend/Clos/Convert.lean:448`) |
| K-OP under a control handler | state machine: a code that may suspend answers `inl v` or `inr (p, k)`; state one variant per resumption point | L-HOP; L-ALG's unary form (the state holds `K`'s live variables) | `machine` (`Backend/Clos/Capture.lean:940`), `MEnv.resumeCode` (`:923`), `collectPoints` (`:709`), `MEnv.suspend` (`:774`) |
| K-HND with control operations | `drive`: value to `h_ret`, own operation to its clause with `κ`, other operations forwarded | L-HRET, L-HOP, L-HFWD | `controlSite` (`Backend/Clos/Capture.lean:241`), `drvBody` (`:207`), `kapBody` (`:233`); the interpreter's `drive` (`Backend/Clos/Interp.lean:484`) |
| a tail-resumptive operation with one closed clause | direct call, `κ` not materialised | L-TAIL | `tailResumptive` (`Backend/Clos/Capture.lean:631`), `tailClause?` (`:542`), `directCalls` (`:611`) |
| K-CAP, K-SWAP (answering) | a call on the capability | L-STATE; `op_tail` (`Core/Handlers.lean:76`) | ordinary calls (SPEC §19 *Lowering*, `SPEC.md:2857`) |
| K-CANCEL | the state's destructor: callee's `k` first, then the point's finalisers innermost first; the first error outside the mask kept | L-W, L-SIGNAL; OQ-21 for the policy | `MEnv.cancelArm` (`Backend/Clos/Capture.lean:893`), `errNext` (`:875`), `masks` (`:986`) |
| K-KONT at `unr` resumed twice | the closure IR's copy | L-P (captures persistent) | ordinary copy (SPEC `:2927`); #208's note "multi-shot works" |
| K-FIX | two codes, a stack closure per level | L-FIX | `fixValue` (`Backend/Clos/Convert.lean:228`) |
| K-NU, K-DIV | one state machine per body (SPEC §14 *One state machine per body*, `SPEC.md:1326`) | L-DIV | the same machine |
| a handler with a state (schema C2) | a dispatched call per resume | L-HOP at a state-passing carrier (unknown, §1) | SPEC §21 *Lowering* (`SPEC.md:3251`) |
| K-LET (`M to x. N`) | ordinary sequencing: no code beyond the continuation; at a row, the point after `M` is a resumption point of the state machine when `M` may suspend | L-TO; L-ALG (the state holds `K`'s live variables) | `machine` (`Backend/Clos/Capture.lean:940`) when `M` may suspend; ordinary code otherwise |
| K-BOR, pure form | no code: lends are ghost, the constant is its λ-term | L-NUB-style identity (lends ghost, 04 §4); L-BOR's abortive half for the unwinding form (above, K-THEN) | ordinary code (`Backend/README.md`) |
| K-HOST (host operations, I/O capabilities) | a call of the host function | L-TAIL at the host's outermost handler (its clauses resume once in tail position); L-RUN for a host capability | `host` steps; the I/O bundle (SPEC §11) |
| K-ALLOC (in the calculus; lift after OQ-68) | the allocator call; an arena's `new` a bump | L-TAIL at the host handler; L-RUN under OQ-30 (b'); L-HOP at an arena's clause | the allocator (SPEC §13) |
| K-FTY: `[thunkΣ]`, `[bangThunkΣ]` (a thunk at a row) | a closure; forcing it is a call that may suspend, so a resumption point of the caller's state machine | L-UF (β), L-ALG at the force | ordinary closures (`Backend/Clos/Convert.lean`); `machine` (`Backend/Clos/Capture.lean:940`) at the force |
| K-GEN (a stored continuation) | a state-machine value: the closure IR's `κ`, `call` its resume arm, `close` its cancel arm | L-BETA, L-W | `kapBody` (`Backend/Clos/Capture.lean:233`), `MEnv.cancelArm` (`:893`) |
| K-HDIV | per observation: one state machine per body, as K-NU; spanning: the unfold state holds the handler state and any stored `κ` | L-DIV, L-HOP; L-BETA, L-W at a stored `κ` | the same machine; spanning form not built |
| K-FOLDΣ (under OQ-62 (b)) | the fold's code when the step cannot suspend; when it can, a state machine holding the traversal's pending levels (an explicit frame buffer, as schema D's `Loop`) | L-FOLD, L-ALG | not built |
| K-SCOPE (not adopted) | as K-OP at the perform (state machine, or direct call when tail-resumptive in the continuation); the scope a closure passed to the clause | L-HOP, L-SCOPE, L-TAIL; scope handling OQ-59 | not built |
| K-CARRIER (not adopted) | at `S ⊸ F_Σ R`: a dispatched call per resume with the state as an argument, no closure per operation; at `C & D`, one code per component | L-HOP at carrier `C` | not built; today's encoding is SPEC §21 *Lowering* (`SPEC.md:3251`) |
| K-BORANS (not adopted) | as K-OP: the answer is a location, the lend has no code | L-HOP, L-HIDE | not built |
| K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ, K-SWAPΣ, K-SELFROW, K-GENNAME (not adopted) | as each 03 §9 entry's *Lowering* states | as stated there | not built |

**Cost parity** is the criterion: `corpus/kernel-counts.expected` against the hand-written
`corpus/capture-log-hand.bc`, `capture-tick-hand.bc`, `capture-take-hand.bc`,
`capture-store-cancel-hand.bc` (SPEC table, `SPEC.md:2950-2955`).

**What the calculus has that the lowering does not lower.** "Compiler never stale" asks every
construct to land with its lowering. The calculus admits each of the following; the lowering
rejects them (SPEC §19 *Not lowered*, `SPEC.md:2937`; #208 item 3):

1. a name with both control and abortive operations: K-SIG allows it (an operation's arity and
   qualifier are per operation, O-SIG), and K-ROW's sum makes such a name ordinary;
2. a cancel whose finalisers may raise under a handler site reached again from its own body;
3. a handler name `≥ 64`: the mask is a `UInt64` (`kapBody`, `Backend/Clos/Capture.lean:233`).

Each is a lowering obligation of T-LOWER, not a restriction of the calculus, and needs an issue.
OQ-42's default leaves the three unlowered, which restricts two decided positions, "compiler never
stale" and U6 (effect handling is erased); the register records it as such (OQ-42), and its option
(a), a run-time mask where the static one is inexact, is the lowering that meets them.
The other lowering gaps: recursion through several codes costs one object per code per level
(#208 item 1); a tail-resumptive clause that captures values is a state machine, not a direct
call (#208 item 2; the evidence-passing technique: Xie, Brachthäuser, Hillerström, Schuster &
Leijen, *Effect handlers, evidently*, ICFP 2020, whose abstract states that evidence passing lets
tail-resumptive operations execute "in place (without needing to capture the evaluation
context)" [read: the abstract, microsoft.com publication page]); the state as a flat `n`-ary tag
in the frontend's generators (#129, #208 item 4).

**What the calculus adds to the lowering.** Under E-BOR a borrow's callback may perform resuming
operations (at R-T1's removal, OQ-2): a suspension inside a borrow then holds an open lend in the
state, and cancel ends it by the unwinding form's finaliser (SPEC `:2908`: "borrows' unwinding
forms are finaliser frames, so their lends end here"). The lowering already treats unwinding
borrows as finaliser frames; what changes is that a state may hold one across a suspension. No new
class is needed; the obligation is that the state machine's cancel arm runs the frame's
finaliser, which `MEnv.cancelArm` does for every `fin` frame of the point.

---

## 7. Threads: what keeps the door open

Threads are required eventually. Nothing below designs them; each item names a choice in the
calculus that would close the door if made differently, and what keeps it open.

1. **`κ` is a value of statically known size** (SPEC `:2873`; `kapBody`). A suspended computation
   can be handed to a scheduler as data, with no stack switching, which is the portable reading.
   Handlers can express lightweight threads (Sivaramakrishnan, Dolan, White, Kelly, Jaffer &
   Madhavapeddy, *Retrofitting effect handlers onto OCaml*, PLDI 2021: "effect handlers allow for
   … async/await, lightweight threads and coroutines to be composably expressed" [read: the
   abstract, arXiv 2104.00250]); the calculus keeps that available by keeping `κ` first class
   (K-KONT) and its lowering a value (T-LOWER).
2. **Rows are sums; disjoint capabilities are tensor** (OQ-18 default (a)). The tensor law
   (L-TENSOR) is the commutation a scheduler relies on to interleave operations on disjoint
   state; it is stated for capabilities from disjoint borrows, which BoLo's separation of `ρ`
   already makes disjoint. Rows as sums keep operations of distinct names ordered, which is what a
   single thread needs. How rows combine at a thread boundary has no source here: operations of
   concurrent threads on shared state do not commute, and the standard models of concurrency
   (resumptions, interleavings) are not tensors; this is boxed under OQ-18.
3. **Cancel is uninterceptable and finalising** (L-SIGNAL). Cancelling a thread is the same
   construct as cancelling a `κ`: the uninterceptable name `⊥`, finalisers run LIFO. An
   Ahman-Bauer signal sent by a runner's own co-operation also skips the rest of the user code and
   runs that runner's finalisation (`kill s ↦ N_s`); only an enveloping runner's signal bypasses
   it, and a signal discards the kernel state (06 L-SIGNAL). Whether our cancel is an instance is
   OQ-66; #235's reading of decision C as one (L4/L5-K) is that report's inference [I].
4. **Adequacy under every allocator** (`adequacyD`, `Core/Demonic.lean:312`; `total_every_run`,
   `Core/Totality.lean:64`) is a demonic, every-run statement; under threads the same form ranges
   over every scheduler. T-ADEQ is to keep that form.
5. **Determinism is used, and would not survive threads.** T-DET (`head_det_eff`,
   `Core/Steps.lean:596`) and TwoRun's determinism up to renaming (`freshRun_det`) are what OQ-4
   (b) uses to avoid a binary relation. A law proved by that route holds of a sequential run; under
   threads it would need restating. Laws proved over `≈` (OQ-4 (a)) do not depend on determinism.
6. **The lend stack `σ`.** D-W makes `σ` one LIFO stack. A fork splits `ρ` by `⋆`; whether `σ`
   splits with it, or becomes a forest, is not decided by anything in the calculus: OQ-54.
7. **Handler state.** A handler's state shared between threads would be a `Mut` aliased across
   them, which BoLo excludes; OQ-25 (b) (comodel state in a cell) makes handler state a lent cell,
   so sharing it is the same question as sharing any cell (interior mutability, open by the
   user's position).
8. **Static names.** A spawned thread that installs handlers installs sites; with static names
   (R-STATIC) two threads running one site's code share its name. That is harmless while names
   are resolved lexically per thread; per-thread instances are OQ-14 (b).
9. **Allocation** as an effect (OQ-30 (b)) admits per-thread arenas as nested handlers.

---

## 8. The completeness check: not an approximation

01's checklist, items C-1 to C-12 (01 §7), checked against the ids:

| item | ids that carry it | holds in the specification? | today |
|---|---|---|---|
| C-1. one signature object | K-SIG, K-ROW | yes: O-SIG, one object; the frontend `EffSig` is its surface (§5.2) | two objects (`Core/Types.lean:147`; `Frontend/Elab/Effects.lean:57`) |
| C-2. one interpretation | K-INT, D-OPTAB | yes: every construct enters the relation through `opTable ⟦Σ⟧` (00 §6) | answering effects are checked by no table |
| C-3. models and comodels of it | K-MODEL, K-COMODEL, D-MODEL, D-COMODEL, T-MODEL, T-COMODEL | yes, with OQ-1 deciding whether the comodel case is derived | models only |
| C-4. laws over the kernel relation | every L id, unary half over D-EWP at `W` (OQ-11) | yes for the unary halves; binary halves wait on OQ-4 | off-kernel (EffModelRel) |
| C-5. one world | D-W, D-ORD, T-MONO | yes, with two items open: the closing-obligation index `τ` beside `W` is recorded as a defect (OQ-57), and `vC`/`cC` are the `σ = []` instance only by T-NIL's per-row proof (OQ-58); the five stacked families retire into it after 05 §9's equivalences (§3.5) | `ρ`/`ls` in the kernel plus `σ`/`αs` in GhostEnd |
| C-6. one borrow per printed constant | K-BOR, D-TABLEOK, T-SUMOK | yes; pure and `*U` constants abbreviate | pure constants plus `*U` twins |
| C-7. no construct recognised by name | T-ELAB; §5.2 | yes in the specification: the kernel recognises nothing by name; the elaborator finds roles by structure with ambiguity rejected (OQ-6's default, which C-7 admits) or by declaration; the name-keyed glue of §5.2 (`io_bt`, `capNames`) and `exhEff?`'s first-match rule are replaced | name-keyed glue (`Frontend/Parser.lean:832`, `Frontend/Sugar.lean:72`); first-match recogniser (`Frontend/Elab/Effects.lean:240`) |
| C-8. every construct complete | every K id | yes, in the specification: the per-construct table below names every facet, including the lowering class, for every K id, the not-adopted constructs of 03 §9 included; facets that cannot be written yet are boxed (OQ-59 for K-SCOPE's clause, OQ-37 for `(νX. C)_1`, OQ-61 (c)-(d), OQ-13 for K-ROWABS's table predicate) | — |
| C-9. no step index, no new mechanism | T-DEF; D-W | yes: T-DEF under OQ-31's cut-offs; the five relation families beside `vC`/`cC` retire into `W` (§3.5); no twin constant survives (§2.2) | five families; `*U` twins |
| C-10. every narrowing named | 00 §7.2 | yes: every default that narrows the calculus is an R id cited at its construct (including R-CLOSEDOP, R-NONEGREC, R-DEEP, R-NOREL, R-EXACTQ, R-NOSELFROW, R-PUREFOLD), every restriction of the equational theory and metatheory is an R id (R-ETALIN, R-INTERLIN, R-FUSETAIL, R-LINRES, R-ADEQF1, R-ALGPLAIN), the restrictions of decided positions are recorded as such (R-HDIV for U5, R-ALLOCORACLE for U20, OQ-42's default for U6), and the full construct behind every R id of a construct is written in 03 §9 (K-SCOPE, K-HDIV, K-CARRIER, K-BORANS, K-ALLOC, K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ, K-SWAPΣ, K-SELFROW, K-FOLDΣ, K-GENNAME, K-NEGREC), or in its own entry (R-T1, R-MID, R-CLOSEDOP, R-EXACTQ); OQ-43 and OQ-47 limit proof routes only | — |
| C-11. every kernel definition change has a SPEC entry | §4.2, §4.4; 05 §4; 00 §3.5 | yes: every changed or new id is governed by an `E-*` entry whose text is drafted (D-STOP in 05 §4; E-SIG, E-W, E-BOR, E-MODEL, E-COMODEL, E-REN, E-GEN, E-BIN, E-HOST, E-LOWER in §4.4), each at its gating question's default with the delta per option. E-W cannot land before OQ-8 and OQ-58, which have no default | — |
| C-12. the user's decisions at their strength | 01 §4 | yes, by the check of each quotation (01 §10) | — |

**Per construct: syntax, statics, dynamics, model clause, laws, compatibility.** A construct with a
missing facet is incomplete (00 §0.2 item 4). "R" marks a facet stated in full with a named
restriction applying by default.

| construct | syntax (03/04) | statics (03) | dynamics (04) | model (05) | laws (06) | compat (07) | lowering class; law (§6) |
|---|---|---|---|---|---|---|---|
| K-OP | `perform` | K-OP | `[op]` | D-OPTAB | L-ALG, L-GEN, L-HOP | T-COMPAT | state machine, or direct call; L-HOP, L-TAIL |
| K-RAISE | `raise` | K-RAISE (R-NOOWNERR) | `[unwind]` | D-OPTAB | L-ALG0, L-EXC | T-COMPAT | branch; L-ALG0 |
| K-LET | bind | K-LET, K-GRADE | — (pure) | D-EWP | L-TO, L-ALG | T-COMPAT | sequencing / resumption point; L-TO, L-ALG |
| K-THEN | `ubind` | K-THEN (R-FINAB) | `[then]`, `[finalise]`, `[finalise-cancel]` | D-DTOR | L-ALG0, L-W | T-COMPAT | finaliser frame; L-ALG0, L-W |
| K-HND | `hnd` | K-HND (R-MID, R-DEEP) | `[ret]`, `[op]`, `[unwind]` | D-MODEL | L-HRET, L-HOP, L-HFWD, L-HUNIQ, L-HBIND, L-HFUSE, L-HCORR | T-COMPAT via T-MODEL | `drive`; L-HRET, L-HOP, L-HFWD |
| K-KONT | `kappa` | K-KONT (R-NOREL) | `[cancel]` | D-SHARE, D-KAP, D-OWED | L-W, L-C, L-P, L-BETA | T-COMPAT | the state's resume/cancel arms; copy at `unr`; L-BETA, L-W, L-P |
| K-CAP | (derived) | K-CAP | `withswap` steps | D-COMODEL | L-STATE, L-RUN, L-TENSOR, L-INTER | T-COMPAT via T-COMODEL | a call; L-RUN, L-STATE |
| K-SWAP | `withswap` | K-SWAP (R-PURESWAP) | as built | D-COMODEL | L-STATE | T-COMPAT | a call; L-STATE |
| K-BOR | `bor_k[Σ]` | K-BOR (R-T1, R-CLOSEDOP, R-FINAB) | as built | D-TABLEOK | L-BOR | T-COMPAT via T-FRAME | no code (pure form) or finaliser frame (unwinding form); L-BOR |
| K-FIX | `bounded_fix` | K-FIX (R-NONEGREC) | `[boundedFix]` | D-REL | L-FIX | T-COMPAT | fixed point; L-FIX |
| K-NU | `unfold`, `nuIn`/`nuOut` | K-NU | as built | D-REL (`ν` clause) | L-NUB, L-DIV (codata laws) | T-COMPAT | one state machine per body; L-DIV |
| K-DIV | (reading of `Loop`) | K-DIV | as K-NU | as K-NU (D-EWPP under OQ-15 (b)) | L-DIV | as K-NU | as K-NU |
| K-HDIV | `hndLoop`, `hndLoopS`; `[fix]` under (b) | 03 §9.2 (R-HDIV defers the spanning form's lift) | none new; `[fix]` under (b) | `ν` clause at `W`; `ewpP_W` under (b) | L-DIV, L-HOP, L-BETA, L-W | T-COMPAT (Rows E) | one state machine per body; L-DIV |
| K-GEN | `[gen]` or `boxI` at `U C` | 03 K-GEN (OQ-28) | none new | D-KAP at a boxed `κ` | L-BETA, L-W at a stored `κ` | T-COMPAT (Rows G) | a stored state-machine value; L-BETA, L-W |
| K-FOLDΣ (not adopted) | the fold constants at a row | 03 §9.13 (R-PUREFOLD) | the fold terms, `Head.count` | `ewp_W` per level | L-FOLD | T-COMPAT (Rows E) | fold code or state machine; L-FOLD |
| K-CANCEL | `ccatch`, `cfin` | (none of its own) | `[cancel]`, `[cfin-*]` | D-CANCELTAB | L-SIGNAL, L-W | T-COMPAT | destructor; L-W |
| K-HOST, K-ALLOC | externs; `Alloc[T]` or the heap capability | K-HOST; K-ALLOC (R-ALLOCORACLE defers its lift) | host steps | D-COMODEL (host); `[TR]` 6.165 | L-STATE, L-RUN, L-TAIL | outside the proofs for externs; T-COMPAT (Rows G) for K-ALLOC | a host call; L-TAIL |
| K-GRADE | — | K-GRADE (R-EXACTQ) | — | D-SHARE's scaling | L-ALG | through K-LET | none (static) |
| K-NAME / K-REN | names | K-NAME, K-REN | — | — | L-REN, L-NAH, L-NU | T-REN | static masks (OQ-42); L-REN |
| K-SIG / K-ROW / K-INT / K-THEORY | declarations | 02 | — | D-OPTAB, T-SUMOK | L-SUM, L-HCORR | — | none (static) |
| K-SCOPE (not adopted) | `scope_{n,j}` | 03 §9.1 | as `[op]` | `opTable` entry with the scope | L-SCOPE | 03 §9.1 | as K-OP; L-HOP, L-SCOPE (scope handling OQ-59) |
| K-CARRIER (not adopted) | `hnd` at `C` | 03 §9.3 | as built | D-MODEL at `𝒞⟦C⟧` | H-laws at `C` | 03 §9.3 | dispatched call per resume at `S ⊸ F_Σ R`; L-HOP |
| K-BORANS (not adopted) | answer `Imm 'h T` | 03 §9.4 | none new | `Imm` at the site's lifetime | H-laws, L-HIDE | 03 §9.4 | as K-OP; L-HOP |
| K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ, K-SWAPΣ, K-SELFROW, K-GENNAME, K-NEGREC (not adopted) | 03 §9.6-§9.15 | 03 §9.6-§9.15 | each entry's *Step* | each entry's *Model clause* | each entry's *Laws* | each entry's *Obligation* | each entry's *Lowering* |

Every construct has every facet named. The facets with no statement anywhere today are the
model clauses D-MODEL, D-COMODEL, D-TABLEOK, D-EWPP and the laws of the K-HND, K-CAP and K-REN rows;
the facets boxed rather than written are listed in C-8's row.

---

## 9. Programs that exercise each construct

| construct | kernel program (`Core/`) | corpus program |
|---|---|---|
| K-RAISE, K-HND (abortive), L-SUM | `failOutside`, `logOutside` (`Core/EffPrograms.lean:277, 220`) | `effects-log-fail.bc`, `effects-fold.bc`, `effects-fold-sum.bc` |
| K-OP at `aff`, K-HND resuming | `nLogOutside`, `nFailOutside` (`:484, 487`); `prog`, `progC` (`Core/EffExamples.lean:35, 67`) | `capture-log-hand.bc` (its hand version) |
| K-BOR unwinding, L-BOR | `reborrowRaise` (`Core/EffPrograms.lean:345`), `logInBorrow` (`:578`) | `effects-borrow-raise.bc`, `core-effects-borrow-abort.bc`, `core-effects-reborrows.bc` |
| K-NU at a row (`Loop_Σ`) | `tickProg`, `tickAnsProg` (`:714, 995`) | `core-effects-loop.bc`, `capture-tick-hand.bc` |
| K-CANCEL, early exit | `takeProg` (`:787`); `prog`, `prog₃` (`Core/EffCancel.lean:56, 59`) | `capture-take-hand.bc` |
| K-KONT stored and cancelled | `storeCancel` (`Core/EffPrograms.lean:905`) | `capture-store-cancel-hand.bc` |
| K-CAP (answering) | — (elaborated only) | `effects-map.bc`, `effects-map-hand.bc`, `effects-map-fail.bc` |
| K-FIX | (`boundedFix_compatX` covers it) | `rec-fib.bc`, `rec-tree.bc`, `rec-overflow.bc`, `rec-log.bc`, `rec-yield.bc`, `rec-emit.bc`, `rec-layer.bc` |
| schema C2 | — | `clause-captures.bc` |
| K-NU, effectful `Aff` | `Core/AffPrograms.lean` | `aff-*.bc` |
| K-OP crossing a borrow (tier 2) | — (R-T1); GhostEnd's spanning programs are the candidates (§3.5) | — |
| SPEC §19's secondary programs: two blocks sharing a handler, `memo`, `choose`, resume-later (`SPEC.md:2810-2815`) | at the paper level: `progP_eval`, `memoPair_eval`, `twoShot_eval`, `laterProg_eval` (`experiments/HandlersControl/HandlersControl/Behind.lean:204`, `Reentry.lean:277`, `Capture.lean:232, 336`) | — |
| the reconciler chain (U5) | specified below (§9.1), not built | none |
| asynchrony (L-ASYNC) | specified below (§9.2), not built | none |

### 9.1 The reconciler chain `timeout |> retry |> log |> kube` (U5)

A derivation sketch in kernel terms, with fallible Kubernetes calls, since `retry` exists to handle
their failures. It is not built; each line names the rule that types it. Two forms of `kube` are
written: the form at the defaults, and the intended form once OQ-20 (c) and OQ-1 (b) are settled.

```
Signatures
  Log      = { log : Str ↠^{lin} 1 }
  Fail[E]  = { raise : E ↠^{aff} 0 }                         E ∋ Timeout, KubeErr e
  Clock    = { now : 1 ↠^{lin} I64 }                         (a host effect, K-HOST)

kube at the defaults (R-PURESWAP, OQ-20 (a)): a handled control effect, because a capability
cannot fail (its callee is pure, and an abortive operation has no co-operation)
  Kube     = { get : Key ↠^{aff} Obj,  put : Obj ↠^{aff} 1 }
  kubeHost : the host's outermost handler of Kube (K-HOST): its clause for get is
     λ(k, κ). hostGet k to r. case r { inj₁ o ↦ resume κ o ; inj₂ e ↦ cancel κ ; raise_{n_f} (KubeErr e) }
  The qualifier is aff because a failing call abandons κ; the pass's context across a Kube call
  therefore drops or is finalised (K-LET's graded side condition; an owned State gets a [then]
  finaliser, abortive-only under R-FINAB, which suffices since it performs nothing).

kube in its intended form (OQ-20 (c), OQ-1 (b)): a capability whose co-operations fail
  c_get : U(Conn ⊗ Key ⊸ F_{n_f:Fail[E]}(Conn ⊗ Obj))        withswap[Σ] at Σ = n_f:Fail[E] (03 §9.11)
  a failure raises out of the co-operation with the connection restored by the restore value r

One reconcile pass, an ordinary effectful function (K-FTY):
  defaults:  pass : !U(State ⊸ F_{n_c:Clock ⊕ n_l:Log ⊕ n_k:Kube ⊕ n_f:Fail[E]} State)
  intended:  pass : !U(State ⊗ Cap_l(Kube, Conn) ⊸ F_{n_c:Clock ⊕ n_l:Log ⊕ n_f:Fail[E]}(State ⊗ Cap_l(Kube, Conn)))

The generic combinators, functions over computations, one separately checked copy per row Σ
(R-NOROWVAR; T-REN relates only copies that differ by a renaming of names, OQ-13):
  timeout_Σ : !U(I64 ⊗ U(F_{n_c:Clock ⊕ n_f:Fail[E] ⊕ Σ} A) ⊸ F_{n_c:Clock ⊕ n_f:Fail[E] ⊕ Σ} A)
     reads now before and after, raises Timeout ∈ E past the bound; a K-LET chain, no handler
  retry_Σ   : !U(I32 ⊗ U(1 ⊸ F_{n_f:Fail[E] ⊕ Σ} A) ⊸ F_{n_f:Fail[E] ⊕ Σ} A)
     bounded_fix (K-FIX) over the attempt count; each attempt is `hnd_{n_f}` (K-HND) of the
     thunk, whose raise clause retries on KubeErr while the budget lasts and re-raises at the end
  log_Σ     : !U(U(F_{n_l:Log ⊕ Σ} A) ⊸ F_{Σ} A)   a handler of Log into a host output capability

The reconcile loop, a div computation read as codata (K-DIV, OQ-15 (a)):
  reconciler : !U(State ⊸ U(Loop_{n_c:Clock ⊕ n_k:Kube ⊕ n_f:Fail[E]} 0 State))          (defaults)
  reconciler ≜ unfold (λs. ⟨ next  ↦ log_Σ (retry_Σ' (3, λ_. timeout_Σ'' (d, thunk (pass s))))
                                        to s'. return (inj₂ s'),
                             close ↦ return s ⟩)

A timeout over the whole loop (K-HDIV's spanning form, 03 §9.2):
  deadline : !U(I64 ⊗ U(Loop_{n_c:Clock ⊕ Σ} 0 State) ⊸ U(Loop_{n_c:Clock ⊕ n_f:Fail[E] ⊕ Σ} 0 State))
  deadline ≜ hndLoopS with S = I64 (the absolute deadline), each observation reading now and
             raising Timeout past it; a retry that restarts the loop keeps the generator !U(State ⊸ …)
             and its seed in S

main (host): drive (kubeHost (deadline (T, reconciler s₀)))                        (defaults)
main (host): with_Kube(conn₀, cl) { c. drive (deadline (T, reconciler (s₀, c))) }  (intended)
```

Each observation `next` runs one pass with `timeout`, `retry` and `log` handling that pass; a
Kubernetes failure is a `raise` of `KubeErr` that `retry` handles, the `Fail` that escapes `retry`
and the `Clock` operations are handled by the host per observation. The run: each observation is a
total run of the machine (04), the `Fail` row handled by `retry`'s `[unwind]` steps, the `Log` row
by `log`'s `[op]` and tail resume (L-TAIL, a direct call in the lowering), `kube` by the host
handler's clause (defaults) or by a capability call (intended).

**What restricts U5 here, by default.** R-HDIV (OQ-67): `deadline`, and a retry that restarts
the loop, are K-HDIV's spanning form, specified, whose lift waits on OQ-67's proof. R-NOROWVAR
(OQ-13): `timeout_Σ`, `retry_Σ`, `log_Σ` are separately checked copies per row, related by no
theorem except a renaming; none can be stored as one row-generic value. R-PURESWAP (OQ-20): a
fallible `kube` cannot be a capability, so at the defaults it is a handled control effect, `Kube`
appears in `pass`'s row and in the loop's, and every function that calls Kubernetes is coloured by
it (OQ-1, U7). Dependence on other open questions: OQ-15 (the reading of the loop), OQ-1 (Kube as a
capability or a handled effect), OQ-19 (a fallible co-operation is runner-like), OQ-30 (Clock and
output as host capabilities).

### 9.2 Asynchrony (L-ASYNC)

A derivation sketch at OQ-60's default (b), the scheduler over codata. Its signature names its own
row in `spawn`'s parameter, which K-SIG excludes; it is written first with K-SELFROW's binder (03
§9.12, OQ-61 (b), not adopted), then at the default R-NOSELFROW.

```
Intended (OQ-61 (b)):
  Async[Σ] = μe. { suspend : 1 ↠^{aff} 1, spawn : U(F_{n_a:e ⊕ Σ} 1) ↠^{lin} 1 }
At R-NOSELFROW (the default):
  Async_Σ  = { suspend : 1 ↠^{aff} 1, spawn : U(F_Σ 1) ↠^{lin} 1 }      n_a ∉ names(Σ)
    a spawned thread runs at the outer row Σ and cannot itself spawn through n_a

asThread_Σ : !U(U(F_{n_a:Async ⊕ Σ} 1) ⊸ U(Loop_Σ' 1 1))      (03 §9.2: hndLoop of n_a)
   each observation runs the thread to its next suspend (answer inj₂ rest) or its end (inj₁ ());
   a spawn is answered by pushing asThread_Σ t onto the queue the observation returns

scheduler_Σ : !U(Queue(U(Loop_Σ' 1 1)) ⊸ F_Σ' 1)
   bounded_fix (or a Loop over the queue): pop a thread, observe it once, push the rest back
```

The queue holds `U(Loop_Σ' 1 1)` values, positive codata, so no negative recursion arises
(R-NONEGREC; OQ-60). A parked thread's lends are those of a stored `Loop_Σ` (OQ-28, OQ-46); an
asynchronous read into a local buffer needs R-T1 and R-CLOSEDOP lifted (OQ-2, OQ-56). A scheduler
that performs an outer affine or abortive operation (an I/O await, a raise) while threads are
parked must finalise the queue, closing each thread at its row: a finaliser at a resuming table,
excluded by R-FINAB (OQ-7), with the forwarding of the cancel to each thread OQ-27's term (06
L-ASYNC, *Finalising the queue*). So at the defaults the asynchronous program is restricted by
R-NOSELFROW and R-FINAB as well as by R-T1 and R-CLOSEDOP. Its obligation is **unknown** until
OQ-61 and OQ-7 are settled. Not built.

---

## 10. Open questions

### 10.1 Carried

This section carries **OQ-5** (EffModelRel's standing: §3.2 uses its default (a)), **OQ-6**
(role declarations: §5.2), **OQ-23** (lowering correctness: §1, T-LOWER; §6), **OQ-32** (the TR's
rule fixes). For OQ-32, its default (a) asks for a table, per fix, of the kernel rule that refuses
the TR's counterexample. From `docs/effects-tr/10-findings.md`:

| TR fix | counterexample | kernel rule that refuses it [read] | checked against a configuration? |
|---|---|---|---|
| §10.1 the owning lend | `movedLend` (a place consumed through a thunk captured before the lend) | the borrow constants consume their source and answer it back (`withbor1`/`2`/`3`, `Core/Fundamental.lean:239-250`), and contexts split linearly (`Ctx.SplitP`) | no |
| §10.2 `Res` as an instance | `resEscape` (a continuation carries a frame-owned resource past its frame) | R-T1: only abortive operations cross a borrow (`Row.Unwind`, `Core/EffBorrow.lean:133`); an owned resource in `κ` is `κ`'s and is finalised by cancel. Under OQ-2 (b) this returns as OQ-28 | no |
| §10.3 scaled capture | `retTwice` (a return clause run twice) | clauses are `!` (`retTy`, `clauseTy`, `Core/EffRules.lean:994, 984`), so the return clause captures nothing linear | no |
| §10.4 ν/op restricted | `nu_op_fails_multishot` | L-NU at `lin`/`aff` (OQ-16) | in the sibling calculus (`experiments/EffModelRel/EffModelRel/Examples.lean:223`) |

Each row still needs its configuration: the TR's term written in `CDerives` and shown underivable,
or derivable and safe.

### 10.2 Raised here

Boxed in [99](99-open-questions.md): **OQ-53** (is the elaborator proved, or each program
checked), **OQ-54** (the lend stack `σ` under a fork, recorded so that D-W's statement does not
exclude a forest), **OQ-55** (the declaration kind at the surface: on the declaration, or on the
handler). Carried and cited here: OQ-13, OQ-20, OQ-61, OQ-67 (the reconciler chain and the
asynchronous program, §9), OQ-60 (the asynchronous program's scheduler, §9.2), OQ-42 (lowering
gaps, §6), OQ-58 (T-CONS.2 and T-CONS.3: whether Core is the `σ = []` instance at `U`).

---

## 11. Unspent and untranscribed (CLAUDE.md §5)

**Printed lemmas in the run-up that are not transcribed** (at the tables this section's
correspondences rely on):

- `[TR]` 6.150 at a resuming table, with its И freshness: needed for `withloadU`'s abbreviation
  (T-CONS.1) and for E-BOR;
- `[TR]` 6.64 at an `Imm` table beyond `ewpTS_I_frameR`;
- `[TR]` 6.65's `↭` steps line by line (audit's O2);
- T14.4 and T14.6 (`docs/effects-tr` §15), not written in `Core/Gen.lean` (branch
  `lift-stage1`).

**Printed hypotheses not spent here.** This section proves nothing; it spends no hypothesis. The
correspondence rows that would spend one are T-CONS.1's `withloadU` row (6.150's freshness) and
T-ELAB's C2 row (no printed statement covers a state-passing carrier).

**Uniqueness and functionality results not used.** `head_det_eff` (`Core/Steps.lean:596`) and
`freshRun_det` (`experiments/TwoRun/TwoRun/Fresh.lean:255`) are cited for T-DET and T-2RUN and
for the threads item (§7 item 5), not used in any argument here. `handle_unique`
(`experiments/CoeffectsStrict/CoeffectsStrict/Handler.lean:59`) and `fold_unique` (`…/Fold.lean:207`)
are the uniqueness results L-HUNIQ would use; unused here.

**Obstructions.** None is claimed. Every "not built" above means not built; I have not derived
any of the missing results and have not verified that any obstruction is real.
