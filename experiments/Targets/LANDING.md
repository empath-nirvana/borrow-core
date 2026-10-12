# Tier 1: the landing inventory

This is a list for review. Nothing in it has been ported. "Landing" means landing the research
and experiments in **Core**: Core theorems, SPEC rules, the checker and elaborator, the backend's
lowering, and running kernel and corpus programs. It does not mean merging `experiments/` onto
`main`.

The source is `tier1-effects` at `f172a63`. Every claim cites a file and line, or a theorem name.
`Status` means `experiments/Targets/Targets/Status.lean`, and `PLAN` means
`experiments/Targets/TIER1-PLAN.md`. Paths without a prefix are relative to the repository root;
Targets files are relative to `experiments/Targets/Targets/`.

The user's decisions of 2026-10-12 are applied throughout:
- The backend's refusal of a suspending finaliser is **unimplemented**, not a typing rule.
- `Row.UnrD` and `PendPers` are accepted.
- E5 and E9 at an `unr` `exn` signature are **restricted out** (decision 63).
- E7c's restatement is accepted.
- `CancelsNZ` and `CancelsNoCtl` are kept as records.
- `prog` stays as Lean and interpreter runs.
- Tier 2 is shelved, and multi-shot is ignored.

Classes used below:
- **(K)**: already changed in Core on `tier1-effects`; it lands with the branch's non-experiment diff.
- **(T)**: becomes a Core theorem, with its restated statement and target file.
- **(P)**: becomes a kernel or corpus program.
- **(S)**: scaffolding that stays in `experiments/`.

---

## 0. What is already in Core on `tier1-effects` (K)

Since the merge base `7655bc0`, the branch changes 46 files outside `experiments/`, with about
+5,100 and −1,300 lines (`git diff --stat 7655bc0 HEAD -- Core Paper Support Frontend Backend
corpus SPEC.md scripts`). None of it is on `main`. Before anything in §1 is ported, this diff
lands as one unit (U0, §6).

| change | where | SPEC |
|---|---|---|
| polymorphic let `CDerives.letPoly`, `letPoly_compatC` | `Core/Fundamental.lean:414`, `Core/PolyLet.lean:69` | §24, 0.41 |
| handler value form `CDerives.effHandleV`, `handleV_compatC`; the old rule becomes the theorem `CDerives.effHandle` | `Core/Fundamental.lean:405`, `Core/EffFin.lean:1142` | §24 |
| capture cell: `hndVal` tags, `capTag`, `kappaC`/`kappaCell`/`kappaAt`; `ewp_kappaCell`, `ewp_kappaC_resume`, `ewp_kappaC_cancel` | `Paper/S3_Dynamics/Definitions.lean:365,470,492,497`; `Core/EffRules.lean:536ff` | §25, 0.42 |
| `[λ-dead]` `CDerives.lamDead`, `lamDead_compatC` | `Core/Fundamental.lean:111,72` | §26, 0.43 |
| frame deadness: `Kont.DeadFrame`, `Kont.dead`, `[cfin-cancel]` (`Head.cfcancel`), first error wins; `dead_comp`, `hasHnd_dead`, `catches_dead`; the abortive-row `[then]` refuted (`not_thenAbort_compatC`) | `Paper/S3_Dynamics/Definitions.lean:418,426,596`; `Core/EffCancel.lean` | §19, 0.44 |
| cancel rows (§27): `OpSig.fin`, `CTy.eff … fin …`, `FinLe`, `ThenLe`, `PendLe`; `[then]` = `CDerives.effThen` with `Row.UnrD` and `Row.PendPers` (**accepted 2026-10-12**); `effThenA` derived; `then_compatC`, `cancel_frame_drop`, `cfin_cancel`, … | `Core/Fundamental.lean:392`, `Core/EffRules.lean:868`, `Core/EffFin.lean:407,968` | §27, 0.45 |
| typed cancel programs `progT` … `progNCrecT` (derivations and runs) | `Core/EffCancelTyped.lean` (896 lines) | §27 *Programs* |
| interpreter follows the machine (cell, deadness, `[cfin-cancel]`) | `Support/Dynamics/Interpreter.lean:169–212` | §19, §25 |
| backend: cancel mask removed (first error kept); `Capture` refuses a suspending finaliser | `Backend/Clos/Capture.lean:1006–1015` | §27 *Lowering* |
| checker: `CTy.eff` gains `fin`; `Row.unrDB`; finaliser at `effOf [] .unit`; empty cancel rows | `Frontend/Check/Decide.lean:812`, `Frontend/Check/Checker.lean:279,521`, `Frontend/Check/Elab.lean:388` | §27 *Baseline* |
| kernel programs: `cancel-suppressed` (`prog`) removed; `cancel-reentered`, `cancel-propagated` added, `inr ()` at `0 0 0` | `Backend/Kernel.lean:156–161`, `corpus/kernel-counts.expected:15–16` | 0.44 |

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD` and `adequacyD_obs` keep their
statements (`Core/Fundamental.lean:508,668`, `Core/Demonic.lean:284,312`,
`Core/EffPrograms.lean:41`). The full `make gate` passed at `3cdeb3c` (PLAN:2788–2790).

Not in Core:
- **Decision R's tie** (`CDerivesAt Ξ`) lives only in `Instance/TiedKernel.lean` (PLAN:2276).
- **The row `∀`** lives only in Targets' open types (SPEC §24 *Open*).

U4 decides the tie (§1.3, §4).

---

## 1. Theorem table

Status words are Status's own: PROVED, PROVED AT σ=[], OPEN, RESTATED.

Names in the "restated over Core" column and in §5 that no Targets file defines (`effSafe_closed`,
`catch_cell`, `kappaC_resume`, `unwind_prefix`, `cancel_prefix`, `alg_seq`, `abort_absorbs`,
`tail_quiet`, `no_dropped_nkc`, `CDerivesAt` in `Core/Tied.lean`, …) are **proposed** names for
the ported statements, and so are the target files.

Throughout §1, "a typed program" means `CDerives LifeCtx.empty [] e (.comp (.ret A))` with `A`
data (`VTy.Data`, `Base/Machine.lean`), or persistent where Core's `adequacyD_obs` already reads
that. Runs are Core's `Steps`/`Step1`/`Head` (`Paper/S3_Dynamics/Definitions.lean:502ff`). No
`EffectSystem`, no `ourInst`, no `J₁`.

### 1.1 Soundness properties S0–S6

| result (Targets) | status | class | restated over Core | target |
|---|---|---|---|---|
| **S0** `MachShape` (`AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`): `machShape_orow`, given `LiveOK` | PROVED AT σ=[] (Status:789) | **S**; the Core content exists | Each law is a `Head` rule or unique decomposition already in Core (`head_plug`, `head_det_eff`, SPEC §19 :2484–2494). `LiveOK` is `adequacyD_safe` (`Core/Demonic.lean:325`) plus closedness (T row below). Nothing new to state. | — |
| closed runs stay closed: `closedAt_of_derives`, `closed_steps` | PROVED (`Base/Closed.lean:47`, `Base/Runs.lean`) | **T** | `CDerives Δ Γ e j → closedAt Γ.length e`; and `Steps μ e μ' e'` from a closed `e` with closed stored values keeps both closed | `Core/Closed.lean` |
| run splitting through contexts `steps_plug_split`, `step1_plug_of_step`, `plug_inj_ctx` | PROVED (`Base/Runs.lean:40`) | **T** | as stated, over `Kont.plug` and `Steps` | `Core/Steps.lean` (extend) |
| **let law** `LetLaw` (`letLaw_ourInst_J₁`, `Instance/J1.lean:578`) | PROVED | **S** | `[let-poly]` *is* the law: `CDerives.letPoly` types `let x = λy.b in N` from `N[λy.b/x]`. Nothing to add. | — |
| **S1** `RowAlgebra` (`rowAlgebra_ourInst_tier1Open`, `Instance/J1Checks.lean:377`; `rowNU_of_wf`) | PROVED, RESTATED (D6) | **T** (small) | `RowLe` is a preorder whose cancel rows only grow (`FinLe`); `[sub]` at a well-formed target row; a well-formed row at an admissible context is unr-free | `Core/Rows.lean` (new), cited by SPEC §19 *Types* |
| `DataDiv` (`dataDiv_ourInst`, `Instance/Safety.lean:44`) | PROVED | **S** | A-level vocabulary (div-free answers); Core has `Loop_Σ` (§19 *Divergence*) | — |
| **S2/S3** `Safety`, `EffSafe` (`safety_ourInst_tier1Open`, `effSafe_ourInst_tier1Open`, `I/Restricted/InstanceSafety.lean:864–868`) | PROVED AT σ=[] (D1 tie) | **T** (closed form) | `effSafe_closed`: for a typed program and `Steps ∅ e μ e'`, `e'` is a value or steps, and is never `K[perform …]` or `K[raise …]` with `K` free of the name. This is a corollary of `adequacyD_safe`. The runner form (a platform answering the program's top row, `PStep`) waits for a Core platform notion (`Base/Machine.lean`, DESIGN D5–D9). | `Core/EffSafety.lean` |
| **`LiveOK`** (`liveOK_tier1Open`) | PROVED | **T** | the closed form above plus closedness | `Core/EffSafety.lean` |
| **leak freedom / T-leak** (`leakFree_of_coreClosed`, `I/ContUseJ1.lean:426`; `I.leakFreeAt_J₁` :797) | PROVED | **T** | `adequacyD_val` generalised to persistent `A`: `Steps ∅ e μ (.val v) → μ = ∅`, continuations' cells included | `Core/EffPrograms.lean` (next to `adequacyD_obs`) |
| **S4** `HandlerSem`, RESTATED at the capture cell (F1): `handlerSem_ourInst` (`Instance/HandlerCell.lean:308`), `catch_unr_ourInst`, `catch_cell_ourInst`, `resumeCellLaw_ourInst`, `cancelCellLaw_ourInst`, `kappaC_resume_parts`, `kappaC_cancel_parts`; `retLaw_ourInst` … `finLaw_ourInst` | PROVED at every effect context (Status:246–259) | **T**: these are machine lemmas | `catch_unr`: `Head μ (hnd(n,qs,H)[K[perform(n,i,v)]]) μ e'` with `capTag qs i = unr` gives `e' = clause_i (v, kappa H K)`. `catch_cell`: at `lin`/`aff`, `μ' = μ[ℓ ↦ ()]` with `ℓ ∉ dom μ` and `e' = clause_i (v, kappaC ℓ H K)`. `kappaC_resume`: resuming `kappaC ℓ` at a store holding `ℓ` reaches, in three steps, the store without `ℓ` and `kappa`'s resume. `kappaC_cancel` is the same at `aff`; at `lin` the cancel branch has no step. Plus the return, forwarding, abort and finaliser laws as `Head` facts. | `Core/EffMachine.lean` (new); SPEC §19/§25 laws H-ret, H-op, H-fwd |
| S4 with no cell `HandlerSemNoCell`, `not_handlerSemNoCell_J₁_ΞA`, `handlerSemNoCell_orow` | kept record | **S** | — | — |
| **S5 unwind** `unwindOrder_J₁` (`I/S5J1.lean:138`), `unwind_pfx` (`Instance/CancelRuns.lean:377`) | PROVED, RESTATED prefix-closed (F3) | **T** | `unwind_prefix`: from `K[raise(n,p)]` with `K` typed-reached, every run is a prefix of the run that fires `K`'s finalisers innermost first (`[finalise]`, then the β-step, then the finaliser alone to `()`, then `(); raise p`) up to the frame catching `n`. A finaliser's own raise supersedes `p`. | `Core/EffCancelRuns.lean` (new) |
| **S5 no-interception** `noIntercept_J₁` (:144), `cancellation_J₁` (:149), `cancel_pfx` (`Instance/CancelRuns.lean:919`), under frame deadness (M3: `pend`, cell clause) | PROVED at `J₁` at every effect context | **T** (needs U4's tie) | `cancel_prefix`: for a typed (tied) program, every run from a cancel of `kappa H K`, or of `kappaC ℓ H K` (after `ℓ`'s release), is a prefix of the trace that runs `K†`'s actions innermost first. Each action is a finaliser `fire D` alone to `()` or a raise, or a running finaliser's `cfin` frame passed by `[cfin-cancel]` (`pend`). The first kept error wins, and the canceller gets `()` or the kept error re-raised. Hypothesis: every fired finaliser is typed at a row whose raises have a live instance (§27). | `Core/EffCancelRuns.lean` |
| `CancelsNamed` run invariant (`cancelsNamed_J₁`, `I/CancelsNamed.lean:420`; `raiseOK_step1`, `Base/RaiseNames.lean:929`; `raiseOK_reach`) | PROVED at `J₁` | **T** | `Expr.RaiseOK P` is preserved by `Step1` and by stored values (`HeapRaiseOK`). A tied typed program has `RaiseOK (names Ξ)`. | `Core/RaiseNames.lean` |
| `FinaliserOrder` (`finaliserOrder_at`, `Base/CoreCancel.lean:1790`), `CancelRun`, `UnwindRun` | PROVED given `FinAloneAt` | **T** (with S5) | as stated; already worded over Core's machine with no world | `Core/EffCancelRuns.lean` |
| finalisers typed per `FinRow` run to `()` (`finOK_of_finRow`, `I/S5J1.lean:86`) | PROVED | **T** | a closed `CDerives … D (F_Σ 1)` whose `Σ` is empty at the effect context runs to `()` from every finite memory | `Core/EffCancelRuns.lean` |
| S5 read whole (`CancellationWhole`, `not_cancellationWhole_J₁`, `fireProg`) | kept record | **S** | — | — |
| `CancelsNZ` (`cancelsNZ_J₁`, `I/CancelsNZ.lean:338`), `CancelsNoCtl` (`not_cancelsNoCtl_J₁`, `Instance/DropWitness.lean:815`) | proved / refuted; read by nothing | **S**: **kept as records** (decision 2026-10-12) | — | — |
| **S6** `ContUseEv` | OPEN; at `J₁` REDUCED (`contUseEv_J₁_of`, `I/ContUseJ1.lean:803`) to `OnlyOwnerFrees` (:514) and `NoDanglingUse` (:533) | **T** for the reduction lemmas, **open** for S6 | `catchEv_cell` (:278): a capture event allocates `κ`'s cell. `use_frees_cell` (:169): a use releases it three steps later. Both are machine lemmas for `Core/EffMachine.lean`. S6 itself: on a complete run of a typed program, each `kappaC ℓ` handed at a catch is applied once (linear), or applied or cancelled once (affine). It lands when both ownership properties are proved (§4). | `Core/EffMachine.lean`; S6 later in `Core/ContUse.lean` |
| S6 teeth (R1): `not_contUseEv_of_der_R1`, `teeth_JR_ΞA`, `I.not_semC_R1` (`I/GhostCoupling.lean:97`) | PROVED | **T** (the Core half) | `not_semC_R1`: R1 at a linear or affine operation is not in `cC` at `F bool` (its run leaks `κ`'s cell). The A-level tooth stays S. | `Core/EffCancelTyped.lean` or `Core/ContUse.lean` |
| today's kernel refuses R1–R4 clauses (`refuses_R_clauses`, `Instance/ClauseRefusals.lean:779`) | PROVED | **T** | inversion facts over `CDerives` (a `kTy` slot at `lin`/`aff` is neither dropped nor duplicated) | `Core/Inversions.lean` (U7a) |

### 1.2 Laws, algebraicity, answering class

| result | status | class | restated over Core | target |
|---|---|---|---|---|
| **algebraicity** `AlgLaw` (F2: a finaliser's start observed, not its code): `I.algLaw_J₁_of` (`I/AlgJ1.lean:230`), `algLaw_of_good` (`Instance/AlgSim.lean:1947`), `AlgRel.head` (:1002), `AlgRelH` (:99) | PROVED at `J₁` **given `KeptLamFree`**, which fails at the admissible `ΞT` (`not_keptLamFree_ΞT`, `Instance/KeptLamWitness.lean:201`) | **T (conditional)** | `alg_seq`: for a typed program reaching `K[(x←M) to y.N]` and `K[x←M; y.(M' to …)]` … stated as `AlgRel`. Related configurations step alike under every `Head` rule, memories related cell by cell (`AlgRelH`, so a κ stored in a cell is covered). Complete runs reach the same data answer and the same platform events, with finaliser starts read as `fire ()`. Hypothesis `KeptLamFree` named and scoped. | `Core/AlgSim.lean` (new) |
| `AlgLawCode` and its refutation `not_algLawCode_J₁` (`algAffProg`) | kept record | **S** | — | — |
| the tail law and algebraicity at the answering class (`calm_tailClause` `Instance/UnaryLaws.lean:815`, `tailLaw_quiet` :867, `algLaw_quiet` :916; `Calm`, `runsAlike_of_calm`, `finDom_reach`) | PROVED at every operation, around a cell | **T** | `tail_quiet`: a clause `λ(a,k). c a to b. k.resume b` whose `c` runs quietly gives a run that, read without the cell's allocation and release, is the call `c a` (same answer, same memory) | `Core/Answering.lean` (with `Core/Handlers.lean`'s `op_tail`) |
| `TailLaw` (general), `EtaHold`/`EtaLin` | OPEN | open | — | — (§2: OA5) |
| comodel reduction `ansCorrect_of_comodel` (`Instance/Theories.lean:858`), `state_correct` (:1131), `not_ansCorrect_badState` | PROVED | **S until OA2** | it reads A's `Theory`/`Eqn`/`AnsCorrect`. Whether answering effects are a sub-theory or comodels is OA2, still undecided (effects-algebra.md:105). After OA2: a Core statement over `ansHnd` at `RunsAlike`. | later: `Core/Answering.lean` |
| `NoDroppedError` on the runs that capture no kept error (`I.noDroppedErrorNKC_J₁`, `I/NoDropped.lean:321`; `kc_head`, `Base/KeptCount.lean:1042`) | PROVED AT σ=[] (restricted) | **T (restricted)** | `no_dropped_nkc`: on a complete run of a typed (tied) program on which no `[op]` step captures a context holding a kept error, #`[cfin-raise]`-at-empty-cancel = #`[cancel-raise]` + #`[cfin-cancel]`-at-two-errors | `Core/KeptCount.lean` |
| `not_noDroppedError_unr` (`Instance/DropWitness.lean:610`) | PROVED (the restriction is needed, at `Ξu`) | **T** (record of the tolerated exception) | `progDropT`'s complete run keeps one error and re-raises none | `Core/EffCancelTyped.lean` (next to `progDropT`) |
| `CfinQuiet`, `not_cfinQuiet_J₁` | retired hypothesis, kept as a record | **S** | — | — |

### 1.3 Typing facts (§24–§27), Accepts, Rejects, AT08

| result | status | class | restated over Core | target |
|---|---|---|---|---|
| decision R's tie `CDerivesAt Ξ`, `toCDerives`, `sig_prefix_of_rowAt`, `hndTags_of_rowAt` (`Instance/TiedKernel.lean`) | built | **T: decide first** (U4) | `CDerivesAt Ξ` is `CDerives` with `RowAt Ξ` at `[perform]`, `[raise]` and `[handle]`; `toCDerives`. Every derivation the checker emits is tied to the program's effect declarations (a checker theorem, §4). S5's no-interception, `CancelsNamed` and `NoDroppedError` read it. | `Core/Tied.lean`; `Frontend/Check` lemma |
| **§27 rejections** `not_der_progT` (`I/RejectsFin.lean:585`), `not_der_progNCrecT` (:782) | PROVED | **T** | `¬ CDerives Δ Γ progT (F_Σ A)` for every `Σ` without `2`; `¬ CDerives Δ Γ progNCrecT j` for every `j` | `Core/EffCancelTyped.lean` (next to `d_progT`) |
| **E7c rejection** `not_der_e7c_J₁` (`Instance/E7.lean:707`), `der_e7c_lift_J₁` | PROVED; **restatement accepted** | **T** | `¬ CDerives … e7c (F_Σ A)` at every `Σ` without `exnᵢ`; typed at that label's row | `Core/EffCancelTyped.lean` |
| **Rejects** AT05/06/08/13 (`not_der_at05` `I/Rejects.lean:2397`, `at06` :1931, `at08` :2002, `at13` :1868), the inversion library (14 inductions, `fv_live`, `der_swap`) | PROVED AT σ=[] | **T** | `¬ CDerives Δ Γ atXX j` for every `Δ Γ j`. AT08 (M5) is refused by the continuation rule. `fv_live`: every free variable of a typed term has a live slot. | `Core/Inversions.lean` + `Core/Rejections.lean` |
| AT08's control `d_at08Once` (:2081), `at08Once_runs` (:2090) | PROVED | **P** | kernel program `at08-once`, answer `()`, counts to be measured (expected `1 0 0`: one cell for `κ`; label: estimate) | `Backend/Kernel.lean`, `Core/EffCancelTyped.lean` |
| AT08 at the interpreter (`at08_eval`), AT07 (`at07_eval`) | evidence | **S** | — | — |
| **Accepts** `I.accepts_J₁`, `compositeT1_tier1`, `acceptedT1_*` (`I/Restricted/CompositeT1.lean:45–77`), `run_*` (`I/AcceptsRejects.lean:71–88`) | PROVED AT σ=[] | **P, already landed** | The programs are Core's (`Core/EffPrograms.lean`, SPEC §19 :2861–2881). Most are kernel programs with counts (`corpus/kernel-counts.expected:1–11`: `log-outside 1 0 0` … `store-cancel 2 0 0`), so nothing new is needed. | — |
| the computed runner `runM`, `runM_sound` (`Base/LookMem.lean:246`), `look`, `look_sound` (`Base/Look.lean:459`) | PROVED | **T (tool)** | `runM n μs e = (μs', v) → Steps (LMem.heap μs) e (LMem.heap μs') (.val v)`. This proves a kernel program's answer by `rfl`. | `Core/Run.lean` |
| `[λ-dead]` callbacks `d_cbDead` | PROVED | **(K)** | the rule is in Core; the derivation is a program fact (E1) | — |
| `not_der_letTwo` (`Instance/Inversion.lean:475`), `not_der_callBang`, `not_der_handle_tier1Open` | PROVED (about the unr-free fragment without §24) | **S** | about `tier1Open`, which Core no longer is | — |
| `I.not_tier1_of_elabClosed` (the elaboration route does not reach tier 1) | PROVED | **S** | — | — |

### 1.4 The (E) properties as programs (P)

Each is a typed Core term with a computed run (`runsTo_*` through Targets' runners). It lands as:
- a **kernel program**: a Core term with its `CDerives` derivation in a Core file, its answer
  proved by `runM`/`rfl`, and its counts in `corpus/kernel-counts.expected`; and later
- a **corpus program**, once §4's surface items exist.

Counts below are **estimates** to be measured. The capture cell is zero-size, and the backend
builds `κ` itself (SPEC §25 *Lowering*), so cells add no allocations.

| E | Targets result | status | kernel program (name, answer, est. counts) | surface needs |
|---|---|---|---|---|
| E1 no colouring | `noColouring_J₁` (`Instance/EProps.lean:48`), `runsTo_noColour`, `runsTo_noColourS` (`Instance/E1Runs.lean:167,194`) | PROVED | `hof-two-rows`: `hof` typed once and used at `exn`'s row and at `wait`'s row (the latter around the cell); answer as in E1Runs; `0 0 0` | letPoly at surface, `[λ-dead]` |
| E2d `sumGen` | `e2d_J₁` (`Instance/E2.lean:582`), `runsTo_prog2d` (:567) | PROVED where no op is `unr` | `sum-gen`, answer from `runsTo_prog2d`; `0 0 0` | letPoly |
| E2a–c `twice`, `compose`, `retryP` | NOT DERIVED | open | — | the `!U C` force rule (§4) |
| E3 loops | NOT DERIVED | open | — | `unfold`'s value (§4) |
| E4 deep handlers | `deepHandler_J₁` (`Instance/E4.lean:394`) | PROVED | `deep-gen`: answer `()`, two ticks, `κ` resumed at its cell; `0 0 0` | — (existing `capture-*` syntax) |
| E5 nested handlers | `nestedHandlers_J₁` (`Instance/E5.lean:442`) | PROVED where no `exn` is `unr`; **the rest restricted out** (decision 2026-10-12) | `nested-both-orders` (two programs: `toResult ∘ withLog` and `withLog ∘ toResult`) | handler values (functions taking computations) |
| E6 no accidental handling | `tunnel_J₁` (`Instance/E6.lean:291`), `runsTo_tunnel` (:255) | PROVED | `tunnel`: `fwrap` once, `exnₒ` passes `exnᵢ`'s handler | letPoly |
| E7a/b/d abandoning a suspension | `cancelPolicy_J₁` (`Instance/E7.lean:1154`), `runsTo_e7a/b/d` (:931,1038,1118) | PROVED | `e7a`, `e7b`, `e7d`: answer `inr ()` each, finalisers fire, first error kept and re-raised; `0 0 0` (each raises; the backend lowers raising finalisers) | finalisers with effects at surface (cancel rows) |
| E7c | rejection (§1.3) | RESTATED, accepted | negative corpus program (rejected at rows without `exnᵢ`) | cancel rows at surface |
| E8b unwinding through finalisers | `unwindPolicy_J₁` (`Instance/E8.lean:244`), `runsTo_e8b` | PROVED | `e8b`: answer `inl (inr ())`; `0 0 0` | as E7 |
| E9a/b/c stored continuation | `storedK_J₁` (`Instance/E9.lean:550`) | PROVED where no `exn` is `unr`; rest restricted out | `stored-k-resume` (two cells allocated and freed), `stored-k-cancel`, `stored-k-fin` (finaliser raises `exnₒ` inside `toResult`); counts: closure plus `0` cells (est.) | handler values; storing `κ` in a closure |
| E10 reconciler | `derV_timeoutR_J₁` (`Instance/E10.lean:111`), `polyUseOpen_timeoutR_J₁` | `timeout` PROVED; `retry`, loop NOT DERIVED | `timeout` alone as a kernel program | `!U C` force, `unfold` |

The A-level schema lemmas (`PolyUse`, `CallsThrough`, `RowVarKernel`), the `EProps` record and
`not_*_of_monoCallback` stay **S**. The `monoCallback` refutations
(`status_not_noColouring_of_monoCallback`, …) are A-level: they show E1/E2/E6/E10 need row
polymorphism, and Core's answer to that is `letPoly`, which needs no theorem.

### 1.5 Borrow-side results proved in the tier-1 run

| result | status | class | note |
|---|---|---|---|
| B0–B4, B6, B7 at `J₁` (`status_guarantees_J₁`) | PROVED AT σ=[] | **S** | re-readings of Core's `fundamentalC`/`adequacy*`/Paper theorems; nothing new for Core |
| B2 drive conjunct at positive loop bodies (`adequateDriveAt_core`, `adequateDrive_needs_nuOk`) and `EffSafeDrive` (`effSafeDrive_of_FL`) | PROVED | **T (optional)** | `CTy.NuOk` is a Core predicate; "a driven program at a positive loop body finishes its drive or diverges safely" belongs in `Core/NuRel.lean` |
| B5 `releasedOnceReuse_of_soundContracts` (`B/BumpSim.lean:2028`), `bumpSimAt` (:1833) | PROVED | **T (optional, later)** | step-for-step simulation of a bump allocator, about 2,000 lines. It is the route to S6's `NoDanglingUse` (PLAN:1658–1664), so port it together with that unit. |
| P14.a `wbCore` (`B/BoLo.lean:117`) | PROVED | **T (tiny)** | R-T1 as a lemma about `wpG` (`Core/EffDefs.lean:40`); see §3 |
| P14.b `conservativeWB_core` (:127), `Conservative`, `ConservativeWB` | PROVED / stated | **S** | tier 2's world `W`; **tier 2 shelved** |
| `Bounds`, `Interface`, `Device`, `Pins`, `I4a`, `I.Combined`, `I.Tier1`, `Tier1Core`, `coreW`, `audit_W`, `FIX-RUN-END` checks (`I/RunEnd.lean`) | PROVED / stated | **S** | the interaction framework and its audit; done is about `J₂`/`W` (tier 2) |
| `I4Typing`, `I4Runs`, `AdequateOfLaws`, `FreezeBinder`, … | OPEN | **S** | — |

### 1.6 Pure scaffolding (S), and why

- **A** (`Targets/A/*`): `EffectSystem`, `EffAlg`, `SProps`/`EProps`, A₂ (`HandlerLaws`,
  `EffDepLaws`, `Abstraction`), A₃ (`Tgt`, `LoweringCorrect`, `ZeroCost`), `Theories`. These are
  instance-independent statements. Core lands their instances, not the abstraction (the brief says
  no abstract `EffectSystem`).
- **Instance** glue: `ourInst`, `orowAlg`/`orowRF`, `AdmEff`, the open types, `OurTyping`,
  `tier1Open`, `J₁`/`J1DerAt`, `RowAt` as the instance reads it, the runners
  (`Rtick`/`Rtl`/`Rrec`), `obsFrom_*` bridges, `KontLaws`/`ConfLaws`.
- **Records**: `HandlerSemNoCell`, `CancellationWhole`, `AlgLawCode`, `CfinQuiet`,
  `CancelsNZ`, `CancelsNoCtl`, `not_algFireProg_J₁`, `ContUse` (the earlier S6 reading),
  `Tier2Pinned`, `AcceptsTier2`.
- **Meta**: `Audit.lean` (pins of Core's relation for P14), `AxiomCheck.lean`, `Status.lean`.

---

## 2. Laws table (effects-algebra.md part 1)

Source: `~/repos/borrow-core-targets/research/effects/src/foundations/effects-algebra.md`, which
is marked "draft for review. Not decided." (:3).

The landing target for each law is one of:
- a Core theorem;
- a SPEC normative law that cites a theorem;
- open;
- drop by decision.

| law (line) | status there | landing target | missing |
|---|---|---|---|
| A1 sequencing (:48) | Model; Core `AlgLaw` "given `KeptKapFree`" | Core theorem `Core/AlgSim.lean` (§1.2), cited by SPEC §19 *Laws* | Core proves it given **`KeptLamFree`**, not `KeptKapFree`: the page names the weaker hypothesis that is not built (Status:292–311). Correct the page or build the confining simulation. It fails at `ΞT` (`not_keptLamFree_ΞT`). |
| A1 application/projection (:49) | Model only | open, then Core `Core/AlgSim.lean` | `AlgRel` relates `to`-frames only. Extend it with the application and projection frames. |
| A2 abort (:50) | Model only | Core theorem (small): `raise e to z.N` and `(raise e) w` step by `[unwind]` to `raise e`. `Core/EffMachine.lean` | statement only; the rule is `Head`'s |
| A3 abort through a finaliser (:51) | Model; Core via F1 | Core theorem `unwind_prefix` (§1.1) | — |
| H-ret, H-op, H-fwd, H-fwd abort (:57–60) | Core: S4 at the cell | Core theorems `catch_unr`, `catch_cell`, `kappaC_resume`, forwarding (§1.1, `Core/EffMachine.lean`), cited by SPEC §19/§25 | — |
| tail (:61) | OPEN | Core theorem at the answering class (`tail_quiet`, §1.2); the general law stays open | `TailLaw` against `fire D` |
| η (:62) | OPEN | **decide (OA5)**: owed or dropped | `EtaHold`: `[handle]`'s `hnS` keeps a forwarding handler's name out of its clauses' row (Status:799), so no typed program may install one, which is not checked by inversion |
| N1 no accidental handling (:68) | Core E6; `Tunnel` (T3) Missing | program `tunnel` (P) + SPEC §19 *Names* | the relational form `Tunnel` |
| N2 sum (:69) | Core S1 | Core theorem `Core/Rows.lean` | — |
| N3 tensor (:70), N4 absorption (:71) | Model only | **OA6**: Core statement or drop by decision | — |
| N5 ν laws (:72) | Model only | **OA3**: with static names, elaboration facts. Proposed: drop from the kernel by decision, recorded in SPEC §19 *Names*. | decision |
| F1 finally (:78) | Decided; `then_compatC` | SPEC §19 normative, cites `then_compatC` + `unwind_prefix` | — |
| F2 cancel not interceptable (:79) | Decided; S5 | SPEC §19 normative, cites `cancel_prefix` | — |
| F3 frame deadness (:80) | Decided; machine | SPEC §19 normative (definition `Kont.dead`), cites `hasHnd_dead`, `catches_dead` (K) | — |
| F4 order (:81) | S5 unwind | cites `unwind_prefix`, `finaliserOrder_at` | — |
| F5 errors (:82) | Decided; §27, M3 | SPEC §27 normative, cites `not_der_progT`, `no_dropped_nkc` | `NoDroppedError` for runs that capture a kept error (needs S6) |
| L1 use (:88) | S6 OPEN | Core theorem `Core/ContUse.lean` after `OnlyOwnerFrees`/`NoDanglingUse` | the two ownership properties |
| L2 no forget (:89) | Decided §19 | SPEC §19 normative, cites `kTy` (linear cancel at `⊤`) and `refuses_R_clauses` | — |
| L3 independence (:90) | Model only | **OA6**; its kernel form is `[let]`'s `unr ⇒ !Γ₂` premise (SPEC §19 :2586–2672, `let_compatC`), so a SPEC law citing `let_compatC` is available | the general statement |
| T-safety (:96) | Core S2/S3 | `effSafe_closed` (§1.1) | — |
| T-handler (:97) | **Missing** (OA1) | open, see below | free model |
| T-leak (:98) | Core | leak freedom (§1.1) | — |
| T-colour (:99) | Core E1 | program `hof-two-rows` + `[let-poly]` | — |

**OA1, the free model and handlers as homomorphisms.** The proposed home is a new
`Core/EffAlgebra.lean`, with a SPEC §19 *Laws* subsection. It would hold:
1. The free model over a signature: Core's computations at `F_Σ A`, modulo A1–A3 and F1, read at
   a Core observation. Use `RunsAlike` at data answers, or `Base/Ctx.lean`'s `≼` moved to Core.
2. **T-handler**: `handle – with H` is the homomorphism from it determined by H-ret and H-op.

This needs a binary observation in Core first; none exists in Core today (`Base/Ctx.lean` is
Targets-side and "outside the first pass"). It is also the place where §3's caution applies.
OA2–OA6 are design decisions, not porting items.

---

## 3. Well-bracketing check (prior-art N12, N13)

N12: one-shot continuations plus higher-order state encode `call/cc`, so stack-discipline
reasoning fails (Dreyer–Neis–Birkedal). N13: well-bracketing for handlers is a conjecture
(Timany–Guéneau–Birkedal) (landing.md:48–49).

Core has both ingredients:
- an affine `κ` can be stored in a closure (E9, `storedK_J₁`) or a cell (AT17 `storeResume`, the
  kernel program `store-cancel`, `corpus/kernel-counts.expected:11`);
- it can be resumed after its handler's call has returned.

Every row below is **[inspection]**; nothing was machine-checked.

| reliance | what it uses | can a stored affine `κ` break it? |
|---|---|---|
| **P14.a / R-T1** (`wbCore`; `Core/EffDefs.lean:40`: at every stop the frame list and record list equal those at entry) | a conjunct of `wpG`, proved from its definition | **No.** It is a theorem about Core's relation, and E9's programs are in that relation (`fundamentalC` covers every typed term). R-T1 is about lends, not control: it says no internal lend spans a stop, and that stays true when `κ` is stored. Do not call it "well-bracketing" in SPEC. It is the lexical-stop condition (`foundations/well-bracketing.md`). |
| **P14.b/c** (`ConservativeWB`, `Conservative`): Core proofs at callback types survive in tier 2's `W` | stack-discipline proof principle; T7 | **Possibly**: it quantifies over values at row-abortive types, and a stored `κ` re-enters a returned region. **Tier 2 is shelved**, so not landed. Recheck if tier 2 reopens. |
| borrows crossing operations (SPEC §19 :2348–2354): abortive ops cross a borrow by LIFO unwinding; other control ops do not (T1, #172) | LIFO unwinding of abortive ops | **No.** An abortive op has no `κ`, so nothing is stored. A resuming op cannot be performed across a borrow (typing), so a stored `κ` holds no lend. |
| answering effects as borrows (`withswap`, `Core/Handlers.lean` `op_tail`, `handle_fold`) | tail-resumptive, no `κ` reified | **No.** No continuation exists to store. |
| S5 unwind/cancel order (`unwind_prefix`, `cancel_prefix`, `FinaliserOrder`) | finalisers read off the captured `K` | **No.** The proofs quantify over every run of a typed program, E9b/E9c's cancels of a stored `κ` included. A stored `κ` freezes its `K`, and its cancel runs `K†` (`fins_dead`). |
| algebraicity's simulation (`AlgRel`, `AlgRelH`) | step-for-step relation, memories related cell by cell | **No.** Not a stack argument. `AlgRelH` relates stored values, so a `κ` in a cell is covered (`Instance/AlgSim.lean:99,420`). |
| `CancelsNamed`, `RaiseOK` | run invariant over terms **and** heap (`HeapRaiseOK`, `Base/RaiseNames.lean`) | **No.** Stored values are covered. |
| **`NoDroppedError`** (`kc`, `OnPath`: kept-error holders sit on the evaluation spine) | the holders are on the spine; it excludes runs where `[op]` captures one | **Yes, this is exactly the gap.** The open remainder is a kept error inside a captured, possibly stored, `κ`. The proof's restriction (NKC) is a stack-discipline assumption. Closing it needs counting through continuations and S6 (Status:532–537). |
| **S6 routes** (`OnlyOwnerFrees`: "until `κ` is applied, its cell's location occurs only inside copies of `κ`") | a store-insensitive invariant | **Must cover the heap**: a `κ` stored in a `Ref` (AT17, `store-cancel`) puts the location in a heap value. The route as written (PLAN:1653–1657) names host and runner answers but not stored values. Add `HeapRaiseOK`'s analogue. |
| `I4Runs` (answering as `[handle]`, a two-context simulation "through the continuations outer handlers capture", Status:776) | OPEN | **Risk**: a stack-shaped simulation would fail where an outer handler stores the captured `κ`. State it run-based, as `AlgRel` is. |
| future binary laws (A₂, OA1's free model, `≼`) | any logical-relation proof of contextual equivalence | **Risk (N12)**: do not use well-bracketed reasoning principles; Core has one-shot `κ` plus `Ref`. |

So **no proved tier-1 result relies on well-bracketing**. The well-bracketing reliance sits in
three open items: `NoDroppedError`'s remainder, S6's `OnlyOwnerFrees` route (heap), and
`I4Runs`. It also applies to future binary laws.

---

## 4. Lowering and surface items

Today the checker and backend use none of `letPoly`, `effHandleV`, `lamDead`, general
`effThen`, `PendPers` or `kappaC`. The checker emits `.effHandle` (`Frontend/Check/Rules.lean:270–279`)
and `effThenA` (`Frontend/Check/Rules.lean:258–266`), and every cancel row is empty
(`Frontend/Check/Elab.lean:388`).

| kernel feature | checker / elaborator needs | backend needs | done already |
|---|---|---|---|
| **`letPoly` (row polymorphism)** | The checker already copies a generic function once per effect assignment (decision 45, SPEC §18 :2147). Emit `CDerives.letPoly` for such a let instead of a copy, or prove that the copy *is* `letPoly`'s premise term (`Base/Fill.lean`'s `fill`). Needed for E1, E2d, E6 from source. | none: `letPoly` reduces by one β-step to the copied term (SPEC §24 *Semantics*) | the kernel rule |
| **handler values (`effHandleV`)** | A surface form for a handler as a value (E5's `toResult`/`withLog` as functions of a computation; E9's `stash`). The checker emits `effHandleV` with the clause tuple over the persistent context. | `Capture` must accept a handler whose clauses are a value form, not only `hndTerm n ir ic e`. To check: whether the closure flow already sees it as the same `hnd` prim (`Backend/Kernel.lean`'s `hndE`). | kernel rule; tags written by `rEffHandle` (SPEC §25 :3779–3782) |
| **`[λ-dead]`** | Emit `CDerives.lamDead` for a callback `λ_. M` with `M` typed at the empty context (SPEC §26 *Baseline*: "The checker does not emit the rule"). | none (an ordinary λ) | kernel rule |
| **finalisers with effects (§27)** | A surface finaliser beyond drop glue (`defer`/`finally`-like) whose body may raise or perform. The checker computes cancel rows (`⋈`, `ThenLe`) instead of `effOf [] .unit`, checks `[sub]` at a cancel's use (D3), and decides `PendPers` (it decides `Row.unrDB` already, `Frontend/Check/Decide.lean:812`). | Raising finalisers lower today (`Backend/Clos/Unwind.lean:206`, `Capture`). **Item: the lowering of a finaliser that may suspend. Currently refused (`Backend/Clos/Capture.lean:1006–1015`), UNIMPLEMENTED; not a typing rule (decision 2026-10-12).** Plan: FINALISERS §2.9 (cancel arm as its own code, each finaliser call a resumption point; `[cfin-cancel]` merge; `catchAll` rewrite for unwinding), with kernel shapes `cancel-perform` (`progFinOp`), `cancel-nested` (`progNC₁`), `cancel-dropped` (`progDrop`, `inl ()`), `cancel-resumed` (`progKeep`, `inr ()`), `live 0`, counts measured. | kernel typing; interpreter; raising finalisers lowered |
| **frame deadness** | nothing: no surface construct | **done**: the cancel mask is removed and the lowering keeps the first error (SPEC 0.44; PLAN:2806). The lowered dead region: `Capture`'s cancel arm runs finalisers directly and has no handler stack, so deadness holds by construction (BRIEF §1a: "no handler stack and no search"). To confirm: a kernel program where a finaliser *performs* past a dead handler, which needs the suspending-finaliser lowering. | machine, interpreter, backend, kernel programs `cancel-reentered`/`cancel-propagated` |
| **capture cell → `zeroCell`** | nothing beyond the tags (written) | Nothing: the backend builds `κ` itself (`Kap`) and never sees the cell (`Backend/Clos/Convert.lean:536–538`), and a unit cell takes no words (`Backend/Flat/Lower.lean:421`). Lowering does not detect a double use; typing does. | yes |
| **decision R's tie** | A checker theorem: every emitted derivation is `CDerivesAt Ξ` for the program's effect declarations `Ξ` (the elaborator resolves every op to its declaration's signature, SPEC §18 :2135–2141). | none | Targets only |
| **E5/E9 restriction (decision 2026-10-12)** | Restrict `unr` abortive (`exn`) signatures out: reject `multi ctl op(…) -> never`. At the kernel, the admissible effect contexts gain `NoUnrExn`. SPEC §18's qualifier text and §27 *Open* (E9 at `unr` `exn`) are updated. | none | `NoUnrExn` defined in Targets (`Status:1625`, `status_noUnr_ΞA`) |

**Kernel gaps the next units need** (from Status:811 and PLAN:3266):
- **The `!U C` force rule** (E2a–c, E10 `retry`). Core's `force` reads only a `U C` slot
  (`CDerives.force`, `Core/Fundamental.lean:106`), and `bangE` derelicts an expression. A rule (or
  a derelicting `let`) for forcing a `!U C` slot needs:
  - a SPEC entry;
  - a `_compatC` case;
  - checker emission;
  - estimate ~150 Core lines.
- **`unfold`'s value** (E3, E10 loop). `unfold f g s` is the stepped codata value
  `etaN C ⟨f,g⟩ s`, and no rule types `etaN` (`unfoldN`, `Core/Fundamental.lean:364`, types only
  the constant). It needs a typing rule for the unrolled state with its `Nu` compatibility, and
  `RunsForever` for E3's diverging runs.
- **S6's `OnlyOwnerFrees` and `NoDanglingUse`** (`I/ContUseJ1.lean:514,533`). The routes are at
  PLAN:1653–1664:
  - `OnlyOwnerFrees` is a sealing invariant on the cell's location, and must include heap values
    (§3);
  - `NoDanglingUse` transfers through B5's maps (`RelAt`).
- **Algebraicity at `ΞT`** (`KeptLamFree` fails, `not_keptLamFree_ΞT`). It needs `KeptKapFree`
  and a simulation confining `AlgRel` to captured continuations (Status:305–311). An alternative
  route is to restrict thunks out of kept errors, a surface rule, which is not decided.
- **E5/E9 at an `unr` `exn`**: closed by the restriction above, so no kernel change.
- **K4, a candidate** (effectful fold constants; acceptance: lazily traverse a borrowed tree).
  SPEC §18 *Open* :2259 records K4 as "an early exit from a kernel fold" (a `raise` in
  `fold_own`/`fold_imm`'s algebra). The candidate generalises it to folds whose algebra performs
  (a generator over a borrowed tree). It needs abortive and resuming ops crossing the fold's
  borrow, and resuming ones across a borrow are T1-excluded (#172). Check scope against tier 2
  (shelved) before starting.
- **`TailLaw`, `EtaHold`**: inversions plus OA5.
- **`RowVarKernel J₁`, `FLOpen` at polymorphic slots**: these are A/Instance-side. If Core never
  gains row variables (`letPoly` is the design), they stay S.

---

## 5. SPEC items (list, not text)

Add to **§19 a *Laws* subsection**: the decided algebra
(`research/effects/src/decisions.md:19–55`), each law citing its Core theorem:
1. Deep handler laws H-ret / H-op (at the cell) / H-fwd → `catch_unr`, `catch_cell`,
   `kappaC_resume`, `kappaC_cancel` (U1).
2. Algebraicity → `raise e to x.P = raise e`: `abort_absorbs` (U1); sequencing: `alg_seq` with
   `KeptLamFree` named as its scope (U10), and the gap at `ΞT` stated.
3. Static per-site names → existing §19 *Names* + `tunnel` program (E6).
4. Continuations linear or affine; `unr` tolerated → `kTy`, `refuses_R_clauses` (U7a); S6 when
   proved.
5. Cancel not interceptable, frames dead → `Kont.dead` (definition), `cancel_prefix` (U6).
6. Finally law; finaliser raises propagate; a raise with no live handler is a type error →
   `then_compatC`, `unwind_prefix`, `not_der_progT`, `not_der_e7c` (U6, U7b).
7. Every finaliser runs; first error wins (policy) → `cancel_prefix`; "no error dropped" →
   `no_dropped_nkc` with its scope, plus the tolerated `unr` exception (`progDropT`) (U9).
8. Finalisers perform operations of live handlers → §27 `[then]` + `progFinOpT` (K); lowering
   UNIMPLEMENTED (§4).
9. Safety (no stuck state, no silently dropped error) → `adequacyD_safe`, `effSafe_closed` (U3).
10. Handling is erased → §19 *Lowering* (exists).

Other SPEC edits:
- **§18 and §27**: the `unr` `exn` restriction (decision 2026-10-12). Remove E9-at-`unr`-`exn`
  from §27 *Open* and record it as restricted.
- **§19 *Typing***: decision R. A program's operation signatures are its effect declarations',
  and `CDerivesAt` is the cited judgement (if U4 lands it in Core).
- **§27 *Lowering***: keep "suspending finaliser: unimplemented" as an Open item with
  FINALISERS §2.9's plan, worded so it is not a typing rule.
- **§19 *Laws***: R-T1 named as the lexical-stop condition, with the §3 caution that Core is not
  well-bracketed in control (stored affine `κ`).

**Design facts flagged by the survey** (landing.md §3, :57–64), each recorded as a deliberate
difference from Rust or Koka:
- **N3**: no destructorless value crosses an abort (`effect-abort-live`; SPEC §18 drop glue :2165–2167).
- **N5**: finalisers are "async drop", guaranteed to run by linearity. A suspending one is not
  lowered yet.
- **N10**: static per-site names give no accidental handling (E6).
- **N11**: finalisation is deep, and a finaliser does not run under its own handler (frame
  deadness, D1).

Flags for future decisions, not SPEC text now:
- N1 before any `Rc`;
- N4 for drop glue in generics;
- N6 as library guidance.

---

## 6. Proposed order of porting units

Each unit is one coherent change on a branch from `main`, gated once. Line counts are
**estimates** from the Targets source sizes (`wc -l`), discounted where the A/Instance wrapping
falls away.

| unit | content | depends on | est. Lean lines |
|---|---|---|---|
| **U0** | land the branch's non-`experiments/` diff (§0) on `main`: Core §24–§27, machine, interpreter, backend, checker, SPEC 0.41–0.45, kernel counts. Rebase over `main`'s two BRIEF commits. | — | 0 new (≈+5,100/−1,300 existing) |
| **U1** | `Core/EffMachine.lean`: handler laws at the cell (`catch_unr`, `catch_cell`, `kappaC_resume`, `kappaC_cancel`, `catchEv_cell`, `use_frees_cell`), A2 abort; SPEC §19 *Laws* items 1–2a | U0 | 600–800 |
| **U2** | `Core/Closed.lean`, `Core/Steps.lean` additions, `Core/Run.lean` (`look`, `runM`, `runM_sound`) | U0 | 1,500–1,900 |
| **U3** | `effSafe_closed`, leak freedom at persistent answers, `LiveOK`; SPEC item 9 | U2 | 100–200 |
| **U4** | decision R in Core: `CDerivesAt Ξ`, `toCDerives`; the checker theorem that emitted derivations are tied; the `NoUnrExn` restriction in the checker and SPEC §18 | U0 | 700–900 + checker 100–200 |
| **U5** | `Core/RaiseNames.lean` (`RaiseOK`, `raiseOK_step1`, heap); `cancelsNamed` at tied derivations | U2, U4 | 1,200–1,500 |
| **U6** | S5: `Core/EffCancelRuns.lean` (`unwind_prefix`, `cancel_prefix` with `pend` and the cell, `FinaliserOrder`, `finOK`); SPEC items 5–6 | U1, U5 | 2,000–2,800 |
| **U7a** | `Core/Inversions.lean` + `Core/Rejections.lean`: AT05/06/08/13, `refuses_R_clauses`, `at08-once` kernel program | U0 | 2,200–2,600 |
| **U7b** | §27 rejections `not_der_progT`, `not_der_progNCrecT`, E7c's rejection into `Core/EffCancelTyped.lean` | U7a | 700–1,000 |
| **U8** | the (E) kernel programs (§1.4): derivations in `Core/EffTier1Programs.lean`, answers by `runM`, rows in `kernel-counts.expected` (counts measured) | U2, U7b | 1,500–2,500 (derivations dominate) |
| **U9** | `NoDroppedError` at runs capturing no kept error: `Core/KeptCount.lean` | U5 | 1,700–2,000 |
| **U10** | algebraicity given `KeptLamFree`: `Core/AlgSim.lean` | U2, U6 | 2,000–2,300 |
| **U11** | answering-class laws (`tail_quiet`, `calm`), after OA2 is decided | U1 | 800–1,100 |
| **L1** | surface: emit `letPoly` (or prove copy = `letPoly`) and `[λ-dead]`; corpus programs for E1, E2d, E6 | U0, U8 | checker 200–400 |
| **L2** | surface handler values (`effHandleV`); corpus E5, E9; backend acceptance of value-form handlers | L1 | checker + backend 400–800 |
| **L3** | surface finalisers with effects: cancel rows in the checker; corpus E7a/b/d, E8b, E7c negative | U7b | checker 400–700 |
| **L4** | **lowering of a suspending finaliser** (FINALISERS §2.9) + four kernel shapes, counts measured | U0 | backend 500–900 |
| **G1** | the `!U C` force rule (SPEC entry, compat, checker); then E2a–c, E10 `retry` | U0 | 150–300 + programs |
| **G2** | typing `unfold`'s value (`etaN`), `RunsForever`; then E3, E10 loop | U0 | 400–800 (uncertain) |
| **G3** | S6: `OnlyOwnerFrees` (heap-inclusive sealing), `NoDanglingUse` (B5's maps, so port `bumpSimAt`), then L1's law, `NoDroppedError`'s remainder | U1, U9; B5 port ~2,000 | 2,500–4,000 (uncertain) |
| **G4** | OA1: free model and T-handler (`Core/EffAlgebra.lean`), after a Core binary observation exists | U10 | not estimated |

Suggested order:
1. Foundations: U0 → U1 → U2 → U3.
2. The tie, invariants and S5: U4 → U5 → U6.
3. Rejections: U7a → U7b.
4. Kernel programs: U8.
5. Surface, which can interleave with steps 3–4: L1 → L3 → L2.
6. Lowering: L4.
7. Conditional laws: U9 → U10 → U11.
8. Gaps, in order of unknowns first: G1 → G2 → G3 → G4.

---

## Unspent, unused, untranscribed

- **Unspent hypotheses carried into the landing**:
  - `KeptLamFree` (U10);
  - the NKC restriction (U9);
  - `FinRow` (U6);
  - the tie (U4);
  - `NoUnrExn`/`NoUnr` (E5, E9, E2d).
- **Unused uniqueness results** (PLAN:3299–3301): `det_ourInst`, `rstep_det`,
  `AStep1.deterministic`.
- **Untranscribed in the run-up**:
  - S6's sealing invariant and B5's map coherence;
  - `KeptKapFree` and its confining simulation;
  - FINALISERS §2.9's backend cancel code;
  - AT07's stuck run (`RejectsAT07`);
  - an affine AT08;
  - `ShareCancel`/`FrameW` at non-empty cancel rows (PLAN:2771–2777).
- **Stale text found while reading**:
  - effects-algebra.md:48 says "`KeptKapFree`" where Core's hypothesis is `KeptLamFree`.
  - README.md:181–183 still says S5 and `EProps` "FAIL AS WRITTEN" under option A.
  - README.md:82 still cites `CfinQuiet`.
  - Status still calls the no-interception teeth OPEN in places, but `finRow_teeth_J₁` proves
    them (PLAN:2769).
