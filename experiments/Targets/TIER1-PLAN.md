# Tier 1: the plan

**Tier 1** is design D0 with tier (i) of capabilities as borrows (D1+B4), as
`research/effects/src/synthesis.md` §2.4, §5.2 and §10 describe them. In Lean it is two things:

- the combined theorem at the tier-1 typing system `J₁`, at Core's world:

  ```lean
  I.Tier1 J₁  -- = I.Combined orowRF J₁ coreW admClosedOp .abortive
  ```

- beside it, the two hard-test items that tier (i) and "Laws first" require:
  - the language's answering handlers are native `[handle]`, and the borrow form lends their
    state (D1.h2, the Lean half of D2.c4);
  - a theory with equations, whose answering handler is proved a model through its co-operations
    (D1.h4 (a)–(c), with D1.h3's comodel).

**Every result is at Core σ=[]** (`coreW`, `B.coreB`). Tier 1 keeps T1, so no lend spans a stop.
`W`, Law 2, the spanning rules and `J₂` belong to tier 2, which this track leaves alone.

The six pieces below are ordered by what depends on them. Ties go to the larger unknown first.
`I.Tier1 J₁` also needs work that is not among these pieces; it is listed at the end.

## The pieces

| # | piece | needs | unblocks | risk |
|---|---|---|---|---|
| 1 | Runs at our instance, and four statement checks | — | 3, 4, 5 | low for the machine laws; each check may refute a statement as written |
| 2 | Law 1: `J₁` and the row `∀` | — | 3, 4, 5 | moderate (size) |
| 3 | Adequacy through platform answers and loop iterations; S2, S3 | 1, 2 | B's conjunct of `Tier1` | moderate |
| 4 | What a typed program does at run time: S5's `FinAlone`, and S6 | 1, 2 | S5, S6 | very high |
| 5 | The answering class: h2, h4, the unary laws | 1, 2 | — (tier (i), the hard test) | moderate to high |
| 6 | `BumpSim` (OQ-43), if in reach | — | B5 | high |

**Where each conjunct of `I.Tier1 J₁` comes from:**

| conjunct of `I.Tier1 J₁` | piece |
|---|---|
| A, S0 `MachShape` | 1. `ConfLaws`, `KontLaws`, `NoIO` and `DataInj` are already proved |
| A, `LetLaw`; S1 `RowAlgebra` | 2 |
| A, `DataDiv`; S2 `Safety`; S3 `EffSafe` | 3 |
| A, S4 `HandlerSem` | 1 |
| A, S5 `Cancellation` | 1, given `FinAlone`; `FinAlone` is discharged in 4 |
| A, S6 `ContUse` | 4 |
| A, E1–E10 | the schema halves of E1, E2, E6 and E10 in 2; the runs are not in these six |
| `B.Guarantees J₁.read B.coreB` | B1 in 2; B2, B3, B4, B4′ in 3; B5 in 6; B0, B6, B7 and the bounds are proved or follow from 2 |
| `Bounds coreW`, `Interface coreW` | proved (`tier1Core_world`) |
| `Pins J₁ admClosedOp .abortive` | 2 |
| `Accepts`, `Rejects` | not in these six |

---

## 1. Runs at our instance, and four statement checks

**Goal.** Build the machine layer that every other piece reads:
- a run through a context splits at the point where the inner term stops stepping;
- our labelled machine is deterministic wherever it does not allocate;
- A's laws that concern single runs hold at our instance: S0's semantic laws, S4, and S5, the
  last given that a fired finaliser runs alone (`FinAlone`).

Before any of that, run four checks on statements that our instance may not meet as written.

**First: four statement checks.** Each check is a small typed program and its run, computed at our
machine.
- **If the program types and breaks the statement**, record it as a discharged configuration: a
  theorem `not_… : ¬ …` whose program is typed at `tier1Open`, so that its configurations arise in
  `TW`. Stop that statement's part of this plan, and report. The repair is a change to a target,
  and that is the user's decision.
- **If the program does not type**, record that, and the part goes on.

None of the four is built. Each "expected" below is a reading of the code, not a result.

1. **S6 observes uses through A's encoding of `resume`.**
   - `ResumeAt` matches `plug K₀ (resume κ w)`. Our instance encodes `resume` A-normally, as
     `resumeE` (`Instance/Core.lean:120`).
   - Core's own clauses resume by applying κ directly to `inj₁ ()` and the answer: `clL` in
     `Core/EffPrograms.lean` (typed by `d_clL`) and `ctlClause` in `Base/Programs.lean` both do.
   - Such a run catches κ and passes no `ResumeAt` step. On a complete run at a data answer,
     `uses < caught`.
   - **Witness:** `withLog`'s shape at a label of Ξ, for example `nLogOutside` with Ξ declaring
     name 2 at `(.aff, .unit, .unit)`.
   - **Expected:** `not_contUse_directResume : ¬ (ourInst orowRF Ξ tier1Open).ContUse`.
2. **S5's events name only Ξ's labels.**
   - For a finaliser that raises a name Ξ does not declare, `labelOf`/`errOf` give `finEnd none`.
   - Suppose that raise happens inside a cancel whose canceller handles the name. Then
     `[cfin-raise]` keeps the error and `[cancel-raise]` re-raises it at the canceller. A's trace
     keeps nothing, and `Answered K₀ none` expects `()`.
   - **Witness:** the shape of `Core/EffCancel.lean`'s `prog₃`, typed, with Ξ declaring name 1
     only. Its finaliser raises name 3, which `H₃` handles outside the cancelled region, so the
     error is kept and re-raised at the canceller. `prog₃` has no typing derivation today; the
     check builds one.
   - **Expected, if it types:** `not_noIntercept_undeclared`, and the same for `UnwindOrder` when
     a raise of an undeclared name supersedes the pending one.
3. **`RunsAlike` compares answers as terms.**
   - `TailLaw`, `AlgLaw` and `EtaHold` move code across frames. When the moved code performs an
     operation that a handler outside catches, the two sides capture different continuations.
   - An outer handler may answer with a closure over the continuation it caught, as E1′'s `sched`
     does. The two answers then differ as terms.
   - **Witness:** `sched` around `handle l H (K[perform l i v])`, where `H` has a tail clause whose
     code performs `wait`.
   - **Expected, if it types:** `not_tailLaw_ourInst`, and the same for `AlgLaw` and `EtaHold`.
4. **`FinAlone` is needed.**
   - **Witness:** a configuration, which need not be typed, in which a fired finaliser performs an
     operation that the dying handler catches.
   - That run is not `Alone`, so `NoIntercept` fails on it. This fixes why the S5 bridges below
     take `FinAlone` as a hypothesis, and why typing must supply it.

**Lands.**

```lean
-- Targets/Base/Runs.lean (new): Core's machine, read through contexts
theorem step1_plug_of_step (K : Kont) {μ μ₁ μ' : Heap} {e e₁ E : Expr}
    (he : Step1 μ e μ₁ e₁) (h : Step1 μ (K.plug e) μ' E) :
    ∃ e', E = K.plug e' ∧ Step1 μ e μ' e'
/-- **Run splitting.** A run from `K[e]` is `K` around a run of `e`, or it runs `e` to a term that
takes no step and continues from `K` around that term. -/
theorem steps_plug_split (K : Kont) {μ μ' : Heap} {e E : Expr} (hs : Steps μ (K.plug e) μ' E) :
    (∃ e', E = K.plug e' ∧ Steps μ e μ' e') ∨
    ∃ μ₁ t, Steps μ e μ₁ t ∧ (∀ μ₂ t₂, ¬ Step1 μ₁ t μ₂ t₂) ∧ Steps μ₁ (K.plug t) μ' E
theorem closed_steps …        -- a run from a closed term, with closed stored values, keeps both closed
theorem hndNamesNZ_steps …    -- no step creates a handler named 0

-- Targets/Base/CoreCancel.lean
/-- **A fired finaliser runs alone** (SPEC §19's finaliser row, at run time). In every run of a
typed closed program, under every platform that keeps its protocol, consider a `[then]` frame at
the step that fires it. Its finaliser, run alone from `D ()`, ends only at a value or at a raise
that nothing inside it catches. -/
def FinAlone (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (S : Row) (A : VTy) (e : Expr), Row.NU S →
    J.closed e (CTy.effOf S A) →
    ∀ (c : Conf P) (K₀ K : Kont) (N D : Val) (n i : UInt32) (v : Val),
      PSteps P (init P e) c →
      c.e = K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v))))) →
      K.Catches n = false →
      ∀ μ' t, Steps c.μ (.app (.val D) (.val .unit)) μ' t → (∀ μ'' t', ¬ Step1 μ' t μ'' t') →
        IsVal t ∨ ∃ (K' : Kont) (m j : UInt32) (w : Val),
          t = K'.plug (raiseE (.val (opPayload m j w))) ∧ K'.Catches m = false
theorem unwindOrder_all (J : TypingJ) : UnwindOrder J      -- the run is alone in a handler-free `K`
theorem cancelOrder_of (hN : NoInterception J) (hF : FinAlone J) : CancelOrder J
theorem finaliserOrder_of (hN : NoInterception J) (hF : FinAlone J) : FinaliserOrder J

-- Targets/Instance/Machine.lean (new)
theorem det_ourInst …          -- a step whose redex allocates nothing is the only step of its configuration
theorem runsAlike_of_join …    -- two terms that reach one configuration, by steps that allocate nothing
                               -- and show no event, run alike in every evaluation context
theorem appLaw_ourInst   : (ourInst RF Ξ J).AppLaw
theorem congr_ourInst    : (ourInst RF Ξ J).Congr
theorem opStuck_ourInst  : (ourInst RF Ξ J).OpStuck
theorem loopLaws_ourInst : (ourInst RF Ξ J).LoopLaws
theorem driveLaws_ourInst : (ourInst RF Ξ J).DriveLaws
theorem machShape_orow   : (ourInst orowRF Ξ J).MachShape
theorem handlerSem_ourInst : (ourInst RF Ξ J).HandlerSem
theorem noIntercept_of_core  : NoInterception J.read → FinAlone J.read → (ourInst RF Ξ J).NoIntercept
theorem unwindOrder_of_core  : NoInterception J.read → FinAlone J.read → (ourInst RF Ξ J).UnwindOrder
theorem cancellation_of_core : NoInterception J.read → FinAlone J.read → (ourInst RF Ξ J).Cancellation
```

`FinAlone` is an added hypothesis, so here are its source and scope.
- **Source.** SPEC §19 types `[then]`'s finaliser at the abortive part of the row (`D : F_{Σ^abort} 1`).
- **Scope.** It is what typing gives about a finaliser's own run. It says nothing about the cancel's
  trace, so it does not assume the bridge it feeds.
- **Why `NoInterception` is not enough.** `NoInterception` is syntactic: typed terms hold no
  `ccatch`, no `cfin` and no handler named 0. It does not stop a finaliser from calling a closure
  that performs an operation the dying handler catches.

**Reuses.**
- Decomposition and determinism: `plug_cmp`, `plug_decomp`, `step1_plug_inv_active`,
  `step1_plug_inv`, `steps_plug_inv`, `steps_peel`, `steps_from_val`, `head_det`, `head_det_eff`,
  `AStep1.deterministic`.
- Stopped operations: `opPlug_no_step`, `stop_irreducible`.
- Contexts: `Kont.plug_comp`, `hasHnd_comp`, `catches_comp`, and from `Instance/Bridges.lean`
  `noUnwind_comp`, `fins_comp`, `kontLaws_orow`.
- The head rules `Head.hret`, `hop`, `hunwind`, `uthen`, `ufin`, `ufinC`, `cfret`, `cferr`,
  `cancel`, `creraise`, `seq` and `beta`.
- κ's administrative steps, as `ewp_kappa_resume` takes them (`plug_shift_subst`,
  `Kont.shift_zero`).
- Loops: `hN_steps`, `etaN_obs` (`Core/Nu.lean`).
- Unwinds: `two_frame`, `one_frame`; typing: `noInterception_tier1`.
- The labelled machine: `OStep`, `labelOf`.

**Risk.**
- **Low** for run splitting, S0 and S4. These are local facts at `Live` configurations.
- **Moderate** for S5, for two reasons:
  - its traces hold on every prefix, with the finaliser `Alone`;
  - check 2 may refute it as written.

**Done when:**
- the four checks are recorded, each as a theorem or as a program that does not type;
- the lemmas above are proved;
- `Status.lean` reads:
  - S0 and S4 at our instance: PROVED, at Core σ=[];
  - S5 and `FinaliserOrder`: PROVED given `FinAlone`;
  - S5: OPEN until piece 4.

**Outcome (landed on `tier1-effects`).**
- **The checks.** Checks 1–3 type at `tier1Open` and break their statements, each at the
  admissible context `ΞA` (`Instance/Checks.lean`, `status_checks_ΞA`):
  - check 1: `not_contUse_directResume`. S6 as written fails; its part stops.
  - check 2: `not_noIntercept_undeclared`, `not_unwindOrder_undeclared`. S5 as written fails, so
    `noIntercept_of_core`, `unwindOrder_of_core` and `cancellation_of_core` are not built; that
    part stops.
  - check 3: `not_algLaw_ourInst`, `not_tailLaw_ourInst`. `EtaHold`'s witness is not built:
    `[handle]`'s `hnS` keeps the handled name out of the row its clauses are typed at, so the
    forwarding clause has no derivation by that reading. No inversion checks it.
  - check 4: `not_noIntercept_of_noInterception`, at the typing `J₄` of one untyped program.
  - The restatements of S5, S6, `AlgLaw` and `TailLaw` are the user's decision.
- **Proved.**
  - `Base/Runs.lean`: `steps_plug_split`, `step1_plug_of_step`, `closed_steps`, stuck redexes.
  - `Base/Look.lean`: `look`, a sound evaluator.
  - `Base/CoreCancel.lean`: `hndNamesNZ_steps`, `FinAlone`, `cancelOrder_of`, `unwindOrder_of`,
    `finaliserOrder_of`.
  - `Instance/Machine.lean`:
    - `det_ourInst`, `rstep_det`, `runsAlike_of_join`;
    - `appLaw_ourInst`, `congr_ourInst`, `opStuck_ourInst`, `loopLaws_ourInst`,
      `driveLaws_ourInst`, `machShape_orow`, `handlerSem_ourInst`, `handlerSem_orow`.
- **Deviations from the statements above.**
  - **`LiveOK`**, added to the laws that assert a step (`AppLaw`, `LoopLaws`, `DriveLaws`,
    `HandlerSem`). It says that every configuration a typed program reaches has a closed term and
    goes on. Without it, an open A-value, a handler of non-values or a loop answer of the wrong
    shape is stuck where the law asks for a step. It holds at `JnLog`, a typing of one program
    with a handler, an operation and a continuation (`liveOK_JnLog`). Piece 4 discharges it at
    `J₁`, with `closed_steps`.
  - **`FinAlone`'s raise is of a nonzero name.** The unwind goes on through the next finaliser
    frame by `[finalise]`, which needs a nonzero name. Typed raises are of labels, so typing gives
    it.
  - **`unwindOrder_all` is not built.** `unwindOrder_of` takes `FinAlone`, because the unwind runs
    the finalisers. I have not checked whether `UnwindOrder` fails at some typing without it.
  - At a general row form, `OpStuck` takes that label names are nonzero, and `HandlerSem` takes
    that and that signatures are at most `2³²` long. `orowRF`'s labels carry both, so
    `machShape_orow` and `handlerSem_orow` take only `LiveOK`.
  - `runsAlike_of_join` takes its two runs as chains of head steps that allocate nothing and show
    no event (`HeadChain`).
  - `hndNamesNZ_steps` is in `Base/CoreCancel.lean`, next to `HndNamesNZ`, not in `Base/Runs.lean`.
- **The instance changed.** `coalgE` read the selector's unit as the state. It now shifts `f` and
  `g` past `withPair`'s two binders, as Core's `loopStep` does.
- **Left for piece 4.** Discharge `LiveOK` and `FinAlone` at `J₁`. S5 and S6 wait on the user's
  restatement.

## 2. Law 1: `J₁` and the row `∀`

**Goal.** Build Law 1 (synthesis §10 item 1): the row `∀` is the intersection of its instances.
- **The typing system `J₁`.** It is today's unr-free rules over open rows, with a rank-1 row `∀`
  at `U` and `!U`. The `∀` is Curry-style, under the value restriction.
- **Its semantics.** The relation at `U(∀ρ:k. C)` is the intersection, on the same term, over the
  admissible instances.
- **What follows:**
  - FL at `⟦J₁⟧`;
  - the pins at `J₁`;
  - A's typing-side laws at `ourInst orowRF Ξ J₁`;
  - the schema halves of E1, E2, E6 and E10.

**Lands.**

```lean
-- Targets/Instance/J1.lean (new)
/-- Each rule of `CDerivesNU` over open rows, the prenex row-`∀` entries of the context carried by
every rule, and `[allR-I]` and `[allR-E]` at `U` and `!U` (RESTRUCTURE §4.2). -/
inductive J1Der : RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop
def J₁ : OurTyping orowRF := ⟨J1Der, OutJ.core, fun _ η => η⟩
/-- The elaboration: at every admissible instance, a derivation of `J₁` is a `CDerivesNU`
derivation of a term whose variables are copies of the original's. Each use of a row-`∀` entry gets
its own copy, at its own instance, and substituting one value for all of an entry's copies gives
back the original term. -/
theorem J1Der.elab …
theorem rowVarKernel_J₁ : RowVarKernel J₁                    -- recorded (RESTRUCTURE §4.2)
theorem tier1Open_sub_J₁ : ∀ Θ Δ Γ e j, tier1Open.der Θ Δ Γ e j → J₁.der Θ Δ Γ e j
theorem extendsNU_J₁ : ExtendsNU J₁.read
theorem noInterception_J₁ : NoInterception J₁.read
theorem letLaw_ourInst : (ourInst orowRF Ξ J₁).LetLaw         -- and at `tier1Open`
theorem rowAlgebra_ourInst : (ourInst orowRF Ξ J₁).RowAlgebra -- and at `tier1Open`
-- the schema halves of E1, E2, E6 and E10: each higher-order value typed once at `J₁`,
-- and `PolyUse` / `PolyUseLacks` / `PolyUseOpen` by `[allR-E]` at each row
theorem hof_polyUse_J₁ …  theorem twice_polyUse_J₁ …  theorem compose_polyUse_J₁ …
theorem retryP_polyUse_J₁ …  theorem sumGen_polyUse_J₁ …  theorem fwrap_polyUseLacks_J₁ …
theorem timeoutR_polyUseOpen_J₁ …  theorem retryR_polyUseOpen_J₁ …

-- Targets/I/OpenRel.lean (new; RESTRUCTURE §4.2)
/-- `M.val` at the instance under `η`, except at a prenex `U(∀ρ:k. C)` or `!U(∀ρ:k. C)`, which is
related at every admissible instance, on the same value. -/
def I.ovalW (M : B.BWorld) (b : Bool) : Inst.OVTy → Idx M.Stk → RowEnv → LSub → Val → WProp
def I.FLOpen (M : B.BWorld) (J : Inst.OurTyping orowRF) : Prop
theorem I.fl_of_flOpen : I.FLOpen M J → FL M J.read
theorem I.flOpen_core_J₁ : I.FLOpen B.coreB J₁
theorem I.fl_core_J₁ : FL B.coreB J₁.read
theorem I.i4a_J₁ : I4a J₁.read admClosedOp .abortive         -- `i4a_tier1`'s construction at `J₁`
theorem I.pins_J₁ : I.Pins J₁ admClosedOp .abortive
```

**How FL at `J₁` is proved, and why that way.**
- **The route.** Rows are erased. A row-`∀` entry is a λ-value: it is persistent at `!U`, and used
  once at `U`. So each use of the entry is typed at its own instance in the elaborated derivation.
  - `fundamentalC` holds of the elaborated `CDerivesNU` derivation.
  - `ovalW` at the entry gives the value at every copy's instance, and at `!U` it holds nothing.
  - Hence `FLOpen` holds without restating a single compatibility lemma.
- **The alternative, and why not.** Induction on `J1Der` with each rule's compatibility proved at
  `ovalW` would re-prove `fundamentalC`'s cases. The rules forbid that.
- **`ovalW` is not a new relation.** It reads `M.val` everywhere except at a prenex `∀`.

**Reuses.**
- The open types and today's kernel over them: `tier1Open`, `tier1Open_read`, `OVTy.den`,
  `OCTy.den`, `octxDen`.
- Today's kernel itself: `CDerivesNU`, `CDerivesNU.toCDerives`, `extendsNU_tier1`, the
  `rc_*_tier1NU` lemmas.
- FL and its transport: `fundamentalC`, through `fl_core_tier1NU` and `semW₀_core`.
- The answering borrow form: `i4a_tier1` and its steps (`CDerives.insert_dead`, `deadP_selfSplit`,
  `.withbor2U`).
- Rows: `rowLink_orowRF`, `rowAlgSafe_orowRF`, `orowRF_den`, `liftExt_orow`.
- The row-`∀` rules as stated: `RC_allRI`, `RC_allRE`, `AdmAt`, `FreshIn`.
- Outlives and the bounds: `outExtends_core`, `lifetimeSound_core`, `admExtends_closedOp`.

**Risk.** Moderate. The concept is low-risk (synthesis §10) but the build is large.
- **Size.** `J1Der` has one rule per `CDerivesNU` rule, and the elaboration threads the copies
  through context splits, dead slots and persistent duplication.
- **Typing work.** CLAUDE.md asks for the cost of typing work to be stated. The elaboration
  constructs derivations and needs no inversion. `i4a_J₁` needs a dead-slot weakening lemma at
  `J₁`, the analogue of `insert_dead`.
- **Stop condition.** If some rule cannot be elaborated, for instance a premise that reads a `∀`
  entry other than by `[var]`, stop and report. Do not restate compatibility at `ovalW`.

**Done when:**
- the lemmas above are proved;
- `Status.lean` reads:
  - `FL coreB ⟦J₁⟧`, `Pins J₁`, and S1 and the let law at our instance: PROVED, at Core σ=[];
  - `RowVarKernel J₁`: recorded.

## 3. Adequacy through platform answers and loop iterations; S2 and S3

**Goal.** Prove B2 in full at Core's world: adequacy under every platform that keeps its protocol,
for programs whose platform operations are answered and resumed, and for driven loops, where each
iteration is a `next` of a loop value. From it follow B3, B4 and B4′ at `⟦J₁⟧`, and A's S2 and S3
at `ourInst orowRF Ξ J₁` through the bridges.

**Lands.**

```lean
-- Targets/B/Adequacy.lean (new)
theorem adequateRetAt_core (P : Platform) (hP : P.Respects) : AdequateRetAt B.coreB P
theorem adequateDriveAt_core (P : Platform) (hP : P.Respects) : AdequateDriveAt B.coreB P
theorem adequate_core : Adequate B.coreB                      -- `Adequate coreW.toBWorld`

-- Targets/Instance/Platform.lean (new; RESTRUCTURE §4.1)
def platformOf (R : (ourInst RF Ξ J).Runner) (ε : (RF.alg Ξ).Eff) : Platform
theorem platformOf_respects : R.Respects → (ourInst RF Ξ J).Answers R ε → (platformOf R ε).Respects
theorem runs_platformOf …        -- A's runs under `R` are Core's runs under `platformOf R ε`
theorem runs_platformOf_drive …  -- the same for the driver, a stuttering simulation of `RStep`'s drive
theorem safety_of_sound : Sound J.read → (ourInst RF Ξ J).Safety
theorem effSafe_of_core : EffSafe J.read → EffSafeDrive J.read → (ourInst RF Ξ J).EffSafe
theorem dataDiv_ourInst : (ourInst RF Ξ J).DataDiv

-- Targets/I/Routes.lean, Targets/I/Restricted/InstanceProps.lean
theorem effSafeDriveOfFL : FL M J → FamEmpty M → AdequateEvery M → EffSafeDrive J
theorem tier1Core_B : …                                      -- `tier1Core_B_of adequate_core`
theorem sound_J₁ : Sound J₁.read
theorem soundContracts_J₁ : B.SoundContracts J₁.read B.coreB
theorem guarantees_J₁_of_bumpSim (hS : BumpSim) : B.Guarantees J₁.read B.coreB
theorem safety_ourInst_J₁ (hΞ : AdmEff Ξ) : (ourInst orowRF Ξ J₁).Safety
theorem effSafe_ourInst_J₁ (hΞ : AdmEff Ξ) : (ourInst orowRF Ξ J₁).EffSafe
```

**Reuses.**
- The demonic replay: `theorem32D`, `wpTS_demonic`, `steps_replay`, `Alloc.replay`,
  `Alloc.replay_agree`.
- Totality: `every_alloc_of_wpTS`, `no_infinite_of_wpTS`, `Alloc.ofRun`, `InfRun`,
  `ARun.no_infinite`, `arun_rest_irr`.
- Adequacy as already proved: `adequateEvery_core`'s replay at `wpG`, `adequateRetAt_core_none`.
- The effectful wp: `ewp_unfold`, `ewp_ind`, `cC_effOf`, `opTable`, `contShare`, `Row.tab_some`.
- Data and reclaim: `vC_data`, `reclaim`.
- Loops: `cC_nu_iff`, `relElim_core`, `CTy.loopEffBody_nuOk`.
- The routes: `soundnessOfFL`, `soundContractsOfFL`, `effSafeOfFL`, `comp_of_FL`,
  `tier1Core_B_of`, `famEmpty_core`, `wBound_core`, `exclusiveB_core`, `lifetimeSound_core`.

**Risk.** Moderate.
- **Termination across answers.** It is induction on `ewpTS`'s least fixed point (`ewp_ind`).
  - Each segment is finite by `wpG`, under the allocator that replays it.
  - At a stop, the platform's answer `w` resumes κ through `contShare` at `PB w`. That holds at
    `∅` for a data answer (`vC_data`).
- **The drive.** `SafeDrive` claims every finite prefix, not termination. The invariant is that the
  current step is in the relation at `F_S (A ⊕ U(Loop_S A B))`. Each `inj₂ l` re-establishes it,
  through `cC_nu_iff`.
- **`platformOf R ε` answers ε's closed prefix.** A typed program at a row with a tail variable is
  read at the instance that sends the variable to `[]`, which `anyCon` admits. So S2 needs no S3.

**Done when:**
- the lemmas above are proved;
- `Status.lean` reads:
  - B2 at `coreB` in full: PROVED;
  - B3, B4 and B4′ at `⟦J₁⟧`: PROVED;
  - S2, S3 and `DataDiv` at our instance at `J₁`: PROVED, at Core σ=[].

## 4. What a typed program does at run time: S5's `FinAlone`, and S6

**Goal.** A's (S) properties ask two things about what a typed program does at a configuration it
reaches:
- a fired finaliser runs alone: `FinAlone`, the hypothesis of piece 1's S5 bridges;
- a continuation is used as often as it is caught: S6 `ContUse`.

No proved route gives either. FL and adequacy say what a whole run reaches, not what a frame inside
a reached configuration does. So this piece builds a route, not a lemma. It is the one genuine
unknown on A's side (synthesis §10 item 3), and `FinAlone` shares it.

**Lands, in order.**

1. **S6's teeth** (RESTRUCTURE §6.1), at our machine, whatever piece 1's check 1 found:

   ```lean
   theorem not_contUse_of_der_R1 (h : (ourInst RF Ξ J).der [] (withCl lw dropCl) (F 0 bool)) :
       ¬ (ourInst RF Ξ J).ContUse                             -- and _R2, _R3, _R4
   theorem refuses_R_tier1Open : …                           -- today's kernel types none of R1–R4
   theorem refuses_R_J₁ : …
   ```

   The refusals are inversions. Their cost, stated as CLAUDE.md asks: one inversion lemma per
   constructor on the spine of `withCl`.
2. **The route's statement, reviewed before it is built:**

   ```lean
   /-- The typing of the configurations a typed program reaches: usage and rows only, borrows
   erased; locations through a heap typing, κ at `kTy`. -/
   def CfgTyped (J : TypingJ) : Heap → Expr → Prop
   theorem cfgTyped_init : J.closed e C → CfgTyped J Adequacy.emptyMem e
   theorem cfgTyped_step : CfgTyped J μ e → Step1 μ e μ' e' → CfgTyped J μ' e'
   theorem finAlone_of_cfgTyped : … → FinAlone J
   theorem contUse_of_cfgTyped : … → (ourInst RF Ξ J).ContUse  -- at S6 as it stands after check 1
   ```

3. **The discharges at `J₁`,** if the route is built: `finAlone_J₁ : FinAlone J₁.read`,
   `cancellation_ourInst_J₁`, `contUse_ourInst_J₁`.

**The routes, and where each stops.**
- **8.2, a typing of configurations with preservation.**
  - It changes no kernel definition.
  - It is a new judgement beside `CDerives`. BRIEF §10 allows no side mechanism without a finding.
  - So state `CfgTyped`, have it reviewed adversarially, and build it only if the review accepts
    it.
- **8.4, a ghost token in `contShare`.** This changes Core's relation, which is a kernel change.
  Stop, and report it with the SPEC entry it needs.
- **8.3, the one-shot cell.** This changes the machine, and S4 as stated excludes it. AGREE Q9 puts
  it with the user.

**Reuses.**
- From piece 1: `det_ourInst`, `steps_plug_split`.
- Typing: `noInterception_tier1`, `noInterception_J₁`.
- Continuations: `kTy`, `vC_kTy_of_kapRel` and `contShare`, read and not changed.
- The witnesses: `withCl`, `dropCl`, `twiceCl`, `cancelCl`, `cancelResumeCl` (`A/Programs.lean`).
- The rules that make linearity a typing fact: `[let]`'s capture condition (`effLet`) and
  `[handle]`'s `!U` clauses.

**Risk.** Very high.
- **Expected outcome:** R1–R4 and a reviewed statement of the route; then a stop with a report,
  unless the review accepts 8.2 and it is built.
- **If check 1 refuted S6 as written:** this piece still lands R1–R4 and `FinAlone`'s route, and
  S6 waits on the user's repair of its observation.

## 5. The answering class: h2, h4, the unary laws

**Goal.**
- **Tier (i) of capabilities as borrows.** An answering handler is a tail-resumptive `[handle]`
  (the control form, with decision 59's state passing). The borrow form, which lends the state, is
  its proof device: they type alike and run alike (D1.h2).
- **The theory side of the hard test.** Signatures can carry equations. An answering handler is a
  model when its co-operations validate the equations on the state, Ahman–Bauer's comodel
  (D1.h3, D1.h4 (a)–(c)). Global state is proved as the first theory.
- **The unary laws at our instance,** as far as piece 1's check 3 leaves them standing.

At tier 1 the control form is already sound by `fundamentalC`, since `[handle]` is a rule of
`CDerives`. Discharging `ewp_handle`'s answering case through the borrow form matters at `W`
(tier 2).

**Lands.**

```lean
-- Targets/Base/Answering.lean (new)
/-- The control form runs a body on `capPass`'s spine as its co-operations, threaded through the
state: the native counterpart of `handle_fold`. -/
theorem ctlForm_fold …

-- Targets/I/Interface.lean, Targets/I/Restricted/Answering.lean
/-- **I4, the run correspondence** (D1.h2, unary). Take a configuration that a typed closed program
reaches with the control form in the evaluation context `K₀`. The complete runs from it, and from
the same configuration with the borrow form in `K₀`, reach the same values. Stated at data state,
data operations and a data answer. -/
def I4Runs (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop := …
theorem i4Typing_J₁ : I4Typing J₁.read admClosedOp .abortive    -- the existing target
theorem i4Runs_J₁ : I4Runs J₁.read admClosedOp .abortive

-- Targets/A/Theories.lean (new; imports nothing of ours)
structure SLComp …    -- a straight-line computation over one label's operations, ending in the continuation
structure Eqn …       -- two such computations over the same parameters
def Theory (S : EffectSystem) := S.EA.Lab → List S.Eqn       -- OQ-22 (a): equations in signatures
def ansHnd (co : List S.Val) : S.Hnd                         -- the state-passing handler of co-operations
def runAt (l : S.EA.Lab) (co : List S.Val) (s₀ : S.Val) (M : S.Term) : S.Term
  -- handled by `ansHnd co`, then run from `s₀`; its closing frame is the clause's own
/-- **Handler correctness at the answering class** (Plotkin–Pretnar Def. 4.5, at `RunsAlike`). -/
def AnsCorrect (th : S.Theory) (l : S.EA.Lab) (co : List S.Val) : Prop
/-- **A comodel** (Ahman–Bauer Def. 1 with equations): the co-operations' runs validate each
equation on the carrier. -/
def IsComodel (th : S.Theory) (l : S.EA.Lab) (co : List S.Val) : Prop
def stateSig (T : S.Ty) : List (OpSig S.Ty)                  -- get : 1 ↠ T, put : T ↠ 1, linear
def stateTheory …                                            -- the four laws of global state

-- Targets/Instance/Theories.lean (new)
theorem ansCorrect_of_comodel (hP : PureCo co) : (ourInst RF Ξ J).IsComodel th l co →
    (ourInst RF Ξ J).AnsCorrect th l co                       -- D1.h4 (c)
theorem state_isComodel : (ourInst orowRF Ξ J₁).IsComodel stateTheory l stateCo
theorem state_correct : (ourInst orowRF Ξ J₁).AnsCorrect stateTheory l stateCo
theorem not_ansCorrect_badPut : ¬ (ourInst orowRF Ξ J₁).AnsCorrect stateTheory l badPutCo

-- Targets/Instance/UnaryLaws.lean (new), as check 3 leaves them
theorem tailLaw_ourInst : (ourInst orowRF Ξ J₁).TailLaw      -- or the recorded witness, and
theorem tailLaw_pure …                                       -- the instance the answering class reads
theorem algLaw_ourInst …  theorem etaHold_ourInst …          -- likewise
```

**Two hypotheses this piece adds, and why.**
- **`PureCo co`: the co-operations' runs keep the memory.** `RunsAlike` compares answers, and
  co-operations that allocate would make the two sides of an equation allocate differently.
  `stateCo` meets it.
- **Data state and data operation types in `I4Runs`.** Answers are compared as terms, and a
  co-operation that answers code could perform the handler's own name.

Both are recorded in `Status.lean` as the scope of the result.

**Reuses.**
- The answering forms: `AnsImpl`, `ansCall`, `ansRun`, `ctlClause`, `ctlRet`, `ctlForm`, `capPass`,
  `ImplTyped`, `I4Typing`, `I4a`, `i4a_tier1`.
- The borrow form's run facts: `op_tail`, `op_answer`, `handle_fold`, `clauseRun`, `seqCalls`
  (`Core/Handlers.lean`).
- The handler: `ewp_handle`, `Head.hop`, `kappa`, `withborUE`.
- From piece 1: `steps_plug_split`, `det_ourInst`, `runsAlike_of_join`.
- The unary laws as stated: `RunsAlike`, `ObsFrom`, `TailLaw` (`A/UnaryLaws.lean`), and `toy` for
  non-vacuity.

**Risk.** Moderate to high.
- **The unary laws** stand or fall with check 3.
- **`i4Typing_J₁` inverts typing along `capPass`'s spine.** The cost, stated: one inversion lemma
  each for `[let]`, `[seq]`, `[letpair]`, `[case]`, and `[perform]` under `[sub]`. They are taken
  at `CDerivesNU` through piece 2's elaboration.
- **`I4Runs` needs no renaming lemma.** The borrow form's cell is placed at a location the given
  run never uses, and the control form never needs that cell.
- **`AnsCorrect` holds only if the two sides of an equation meet at one configuration.** For that,
  `runAt`'s closing frame and the clause's resume frame must be the same A-term.

**Done when:**
- the lemmas above are proved, or the unary laws' witnesses are recorded;
- `Status.lean` reads:
  - `I4Typing`, `I4Runs` and the state theory's correctness at `J₁`: PROVED, at Core σ=[];
  - the unary laws: as proved or as refuted, with the witness.

## 6. `BumpSim` (OQ-43), if in reach

**Goal.** Prove the step-for-step simulation, and with it B5 at tier 1 and the whole of
`B.Guarantees J₁.read B.coreB`.

**Lands.**

```lean
-- Targets/Base/BumpSim.lean (new)
def _root_.BoCa.BoLo.Kont.mapLoc (g : Loc → Loc) : Kont → Kont
theorem mapLoc_subst …  theorem mapLoc_shift …  theorem mapLoc_plug …  theorem kappa_mapLoc …
theorem head_sim …      -- each `Head` rule, along `g`, with a bump allocation outside `X`
theorem bumpSim : BumpSim
-- Targets/I/Restricted/InstanceProps.lean
theorem releasedOnceReuse_J₁ : B.ReleasedOnceReuse J₁.read B.coreB
theorem guarantees_J₁ : B.Guarantees J₁.read B.coreB
theorem tier1Core_guarantees : B.Guarantees tier1Open.read B.coreB
```

**Reuses.**
- The statement's own vocabulary: `Named`, `Expr.mapLoc`, `Val.mapLoc`, `Heap.push`, `RelAt`,
  `BlocksAffine`, `Bump`, `BumpSim`.
- The route to B5: `bumpSim_at_reuse` (the `alloc` case's evidence), `releasedOnceReuse_of_bumpSim`,
  `bump_follows`.
- The machine: `head_det`, `plug_decomp`.
- Host calls, which act on literals only and so commute with any renaming (`Host.call`).
- TwoRun's `run_sim` (`experiments/TwoRun/Sim.lean:253`), read as a guide only, since it does not
  build.
- From piece 3: `guarantees_J₁_of_bumpSim`.

**Risk.** High.
- **`BumpSim` was refuted once as written** (AGREE's resolved blocker). Check `tab` first: its
  block's end location `ℓ + n` is what `BlocksAffine` reads at `j = n`. Check `split` next.
- **The other rules to watch:** `count`, `countTry`, `boundedFix`, and the capture step, which
  copies `K` into κ.
- **A step that refutes it** is recorded as a discharged configuration, and the piece stops.

---

## What the six pieces leave for `I.Tier1 J₁`

- **The (E) runs at our instance.** E1–E10's `RunsTo` and `RunsForever` need computed runs: by
  `det_ourInst` and written-out runs, or by an interpreter proved to agree with `OStep`
  (RESTRUCTURE §6.1, §8 step 3).
- **`CompositeT1 J₁.read`.** Each of its eight programs needs an NU derivation, and only
  `d_storeCancelNU` exists. Each also needs one complete run (`logOutside_answers` and the others).
- **`Rejects J₁.read` and `RejectsAT07`.** The first needs inversions, with their cost stated. The
  second needs AT07's stuck run (`at07_eval` is evidence of it).
- **`monoCallback_tier1Open` and its three siblings.** These are the teeth: today's kernel fails
  E1, E2, E6 and E10. They are not conjuncts.
- **Whatever pieces 1, 4 and 6 stop on.**

## Outside this track

- **Tier 2:** `W`, Law 2, the spanning rules, `J₂`, `Tier2Programs`, OQ-8's placement, `reconB′`.
  ProbeD1 is another agent's, in `~/repos/borrow-core-targets`.
- **D1.i1:** `[handle]`'s extent, a kernel rule change with a SPEC entry.
- **D1.a8:** `ClosedLife` as a checked premise of `[perform]` and `[handle]`, a kernel change.
  Tier 1 keeps it as `AdmEff`'s hypothesis.
- **D2.c4's surface half:** §18 emitting `hnd` is Frontend work with a SPEC entry.
- **D2.c11:** an answering class in `ConservativeWB`'s guard. It matters at `W`.
- **Tiers (ii) and (iii) of capabilities as borrows:** extents in types, and OQ-29.
- OQ-28, OQ-56, the binary laws (A₂), lowering (A₃), and multi-shot.

## Every piece

- **Builds:** targeted `lake build Targets` or the one module. No `sorry`, `axiom`,
  `native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`.
- **Checks:** `AxiomCheck` passes, with a `#print axioms` line for each new theorem; `Audit`
  passes.
- **Record:** `Status.lean` rows are updated, each naming its world (Core σ=[]).
- **Imports run one way:** A imports nothing of ours; base imports no A; B imports no A, I or
  Instance; the Instance imports no B or I.
- **No `Core/` edit.** A piece that needs one stops and reports: a kernel change needs a SPEC entry
  and the user.
- **Obstructions:** report one only as an elaborating `def … : Prop`, or as a configuration with
  every hypothesis discharged, reached from a typed program, so that it arises in `TW`. A statement
  a check refutes is reported, not restated. Restating a target is the user's decision.
- **Commit** on `tier1-effects` with the trailer the task names. Never push, and never touch main.
