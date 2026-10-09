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

**Where it stands.** `J₁` is built (decision D5, below). `I.Tier1 J₁` **fails as written**: A's
(E) properties and S5 fail as written at `J₁` (round 3, steps T3 and T4). S4 is restated so that a
catch may allocate the capture cell, and is proved at `J₁` at every effect context (fix-up F1,
below). `Accepts` and `Rejects` are proved (step T5), so `I.Tier1 J₁` follows from A's (E)
properties, S5 and S6 at every admissible effect context (`I.tier1_J₁_of_ECU`). Piece 5 has run:
D1.h4 is proved through the comodel, with global state as the first theory; D1.h2 is open. Piece 6
has run: B5 is proved, and with it `B.Guarantees J₁.read B.coreB`.

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
| `Accepts`, `Rejects` | not in these six; proved in round 3, step T5 |

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

**Outcome (stopped at this section's stop condition; landed on `tier1-effects`).**
- **`J₁` is not built.** The route above does not exist, for three reasons. Each is
  machine-checked at today's kernel (`Instance/Inversion.lean`, `Instance/J1Checks.lean`,
  `I/Tier1Route.lean`).
  1. **A polymorphic let has no elaboration.**
     - At a closed judgement the elaboration copies nothing. So it says that a closed derivation of
       `J₁` is a `CDerivesNU` derivation of the same term (`ElabClosed`).
     - The let law at a row-`∀` value, with a body that reads the bound variable at two
       instances, types `(λx. ⟨x, x⟩) (λx. x)` at `F(!U(1 ⊸ F 1)) & F(!U(1 ⊸ F_[o] 1))`.
     - No `CDerivesNU` derivation types that term. A slot has one type, and every judgement a
       variable is read at is a view of that type (`der_var_inv`, `not_der_letTwo`).
     - So `J1Der.elab`, `letLaw_ourInst` and the rules this section gives `J₁` cannot all hold
       (`not_elabClosed_of_letLaw`). The plan's rules give its two typing hypotheses: `[allR-I]`
       for the value; `[var]`, `[allR-E]` at `!U`, `[ret]` and `[&I]` for the body.
     - `CDerivesNU` has no intersection, and the polymorphic let is where one is needed.
  2. **A-level handlers are not today's `[handle]`.**
     - Our instance encodes A's `handle l H M` as the run-time frame, with the clauses as values
       (`handleK`). S4 and `KontLaws` read that frame.
     - Core's `[handle]` types only `hndTerm n ir ic e`, whose clauses are two variables. No
       `CDerivesNU` derivation has the frame form, at any context and judgement
       (`not_der_handleK`).
     - So a typing system whose closed derivations elaborate fails E8, and so fails `I.Tier1`
       (`I.not_tier1_of_elabClosed`).
     - Today's kernel fails E4, E5, E6, E7 and E8 at every effect context
       (`status_handlers_tier1Open`). RESTRUCTURE §4.3 expected E4, E5, E7 and E8 to hold there.
     - By reading this section's rules, not by a theorem: a `J₁` whose handler rule is today's
       types none of `retryP`, `sumGen`, `fwrap`, `timeoutR` and `retryR`, which five of the
       eight schema lemmas need.
  3. **The uses read a row-`∀` entry by `force`.**
     - Each schema's use is A's `call x g`, which forces `x` itself.
     - `CDerivesNU` forces a variable only from a `U` slot (`der_var_arr_thunk`). It calls no
       `!U` slot at an effectful arrow (`not_der_callBang`).
     - So the use this section describes ("`[var]`, then `[allR-E]` at `!U`, then `bangE`, `force`
       and `[app]`") has no `force` step. Typing the use needs a rule that reads the entry by
       `force`, which is this section's stop condition.
     - A force from a `!U` entry would elaborate to a linear copy. The two branches of `[&I]`,
       `[case]` and `[then]` share one context, so a linear copy that one branch uses must be
       used by the other.
- **What `J₁` needs, and what is the user's decision.**
  - `J₁` needs rules that today's kernel lacks:
    - a polymorphic let;
    - a force of a row-`∀` entry, and of a persistent one;
    - a handler at clause values.
  - `fundamentalC` covers none of these rules. Three ways on, none chosen:
    - prove each new rule sound at `ovalW`, keeping Core's compatibility lemmas for the lifted
      rules through an induction over `J1Der`. This section ruled that induction out;
    - change A's encodings at our instance: calls through a let of the derelicted value, and
      handlers whose clauses are let-bound. This reopens piece 1's machine laws, and still
      leaves item 1;
    - put the row `∀` and these rules into Core's kernel, with a SPEC entry.
- **Proved.**
  - `I/OpenRel.lean`:
    - `I.ovalW` and its computation counterpart;
    - Law 1 at the relation (`ovalW_allR`, `ovalW_bang_allR`);
    - `I.FLOpen`, `I.fl_of_flOpen` and `I.flOpen_core_tier1Open`.
  - `Instance/J1Checks.lean`:
    - `letLaw_ourInst_tier1Open`;
    - `rowAlgebra_noSub_ourInst`: `EA.Laws`, `EA.Safe` and `RowSig` at every typing system;
    - `subClosed_nu_tier1Open`.
  - `I/Combined.lean`: `pins_tier1Open`, from `i4a_tier1NU` (`I/Restricted/Answering.lean`).
    This is `I.Tier1Core`'s `Pins` conjunct.
  - `Base/Support.lean`: `CDerivesNU.insert_dead` and `CDerivesNU.append_dead`.
- **Refuted as written (a check).** S1 at today's kernel, at every effect context.
  - `SubClosed` ranges over every row of the algebra, and `[sub]` asks `Row.NU` of its target.
  - So `()` at the pure row is not typed at a row with a resuming `unr` operation
    (`not_rowAlgebra_ourInst_tier1Open`).
  - It holds at target rows whose prefix is unr-free. The restatement is the user's decision.
- **Not built.**
  - `J1Der`, `J₁` and `J1Der.elab`;
  - `rowVarKernel_J₁`, `tier1Open_sub_J₁`, `extendsNU_J₁` and `noInterception_J₁`;
  - `letLaw_ourInst` and `rowAlgebra_ourInst` at `J₁`;
  - the eight schema lemmas;
  - `I.flOpen_core_J₁`, `I.fl_core_J₁`, `I.i4a_J₁` and `I.pins_J₁`.
- **The cost of the inversions** (CLAUDE.md asks for it). `Instance/Inversion.lean` holds ten
  inductions over `CDerivesNU`, in 765 lines with their invariants.
  - Each induction tells apart the rules whose conclusion's term has another head by one simp set
    over the term constants (`cdnu_terms`, `cdnu_at`).
  - It carries an invariant through the fourteen rules whose premise has the conclusion's term.
  - The invariants are reusable: the views of a slot's type (`ThunkOf`, `ValInv`, `CompInv`), and
    `ν`'s unrolling (`NuUp`, `NuEq`, `NuRoot`).
- **For pieces 3–5,** which need `J₁`:
  - at `tier1Open` they can go on;
  - every (E) property whose program has a handler at its top fails there, and each waits on the
    handler decision in item 2.

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

**Outcome (landed on `tier1-effects`; B2's drive conjunct, S2, S3 and `EffSafeDrive` fail as
written).**
- **B2's return conjunct is proved at every platform** (`B/Adequacy.lean`, `adequateRetAt_core`).
  - A run under a platform is machine segments split at the platform's answers (`psteps_split`).
  - A segment continues to `wpG`'s end under the allocator that replays it (`wpG_seg`), and is
    finite (`wpG_no_infinite`, with `arun_no_infinite_irr`, `ARun.no_infinite` at an end that
    takes no step).
  - At a stop, the operation is the platform's (`stop_op`): linear, data, never abortive
    (`not_raise_stop`). Its argument and the answer hold nothing (`vC_data`), so `contShare` resumes
    `K` at the post's own resource (`answer_at_stop`).
  - Induction on `ewpTS`'s least fixed point (`ewp_ind`) carries `PlatOK`: every run continues to an
    end in the postcondition, and none is infinite (`platOK_of_ewp`). The frame accumulates the
    leftovers, which own nothing, and `↭` from `∅` composes by 6.48 and 6.49 (`seg_frame`). At a
    data answer, `reclaim` empties the memory (`final_of_platEnd`).
- **B2's drive conjunct fails as written** at every platform with an operation
  (`not_adequateDriveAt_core`). So `Adequate coreB` fails (`not_adequate_core`), `B.Guarantees J
  coreB` fails at every `J` (`not_guarantees_core`), and **`I.Tier1 J₁` fails at every `J₁`**
  (`I.not_tier1`), as does `I.Tier1Core` (`I.not_tier1Core`).
  - The configuration: for `o` the platform's, the row `[o, shadowOp o]` reads as `[o]`, so the
    platform answers it. Its loop body is not positive: the shadowed entry's argument type is
    `tvar 0`, and `CTy.EffLeaf` asks every layer's types closed (`not_nuOk_shadow`).
  - `cC` at `νX. C` holds of every term when `C` is not positive, so `()` is in the relation at
    `F_S(U(Loop_S 1 1))` (`cC_loop_unit_of_not_nuOk`). Its drive is stuck at `nextE ()`
    (`not_safeDrive_unit`). The world is the empty one.
- **Proved of the drive.**
  - At a positive loop body, every finite prefix of the drive is safe (`adequateDriveAt_core_nuOk`).
    The invariant: the current step is reached from a start in the relation at
    `F_S(A ⊕ U(Loop_S A B))`, re-established at each `inr l` (`ewp_next_of_loop`, `cC_nu_iff`,
    `loopEffBody_instT`).
  - At rows with distinct keys the body is positive (`adequateDriveAt_core_uniq`), and at the
    platform with no operation every row is (`adequateDriveAt_core_none`, `adequateAt_core_none`).
- **B3, B4, B4′ and B5 at today's unr-free kernel** (`tier1Core_B_nu`).
  - B3 and B4: the return conjunct at every platform (`soundRetAt_tier1NU`); the drive at positive
    loop bodies (`soundDriveAtNu_tier1NU`). The drive at the other rows is OPEN: FL says nothing
    there, and no typed program at such a type is known to get stuck.
  - B4′ in full: it reads only the return conjunct (`soundContractsOfFL_ret`,
    `soundContracts_tier1NU`).
  - B5 given `BumpSim` (`releasedOnceReuse_tier1NU_of_bumpSim`).
- **S2 and S3 fail as written** at today's kernel, at every effect context
  (`Instance/Safety.lean`, `not_safety_tier1Open`, `not_effSafe_tier1Open`).
  - Our instance's typing reads a row through `RF.den` and ties none of its names to `Ξ`. Today's
    `[perform]` types `perform (0, (0, ()))` at the row `[0.0 : 1 ↠ 1]` (`der_perform₀`).
  - No label is named `0`, so the row admits no label's operation (`not_has_ε₀`). The runner that
    answers nothing keeps its protocol and answers everything the row admits.
  - The program is stuck at once (`no_ostep_perform₀`), is no answer, and is no label's stop.
  - `orowAlg`'s `WF` (every name a row finds is a label, at its declared signature) is what such a
    row lacks. Nothing in `ourInst`'s `der` or in today's rules asks it.
- **`DataDiv` is proved** at every row form, effect context and typing system (`dataDiv_ourInst`).
- **`EffSafeDrive` fails as written** at today's unr-free kernel (`not_effSafeDrive_tier1NU`).
  - `FinalDrive` asks a data answer, and a typed loop step may finish at `inl (λ_. ())` at `U(F 1)`.
  - At data answers and positive loop bodies it is proved (`effSafeDriveNu_tier1NU`).
  - The plan's route `effSafeDriveOfFL` fails as written at `coreW` (`not_effSafeDriveOfFL`): a
    typing system that types `return (inr ())` at a loop type whose body is not positive meets FL.
- **Not built.**
  - `adequateDriveAt_core` and `adequate_core`: they fail as written (above).
  - `platformOf`, `platformOf_respects`, `runs_platformOf`, `runs_platformOf_drive`,
    `safety_of_sound`, `effSafe_of_core`: the statements they serve, S2 and S3, fail as written.
  - `tier1Core_B` and `guarantees_J₁_of_bumpSim`: they read `Adequate coreB`.
  - `sound_J₁`, `soundContracts_J₁`, `safety_ourInst_J₁`, `effSafe_ourInst_J₁`: `J₁` is not built
    (§2). Their `tier1Open` forms are the results above.
- **What the restatements would need** (the user's decision).
  - B2's drive (and `SoundDriveAt`, S2's drive, S3 at driven programs): the loop body positive, or
    the loop's row with distinct keys.
  - `EffSafeDrive`: also a data answer.
  - S2 and S3: rows tied to the effect context, in `der`, in the typing system, or in S2 and S3.
- **Typing work.** The S2/S3 configuration needs one derivation (`[perform]` over `[unit]`), and
  `EffSafeDrive`'s needs one (`[ret]`, `[sumI₁]`, `[thunkF]`). No inversion.

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

**Outcome (landed on `tier1-effects`; the route's review did not accept 8.2, so the build stops
there).** Check 1 refuted S6 as written, so this piece followed the plan's second branch: R1–R4
and `FinAlone`'s route. S6 waits on the user's repair of its observation.

- **S6's teeth, R1–R4: PROVED** (`Instance/ContUse.lean`). Every typing system over our machine
  that types one of them at `F 0 bool` fails S6 (`not_contUse_of_der_R1` … `_R4`).
  - Each run is written out at a symbolic label name: 3, 20, 8 and 16 head steps, none of which
    allocates, so each is the program's only run.
  - The counts break as follows:
    - R1 catches `κ` once and uses it never. That breaks the exactly-once clause when the
      label's first operation resumes.
    - R2 and R4 use `κ` twice and catch it at most once (`caught_le_one`), at any label.
    - R3 cancels `κ`, which no affine catch made, when the operation is linear.
  - At a general row form the lemmas take what `orowRF` gives: the pure row reads as the empty
    row, label names are not `0`, and signatures have at most `2³²` operations. The `_orow`
    corollaries take none of these.
  - **Non-vacuity**: `JR` types the four programs, and at `ΞA` each lemma applies to it
    (`teeth_JR_ΞA`).
- **`refuses_R_tier1Open`: PROVED, but for the handler's form, not for linearity.** Today's
  kernel types none of R1–R4 for the same reason it types no A-level handler
  (`not_der_handle_tier1Open`, piece 2's item 2).
  - That refusal needed no new inversion: it reuses `der_hnd_shape`.
- **The linearity refusal at the clauses: PROVED** (`Instance/ClauseRefusals.lean`,
  `refuses_R_clauses`). This is the refusal this section named: `kTy` at `lin`/`aff` is a thunk,
  neither droppable nor persistent, and a linear `κ`'s cancel branch is at `⊤`. It is read at
  `clauseTy`, the type `[handle]` gives a clause.
  - R1's, R2's and R4's clauses are refused at every resuming `lin` or `aff` operation: a live
    slot of `kTy` is neither dropped (`return ff` consumes its context) nor duplicated (both sides
    of a bind read `k`).
  - R3's clause is refused at every `lin` operation: `k (inj₂ ())` at a linear `kTy` is at `⊤`,
    which no bind takes.
  - **Pinned** (`clauseRefusals_pinned`). At the clause type of a linear `1 ↠ 1`, where all four
    clauses are refused, a clause that resumes `κ` once is typed (`d_tailClNU`). `cancelCl`,
    which cancels `κ`, is typed at `aff` (`d_cancelClNU`) and refused at `lin`.
  - **Scope.** At `unr`, `kTy` is `!` and persistent, so the argument does not apply. `clsOf`
    reads a resuming `unr` operation as affine. Multi-shot is not considered.
  - It would matter to a `J₁` whose handler rule types A-level handlers with today's clause
    types.
- **`refuses_R_J₁`: not built.** `J₁` is not built (§2).
- **`FinAlone` FAILS AS WRITTEN** (`Instance/RunTyping.lean`, `not_finAlone_of_types`,
  `not_finAlone_tier1NU`).
  - It ranges over every platform that keeps its protocol, and nothing ties the type a platform
    answers at to the one the program's row declares.
  - The configuration: `finProg` performs `1.0 : 1 ↠ 1`, then raises under a finaliser `x; ()`.
    `Pmis` answers `1.0` at `1 ⊕ 1` and keeps its protocol. The fired finaliser's run alone stops
    at `inj₁ (); ()`.
  - B2's `AdequateRetAt` asks `RowLe S P.ops`; `FinAlone` does not.
  - `FinAlone`'s only consumer reads it at the platform with no operation and the pure row
    (`finAlone_at`). Restating it is the user's decision.
- **`LiveOK` FAILS AS WRITTEN at today's kernel and `ΞA`** (`not_liveOK_ΞA`). Piece 1 left its
  discharge here.
  - Today's `[perform]` types `perform (6, 0, ())` at the row `[6.0 : 1 ↠ 1]`. At `ΞA` the name
    `6` is `kube : 1 ↠ bool`.
  - The runner that answers `kube` at its declared type keeps its protocol. The sequenced answer
    `inj₁ (); ()` is stuck: no answer, no step, no operation.
  - This is the root cause of S2's and S3's failure (§3): rows are not tied to the effect context.
    The repair that §3 lists would serve `LiveOK` too.
  - S0 and S4 are proved given `LiveOK`. Whether they hold at today's kernel without it is not
    checked.
- **`FinaliserOrder` now takes the platform-free form.**
  - `FinAloneAt` is `FinAlone` at the platform with no operation and the pure row
    (`Base/CoreCancel.lean`). `finaliserOrder_at`, `cancelOrder_at` and `unwindOrder_at` take it.
  - `finaliserOrder_of` and its siblings keep their statements, through `finAloneAt_of_finAlone`.
- **`FinAloneAt` splits in two, and B gives one half** (`I/Restricted/FinAlone.lean`).
  - **Stuck redexes, from B.** A program in Core's relation never gets stuck without a platform
    (`stuck_of_rel`, from `platOK_of_ewp`).
    - The fired finaliser is the innermost frame that stops the raise (`step1_raise`,
      `innerCatch_unique`, `head_ubind_raise`). So the finaliser's run alone is the whole run's,
      inside `K₀[□; raise p]` or `K₀[cfin p □]`.
    - A term that is no value and leaves no operation uncaught takes no step in such a context
      (`no_step_plug`, from `head_plug`).
  - **Operations, which typing must give.** `FinRowsAt J`: an operation the finaliser's run alone
    leaves uncaught is a raise of a nonzero name.
  - `finAloneAt_of_finRows`: `FinRowsAt J` and FL at Core's world give `FinAloneAt J`.
  - So **`FinaliserOrder tier1NU` follows from `FinRowsAt tier1NU` alone**
    (`finaliserOrder_tier1NU_of_finRows`, with `fl_core_tier1NU` and `noInterception_tier1NU`).
- **The route's statement** (`RowRoute J`).
  - `Typed μ E S` is a term typed at a row through the heap. Its obligations:
    - `reach`: configurations that typed programs reach are typed at the pure row (the plan's
      `cfgTyped_init` and `cfgTyped_step` along the run);
    - `fire`: a fired finaliser is typed at a row of abortive operations with nonzero names;
    - `step`: typing is preserved by steps;
    - `stop`: such a term leaves no resuming operation and no cancel uncaught.
  - `finRowsAt_of_route` and `finaliserOrder_of_route` prove the obligations suffice.
  - `contUse_of_cfgTyped` is not stated: S6 stands refuted (check 1).
- **The review (adversarial; mine, not an independent reviewer's): route 8.2 is not accepted.**
  - **The obligations are not circular only if `Typed` is a syntactic judgement.** With `Typed`
    defined as "reached, and well behaved", `reach`, `fire` and `step` hold by definition and
    `stop` is `FinRowsAt` itself. So the route is a typing of run-time terms with preservation:
    `step` is subject reduction and `stop` is canonical forms. That judgement sits beside
    `CDerives`, which BRIEF §10 allows only on a finding. The finding is above: B supplies every
    part of `FinAloneAt` but `FinRowsAt`.
  - **What `Typed` must type that `CDerivesNU` never does:**
    - run-time handler frames whose clauses are values (`not_der_handleK`);
    - `κ` values, whose bodies hold `hnd H K[x]` for a captured `K`;
    - `ccatch` and `cfin` frames;
    - locations and array values;
    - the intermediate states of the machine's loops (`tabFill`, `dropFill`, `countNext`,
      `countTryNext`, `boundedFixNext`).
  - **Every constant's body.** Core types its constants as axioms: the borrow constants, the
    array and slice operations, the folds and `unfold`. A β-step exposes the body, so `step`
    needs a rule for each body.
    - `withbor` and `withswap` use the location more than once (owner and borrow). With borrows
      erased, locations must be unrestricted.
    - The folds and `unfold` recurse through the self-application `selfV` (`Core/Fix.lean`),
      which no simple typing types, so each needs a dedicated rule for its unrolled states.
  - **Subject reduction needs a substitution lemma for `Typed`,** and `fire` needs its inversion
    at every frame former. Core has neither for `CDerives` (`fundamentalC` is semantic), and
    CLAUDE.md asks for inversions to be costed. The cost is one preservation case per head rule
    (27) and one rule per run-time form and constant body: on the order of thousands of lines,
    an estimate, not a measurement.
  - **The heap typing with borrows erased may need an invariant an erased typing cannot state.**
    Preservation must hold for every configuration `Typed` accepts, not only for those a run
    reaches.
    - An erased `Typed` would accept a configuration in which a copy of a borrowed location still
      occurs after its owner frees it. An `alloc` that reuses the location at another type would
      then break the heap typing.
    - Excluding such configurations would need the ownership discipline that lifetimes give, which
      an erased typing drops. BoLo establishes that discipline semantically, and B3 speaks of
      uses, not occurrences.
    - I have not built such a `Typed`, I have not derived such a configuration from a typed
      program, and I have not verified that any obstruction is real. It is a risk, not a claim.
  - **What it would buy now:** `FinaliserOrder tier1NU` (Core's I3.b). S5 at our instance fails as
    written (check 2), and S6 too (check 1), so their payoff waits on the user either way.
- **The other routes.**
  - **8.4, a ghost token in `contShare`** (for S6), changes Core's relation, so it stops here.
    The SPEC §19 entry it would need: at `lin` and `aff`, `contShare` also owns a non-persistent
    obligation for `κ` in the world, created at `[op]` and consumed by its resume or its cancel.
    `NoOwn` at a run's end then forces every caught `κ` to be used. It must preserve
    `fundamentalC`, `adequacyC`/`adequacyD`, B2–B5 at `coreB`, `ewp_handle` and `i3_core`. It
    leaves open the coupling from consuming the token to the step that resumes or cancels `κ`,
    which S6's counts read.
  - **For `FinRowsAt`, the relation-level analogue** is an obligation in the world for each live
    finaliser frame, consumed at `[finalise]`. It too is a kernel change and needs a SPEC entry.
  - **8.3, the one-shot cell,** is the user's (AGREE Q9).
- **Not built:**
  - `CfgTyped` and its theorems (the review above);
  - `finAlone_J₁`, `cancellation_ourInst_J₁` and `contUse_ourInst_J₁`: `J₁` is not built,
    `FinAlone` fails as written at every typing system that types `finProg`, and S5 and S6 fail
    as written.
- **Typing work** (CLAUDE.md asks for the cost).
  - Two `CDerivesNU` derivations (`d_finProgNU`, `d_lvProgNU`).
  - `refuses_R_tier1Open` reuses piece 2's `der_hnd_shape`.
  - The clause refusals need seven inversions, each one induction over `CDerivesNU`'s 89
    constructors: `der_free_live`, `der_unit_dead`, `der_lam_arr`, `der_letpair_split`,
    `der_var_tensor`, `der_appLam_split` and `der_cancel_lin`. The file is about 800 lines.

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

---

## Tier-1 track outcome

**Where the track ends.** `I.Tier1 J₁` is not proved: `J₁` is not built (piece 2; decision D5).
After the four pieces, seven target statements failed as written at configurations built in Lean.
The user restated them on 2026-10-07 (D1–D4, D6), and the restatements are applied below
("Decisions of 2026-10-07"). With them, `I.Tier1Core` follows from S5 at today's kernel and
`BumpSim` (`I.tier1Core_of`), and S2, S3 and `LiveOK` hold at today's kernel. Pieces 5 and 6 were
not run. Every result is at Core σ=[]. `lake build Targets` passes with AxiomCheck and Audit, every
new result's axioms are within `[propext, Classical.choice, Quot.sound]`, and nothing in `Core/`
changed. HEAD after the four pieces was `56f10a8`; none of it is pushed. The per-piece notes below
record each piece as it landed; where a decision restated a statement, the note's refutation is no
longer in the build.

| # | piece | status | verifier | commits |
|---|---|---|---|---|
| 1 | Runs at our instance, and four statement checks | LANDED; S0, S4 and `FinaliserOrder` proved given `LiveOK`/`FinAlone`; checks 1–3 break S6, S5, `AlgLaw`/`TailLaw` as written | pass | 2a84ac7, bc4218b, 12d5e83, 188d4de |
| 2 | Law 1: `J₁` and the row `∀` | STOPPED at its stop condition; Law 1 at the relation proved (`ovalW_allR`, `FLOpen`); `J₁` not built | **fail: one major finding (open, below)** | dff0a57, 335046f |
| 3 | Adequacy through platform answers and loop iterations; S2, S3 | LANDED; B2's return conjunct proved at every protocol-keeping platform; B2's drive, S2, S3, `EffSafeDrive` fail as written | pass | d53c464 |
| 4 | `FinAlone` and S6 | PARTIAL; R1–R4 teeth and the clause refusals proved; `FinAlone` and `LiveOK` fail as written; route 8.2 not accepted, not built | pass (the route's review was the agent's own) | 789506a, 56f10a8 |
| 5 | The answering class: h2, h4, the unary laws | PARTIAL (the last section); h4 through the comodel and global state proved, and the tail law and algebraicity at the answering class; `AlgLaw` fails as written at `J₁`; `TailLaw`, `EtaHold`, `I4Typing` and `I4Runs` open | not run | 6e38745, 3d861cb |
| 6 | `BumpSim` (OQ-43) | LANDED (the last section); the simulation proved at the configurations a bump run reaches (`bumpSimAt`), B5 proved from B4′, `B.Guarantees J₁.read B.coreB` proved; `BumpSim` over every related configuration not proved, not used | not run | 3870da8 |

### Piece 1

- **Proved.** Run splitting and the `look` evaluator (`Base/Runs.lean`, `Base/Look.lean`);
  `det_ourInst`, `runsAlike_of_join`; S0 `machShape_orow` and S4 `handlerSem_orow` given `LiveOK`;
  `finaliserOrder_of` given `NoInterception` and `FinAlone`; `liveOK_JnLog`.
- **Fails as written** (each at `ΞA`): S6 (`not_contUse_directResume`), S5
  (`not_noIntercept_undeclared`, `not_unwindOrder_undeclared`), `AlgLaw`, `TailLaw`
  (`not_algLaw_ourInst`, `not_tailLaw_ourInst`); check 4 shows `FinAlone` is needed
  (`not_noIntercept_of_noInterception`).
- **Added hypotheses.** `LiveOK`; `FinAlone`'s nonzero raise name.
- **Unchecked.** `EtaHold`'s witness (no inversion); whether `UnwindOrder` fails without
  `FinAlone`.

### Piece 2

- **Proved.** Law 1 at the relation (`I.ovalW`, `ovalW_allR`, `ovalW_bang_allR`, `I.FLOpen`,
  `I.fl_of_flOpen`, `I.flOpen_core_tier1Open`); `letLaw_ourInst_tier1Open`;
  `rowAlgebra_noSub_ourInst`; `i4a_tier1NU` and `I.pins_tier1Open`.
- **Why `J₁` stops.** Three Lean facts against `CDerivesNU`: no polymorphic let
  (`not_der_letTwo`, `not_elabClosed_of_letLaw`); A-level `handle` is not the form `[handle]` types
  (`not_der_handleK`, `I.not_tier1_of_elabClosed`, `status_handlers_tier1Open`); a schema's use
  needs a `force` of a `∀` entry (`der_var_arr_thunk`, `not_der_callBang`).
- **Decision for the user.** `J₁` needs a polymorphic let, a `force` of a polymorphic entry and a
  handler with value clauses. Options: prove each new rule sound at `ovalW`; change A's encodings at
  our instance; or add the rules to Core with a SPEC entry.

> **OPEN VERIFIER FINDING (major), piece 2.** The S1 refutation
> `not_rowAlgebra_ourInst_tier1Open` (`Instance/J1Checks.lean`, `unrOp`) uses the row `[unrOp]`,
> which is not `(orowAlg Ξ).WF` at any `AdmEff Ξ`: `Ξ.NU` makes every `unr` operation abortive, so
> `WF ⇒ Row.NU`. The check measures our `A.SubClosed`, which ranges over rows "well formed or not"
> and omits the well-formedness premise Yoshioka's `[sub]` carries (`Γ ⊢ ε₂ : Eff`). That is a
> defect in our transcription of S1, not a fact about S1 at our instance. Not yet done: prove
> `WF Γ ε → Row.NU ε.ops` at `AdmEff Ξ`; with `subClosed_nu_tier1Open` this gives subeffecting at
> every well-formed target. Status.lean's S1 row still reads FAILS AS WRITTEN, and its `Tier1Core`
> line is inconsistent with the refutation. Until this is resolved, do not cite the S1 refutation.

### Piece 3

- **Proved.** B2's return conjunct at every platform that keeps its protocol
  (`adequateRetAt_core`, by induction on `ewpTS`); the drive at positive loop bodies, at rows with
  distinct keys, and in full at `Platform.none` (`adequateDriveAt_core_nuOk`, `_uniq`, `_none`);
  `I.tier1Core_B_nu` (B3/B4 return, B4′ in full, B5 given `BumpSim`); `Inst.dataDiv_ourInst`;
  `effSafeDriveNu_tier1NU`.
- **Fails as written.** B2's drive at every platform with an operation (`not_adequateDriveAt_core`,
  hence `not_adequate_core`, `not_guarantees_core`); S2 and S3 at `tier1Open`
  (`Inst.not_safety_tier1Open`, `Inst.not_effSafe_tier1Open`: rows are not tied to `Ξ`);
  `EffSafeDrive` (`not_effSafeDrive_tier1NU`); the route `EffSafeDriveOfFL`
  (`not_effSafeDriveOfFL`).
- **Open.** B3/B4's drive at non-positive loop bodies; not derived, and no stuck typed program
  checked.
- **Unspent hypotheses.** `P.Respects.nz`; `Row.NU S` in `effSafeDriveNu_of_FL`.

### Piece 4

- **Proved.** S6's teeth `not_contUse_of_der_R1` … `_R4` with witnesses at `JR` and `ΞA`
  (`teeth_JR_ΞA`); `refuses_R_tier1Open`; the linearity refusal at `clauseTy`
  (`refuses_R_clauses`, `clauseRefusals_pinned`); `FinAloneAt`, `finaliserOrder_at`;
  `finaliserOrder_tier1NU_of_finRows` (FinaliserOrder from `FinRowsAt` alone);
  `finaliserOrder_of_route`.
- **Fails as written.** `FinAlone` (`not_finAlone_of_types`, `not_finAlone_tier1NU`) and `LiveOK`
  (`not_liveOK_ΞA`): both from platform answers not tied to the program's row, the same cause as
  S2/S3.
- **Not built.** `CfgTyped` and route 8.2 (a syntactic run-time typing with subject reduction;
  thousands of lines, estimated). Route 8.4 is a kernel change; its SPEC §19 entry is drafted in §4.
  Route 8.3 is the user's call (AGREE Q9).

### Decisions for the user

> - **S1:** add `[sub]`'s well-formedness premise to `SubClosed` (the verifier finding above).
> - **Rows and `Ξ`:** tie rows to the effect context. One repair serves S2, S3 and `LiveOK`.
> - **Platform answers and rows:** restate `FinAlone` as B2's `AdequateRetAt` does (`RowLe S P.ops`).
> - **B2's drive, `SoundDriveAt`, S3 for driven programs:** a positive loop body or distinct keys,
>   or a change to Core's relation at non-positive `ν` (kernel; SPEC entry).
> - **`EffSafeDrive`:** also require a data answer.
> - **S5, S6, `AlgLaw`, `TailLaw`:** restate the observations (checks 1–3).
> - **`J₁`:** one of the three options under piece 2.

The user decided these on 2026-10-07 (D1–D6, below); D1–D4 and D6 are applied, D5 is next.

### Untranscribed in the run-up

`J₁` and `J1Der`; `CfgTyped`; the bridges `noIntercept_of_core`, `unwindOrder_of_core`,
`cancellation_of_core`; `platformOf`; pieces 5 (h2, h4, the unary laws) and 6 (`BumpSim`).

### Next

Superseded by "Decisions of 2026-10-07", below: piece 2's verifier finding is resolved (D6), and
the decisions are applied but D5.

---

## Decisions of 2026-10-07: D1–D4 and D6 applied

**The decisions** (the user's):

- **D1.** Tie rows to the effect context `Ξ`: the one repair serving S2, S3 and `LiveOK`.
- **D2.** B2's drive conjunct holds under distinct keys (well-formed rows) and positive loop
  bodies; state these as hypotheses or well-formedness.
- **D3.** Finalisers, option A: the `[then]` finaliser premise requires a finaliser's raises to be
  handled locally (no escape). S5's set of endings is parameterised by what finalisers may raise;
  option A is the empty instance. OQ-7 stays separate and open. This subsumes the `FinAlone`
  restatement.
- **D4.** Restatements: S6 counts a direct application of `κ` as a use; `AlgLaw`, `TailLaw` and
  `EffSafeDrive` compare observationally, not as terms; S5 per D3; the cancellation statement
  carries the no-interception condition explicitly.
- **D5** (next step, not this one). `J₁` by new Core rules.
- **D6.** Prove `WF → Row.NU` at `AdmEff`, drop the invalid S1 refutation, fix Status.lean.

**How each landed.**

| decision | statements | the hypothesis is needed |
|---|---|---|
| D1 | `RowAt Ξ S` (`Instance/Rows.lean`): every operation the row finds is a label's, at the signature `Ξ` declares; `orowAlg.WF` and `closedRowAlg.WF` read it; `OCTy.TiedAt`, `EnvAt` (`Instance/Core.lean`); our instance's `der` carries `C.TiedAt Ξ` | `safety_needs_tie`, `liveOK_needs_tie` |
| D2 | `CTy.NuOk` of the loop body in `AdequateDriveAt`, `SoundDriveAt`, `EffSafeDrive` and `IsLoopSum`; distinct keys give it at a platform that answers the row (`loopEffBody_nuOk_of_uniq`) | `adequateDrive_needs_nuOk`, `effSafeDrive_needs_nuOk` |
| D3 | `Cancellation FR`, `FinEnd FR`, `noFinRaise` (`A/Soundness.lean`), `SProps` at `noFinRaise`; `FinAloneAt FR`, `FinRowsAt FR`, `finaliserOrder_at`, `finaliserOrder_A` (`Base/CoreCancel.lean`); the platform-quantified `FinAlone` is gone. The kernel half, `[then]`'s finaliser premise at option A, is a Core change and waits with D5: today's `[then]` types the finaliser at the row's abortive part | — |
| D4 | S6: `UseAt`, `uses`; `RunsAlike` at a program's data answers; `EffSafeDrive` observes a finished drive (`DoneDrive`); `NoIntercept FR`, `UnwindOrder FR` take `∀ D ∈ fins K, FinRow FR D` | `noIntercept_needs_finRow` |
| D6 | `SubClosed` at a target well formed under some variables; `rowNU_of_rowAt`, `rowNU_of_wf`; S1 at today's kernel, `rowAlgebra_ourInst_tier1Open` (at `Ξ.NU`); `not_reconciler_of_monoCallback` takes labels well formed at `[]` | `subClosed_needs_wf` |

**Readings to confirm.** Four places where the decision's words admit more than one statement:

1. *"The cancellation statement carries the no-interception condition explicitly"* (D4) is read
   as a hypothesis on the finalisers a cancel or an unwind fires: `FinRow FR D`, `D` closed and
   typed at a row whose operations are abortive operations of labels in `FR` (SPEC §19's
   finaliser row). At `noFinRaise` that row admits nothing.
2. *"S6 counts direct application of κ as a use"* (D4) is read as: a use is a step whose
   configuration applies `κ` to a data value at the evaluation position (`UseAt`). `resume κ w`
   (A-normal) counts once, at its application step; `cancel κ` is `κ (inj₂ ())`.
3. *"Compare observationally"* (D4) is read, for `RunsAlike`, as comparing programs at data
   answers (`DataTy A → der [] P (F ε A)`), and, for `EffSafeDrive`, as observing a finished drive
   (`DoneDrive`: the drive at a value) instead of `FinalDrive`'s data answer with the memory empty.
4. *"Distinct keys and positive loop bodies"* (D2) is carried as positivity (`CTy.NuOk`); distinct
   keys at a platform that answers the row give it (`loopEffBody_nuOk_of_uniq`).

**Found and repaired: an encoding defect in our instance.** `perform l i v` and `raise l i v` read
the index `i : ℕ` through `UInt32.ofNat`, so `i` and `i + 2³²` were one operation. A runner that
keeps its protocol (`Runner.Respects` constrains only the indices a label's signature has) could
answer `perform l (i + 2³²) v` at any type, and `LiveOK` failed at today's kernel even with the
tie. This was checked in Lean before the repair (`not_liveOK_alias`, in scratch, standard axioms;
not kept, since it measures the old encoding). An index beyond `UInt32` now encodes to `opJunk`,
an open stuck term that no closed configuration holds (`not_closed_opJunk`, `no_ostep_junk`).
Nothing in BoLo changed.

**Proved now** (Core σ=[]; every result's axioms within the standard three):

- **S2, S3 and `LiveOK` at today's kernel, at every effect context**
  (`I/Restricted/InstanceSafety.lean`: `safety_ourInst_tier1Open`, `effSafe_ourInst_tier1Open`,
  `liveOK_tier1Open`). A typed closed program is closed (`closedAt_of_derives`,
  `Base/Closed.lean`) and in Core's relation (`der_cases`). A run under a runner is the run under
  the platform it gives (`platformOf`, `Instance/Platform.lean`), step for step from a typed
  program (`pstep_of_io`, `plain_rstep`, `drive_rstep`). Under a platform that answers part of the
  row, every run continues to an end or to a stop of the row the platform does not answer
  (`platSafe_of_ewp`, `driveSafe_cont`, `B/PlatSafe.lean`). B2 gives the rest
  (`adequateRetAt_core`, `safeDriveFrom_of_rel`).
- **S0 and S4 at today's kernel, at every effect context**, from `LiveOK`.
- **S1 at today's kernel** at every effect context with no resuming `unr` operation
  (`rowAlgebra_ourInst_tier1Open`).
- **B2 at BoLo** (`adequate_core`), so B3 and B4 at today's unr-free kernel (`sound_tier1NU`);
  the drive at positive loop bodies (`adequateDriveAt_core`, `soundDriveAt_tier1NU`).
- **`EffSafeDrive`** at every typing system with FL at BoLo (`effSafeDrive_of_FL`), so at today's
  unr-free kernel (`effSafeDrive_tier1NU`).
- **`I.Tier1Core` given S5 at today's kernel and `BumpSim`** (`I.tier1Core_of`); A's properties but
  S5 at every admissible context (`I.sPropsNoCancel_tier1Open`).

**Remaining.**

- **S5 at our instance** (`Cancellation noFinRaise`): the bridges `noIntercept_of_core` and
  `unwindOrder_of_core` from Core's `FinaliserOrder` are not built. `FinRowsAt`, what typing gives
  about a finaliser's own run, is OPEN; route 8.2 is not built.
- **S6 at our instance**, restated: not proved at today's kernel.
- **The unary laws at our instance**, restated: not checked.
- **`EffSafeDriveOfFL`** at a generic world: OPEN.
- **`BumpSim`** (OQ-43): OPEN.
- **`J₁`** (D5): a polymorphic let, a `force` of a polymorphic entry, and a handler with value
  clauses, as new Core rules.
- Pieces 5 and 6: not run.

**Unspent hypotheses.** S2, S3 and `LiveOK` hold at every effect context; `AdmEff` is spent in
`Tier1Core`'s A conjunct only by S1 (`Ξ.NU`). `I.Tier1Core`'s `AdmEff` conjuncts `ClosedLife` and
`Rich` are not used by any S property at today's kernel.

**Untranscribed in the run-up.** `noIntercept_of_core`, `unwindOrder_of_core`; `CfgTyped` (route
8.2); `J₁` and its FL.

**Next.**

1. D5: `J₁` by new Core rules (a SPEC entry each), and FL for them; with them, D3's `[then]`
   premise at option A.
2. S5's bridges at `noFinRaise`, from Core's `FinaliserOrder` (`finaliserOrder_A`) and `FinRowsAt`
   at option A.
3. S6 at today's kernel, restated.
4. Piece 5 (h2, h4 through the comodel) and piece 6 (`BumpSim`).

---

## Decision D5 applied: `J₁` by new Core rules

**The decision** (the user's, 2026-10-07). `J₁` gets its rules from Core: row polymorphism (a `∀`
over rows or a polymorphic let) and a general `[handle]`, each with a SPEC entry and its
`fundamentalC` case, and with them D3's kernel half (`[then]` at option A). Nothing may change
BoLo's definitions or weaken a borrow guarantee. S6's route 8.4 goes probe-first.

**Core: SPEC §24 (Entry 23).** No change to the machine, the relation (`cC`, `vC`, `wpTS`, `wpG`,
`ewpTS`) or any borrow rule. `fundamentalC`, `adequacyC` and `adequacyD` keep their statements
and hold over the extended judgement.

| rule | `CDerives` | its `fundamentalC` case |
|---|---|---|
| `[let-poly]`: `let x = λy. b in N` for a closed λ-value, from `N` with the λ-value for `x`, `x`'s slot dead | `letPoly` | `letPoly_compatC` (`Core/PolyLet.lean`): one β-step that allocates nothing (`cC_head`); closing at the dead slot is closing `N` at the λ-value (`psub_fill`) |
| `[handle]` at a value form: the handler `H` a value form (`Expr.ValFormIn`) over a part of the context whose live slots are persistent | `effHandleV`; the two-variable rule is now the theorem `CDerives.effHandle`, with its former statement | `handleV_compatC` (`Core/EffRules.lean`): `H`'s relation read off `wpTS` at its value (`wpTS_val_post`), then `ewp_handle` at clause values (`ewp_handle_vals`) |
| `[then]` at option A: the finaliser at `F 1` | `effThen` | `thenA_compatC`: `[sub]` to `F_{Σ^abort} 1`, then `then_compatC` |

- **Row polymorphism is the polymorphic let**, not a `∀` in Core's types. It adds no type former,
  so the relation, the machine and every Core lemma over `CTy` are unchanged. Terms carry no rows:
  each occurrence of the bound λ-value is typed at its own row.
- **Only closed λ-values are bound** (the value restriction). A λ-value is no pair and no primitive,
  so filling a variable with it makes and unmakes no handler frame (`okE_fill`); a closed pair
  could.
- **The checker** types a finaliser at `F 1` (`Frontend/Check/Steps.lean`, `Rules.lean`,
  `Checker.lean`; `Elab/Infer.lean`, `Sugar.lean`). Its finalisers are destructors, which were
  already pure.

**`J₁`** (`Instance/J1.lean`).
- **Definition.** `J1Der Θ Δ Γ e j`: the slot types and `j` are free of the row `∀`, or are
  polymorphic function types `U(∀ρ:k. C)` / `!U(∀ρ:k. C)` with `C` free of it and no returner
  (rank 1); and at every admissible `η` and every closing `σ` of the live polymorphic slots, Core
  types `fillS σ 0 e` (`J1Core`). A closing fills each such slot with a closed λ-value that Core
  types at every instance of the slot's type (`Closing`). A judgement at a polymorphic type is
  Core typing the λ-value at every instance.
- **Proved.** `j1_read : J₁.read = tier1` (Core's kernel); `coreClosed_J₁`; the let law
  (`letLaw_ourInst_J₁`: `[let-poly]` at a polymorphic type, `[let]` otherwise, through
  `fillS_scons_some`); S1 at every effect context (`subClosed_ourInst_J₁`,
  `rowAlgebra_ourInst_J₁`: Core's `[sub]` asks nothing of its rows).

**The interaction** (`I/J1.lean`), Core σ=[]:
- B1 (`fl_core_J₁`); B's guarantees but B5 (`guarantees_noB5_J₁`), and with B5 given `BumpSim`
  (`guarantees_J₁_of_bumpSim`); the pins (`pins_J₁`, abortive rows);
- FL at `J₁`'s open judgements over contexts with no polymorphic slot (`flOpen_J₁_mono`): a
  polymorphic type is read through `ojdgW` as the intersection of its instances (Law 1,
  `oretThunk_rFree`), each instance by `fundamentalC`;
- A's (S) properties but S5 and S6, at every effect context (`sPropsNoCancel_J₁`), through
  `CoreClosed`: `InstanceSafety` now proves S2, S3 and `LiveOK` (whence S0 and S4) at every typing
  system whose closed programs are Core's (`safety_of_coreClosed`, `effSafe_of_coreClosed`,
  `liveOK_of_coreClosed`), and keeps its `tier1Open` corollaries;
- **`I.Tier1 J₁` given what is open** (`tier1_J₁_of`): A's (E) properties, S5 and S6 at every
  admissible effect context, `Accepts`, `Rejects` and `BumpSim`.

**S6's route 8.4: probed, stopped** (`I/GhostCoupling.lean`). The probe asked for the coupling at a
single capture, a resume and a cancel. What fails, each machine-checked:
- **FL at BoLo does not give S6.** A closed program's relation at its pure type is `wpTS`
  (`cC_ret_eq`), where no protocol table and so no `contShare` occurs. R1 (a capture never used),
  R2 (a capture resumed twice) and R3 (a linear capture cancelled) run by head steps that allocate
  nothing to a value of `bool`, so each is in Core's relation at `F bool` (`semC_RProg`). `JRp`,
  which types them there and nothing else, has FL at BoLo (`fl_core_JRp`) and fails S6 at `ΞA` on
  each (`ghost_probe`, `ghost_probe_resume`, `ghost_probe_cancel`). Hence `¬ GhostCoupling`
  (`not_ghostCoupling`): whatever `contShare` carries, it changes no closed program's relation.
- **BoLo's world has no obligation along those runs.** Their heap stays empty, and BoLo's world at
  the empty heap is the empty resource (`lower_empty_eq`), so `NoOwn` holds at every configuration
  (`noOwn_of_lower_empty`).
- **What the route needs**: an `own`-like obligation that `ResU.Lower` does not lower to the heap,
  or `wpTS`'s run-end conditions read on a run's steps. Both change BoLo's definitions, so the S6
  part stops here. S6 at `J₁` is OPEN; route 8.2 (`CfgTyped`) is not built.

**Changed statements in the Targets.**
- `CDerivesNU`'s `effThen` and the pin `RC_effThen` take the finaliser at `F 1` (option A).
- Check 2's four derivations (`d_thenProgNU`, `d_prog₃TNU`, `d_thenRaiseProgNU`,
  `d_unwindProgNU`) are removed: their finalisers let a raise escape, which option A excludes. The
  programs stay.
- The inductions over `CDerives` gain the new cases: `insert_dead` (`Base/Support.lean`,
  `hndExpr_shift`, `valFormIn_insert`), `closedAt_of_derives` (`Base/Closed.lean`,
  `closedAt_of_fill`), `okE_of_derives` (`NoInterception.lean`, `okE_fill`); `Base/Fill.lean`
  holds `fill_shift` and `closedAt_of_fill`.

**Readings to confirm.**
1. **`J₁`'s kernel is Core's whole `CDerives`**, not the unr-free fragment this plan's §2 named.
   The new rules are in `CDerives`; `CDerivesNU` stays the fragment `tier1Open` reads. Our
   instance ties a derivation's conclusion to `Ξ` (D1), so at an admissible context its rows are
   unr-free (`rowNU_of_rowAt`). A derivation's inner judgements are not tied, and may use Core's
   unr rules.
2. **"A `∀` over rows or a polymorphic let"** is read as the polymorphic let, with the row `∀` of
   the open types read through it (rank 1, by closing substitution). `J₁` is defined by its
   closings, not as an inductive with `[allR-I]` and `[allR-E]` (§2's `J1Der`).
3. **"A general `[handle]` (clauses not restricted to variables)"** is read as §19's printed rule:
   the handler a value form over a persistent part of the context. A handler that is a computation
   is not admitted.
4. **D3's kernel half** is read as the finaliser at the pure row, in Core's `[then]`, in
   `CDerivesNU`'s and in the pin `RC_effThen`.

**Remaining.**
- **A's (E) properties at `J₁`**: the runs (E1–E10's `RunsTo`, `RunsForever`) and the eight
  schema lemmas. A schema's callback `λ_. M` puts `M`, typed at the empty context, under a live
  binder it does not use. Core's λ with a dead binder (`thunkF`) is at the pure returner only, and
  Core has no weakening by an unused live slot (a direct induction meets `bangThunkV`'s
  `Persistent` premise). Not derived; no obstruction verified.
- **`RowVarKernel J₁`**: not attempted. `[allR-I]` reads a value judgement at `U C` as Core
  typing the λ-value at `C`, an inversion of Core's thunk rules (cost not stated).
- **`FLOpen coreB J₁` at contexts with a polymorphic slot**: not proved. `ogDenW` relates such a
  slot to any value related at every instance, and `J₁` speaks of closed λ-values Core types.
- **S5** at `noFinRaise`: the bridges `noIntercept_of_core`, `unwindOrder_of_core`, and
  `FinRowsAt noFinRaise` for typed programs, now that `[then]` types a finaliser at the pure row.
- **S6**: route 8.4 stopped (above); route 8.2 not built.
- **`Accepts J₁.read .abortive`** (the composite's eight programs, each with a derivation in Core's
  kernel and one complete run) and **`Rejects J₁.read`** (inversions, cost to be stated).
- **`BumpSim`** (OQ-43); pieces 5 and 6.

**Unspent hypotheses.** `sPropsNoCancel_J₁` holds at every effect context, so `tier1_J₁_of` spends
`AdmEff` only through its open hypotheses. `letPoly`'s premise typing the λ-value (`hV`) is not
read by `letPoly_compatC`; `okE_of_derives` reads it (the λ-value's body passes `okE`). The probe
uses no determinism result (`det_ourInst`): each run is a chain of head steps.

**Untranscribed in the run-up.** The schema lemmas; the (E) runs at `J₁`; `RowVarKernel J₁`;
`noIntercept_of_core`, `unwindOrder_of_core`, `cancellation_of_core`; `CfgTyped` (route 8.2); the
composite's derivations in Core's kernel; `Rejects`' inversions over `CDerives`; `BumpSim`.

**Next.**
1. The schema lemmas at `J₁`: a weakening of Core's derivations by an unused live slot of a
   droppable type, or a dead-binder λ at an effectful returner (a Core rule, with a SPEC entry).
2. S5's bridges at `noFinRaise`.
3. S6 by a route that does not run through FL at BoLo: route 8.2's run-time typing, or the user's
   call on a resource kind for `κ` (a BoLo change, so the user's).
4. `Accepts`, `Rejects` at `J₁`; piece 5 (h2, h4) and piece 6 (`BumpSim`).

---

## Piece 5 run: the answering class

**What ran.** Piece 5 at `J₁` (D5), with D1–D4 and D6 applied: D1.h4 through the comodel, the
unary laws at our instance, and D1.h2. Every result is at Core σ=[]. `lake build Targets` passes
with AxiomCheck and Audit, and every new result's axioms are within
`[propext, Classical.choice, Quot.sound]`. Nothing in `Core/` changed, and no BoLo definition or
borrow guarantee was touched. Commits: `6e38745` (theories, the comodel reduction, global state,
the unary laws) and `3d861cb` (`I4Runs`, the Status rows for h2).

**Proved.**
- **Equations in signatures, D1.h4 (a)–(b)** (`A/Theories.lean`, which imports nothing of ours).
  - An equation is two straight-line computations over one label's operations and the same
    parameters, ending in the continuation (`VExpr`, `SLComp`, `Eqn`; `Theory`, OQ-22 (a)).
  - The answering handler is the state-passing handler of co-operations (`ansHnd`, `runAt`;
    decision 59).
  - `AnsCorrect` is Plotkin–Pretnar Def. 4.5 read at `RunsAlike`. `IsComodel` is Ahman–Bauer
    Def. 1 with equations, read through the co-operations' own runs (`coRun`).
  - Global state is the first theory: `stateSig`, `stateTheory` (get–get, get–put, put–put,
    put–get) and `stateCo`; `badStateCo` is the witness.
- **The comodel reduction, D1.h4 (c)** (`ansCorrect_of_comodel`, `Instance/Theories.lean`). It
  holds at every typing system with `LiveOK` whose typed closed values are closed: co-operations
  that run quietly (`PureCo`) and form a comodel give a correct handler. The route:
  - one clause step (`quiet_opStep`);
  - the handled side's fold over the computation (`quiet_fold`, the native counterpart of
    `handle_fold`);
  - the co-run's fold (`quiet_coFrom`).

  The two sides meet at one configuration, because their co-runs reach one state and one
  continuation argument.
- **Global state** (`state_isComodel`, `state_correct`; `I.state_correct_J₁` at every effect
  context, carrier and label). **Not vacuous** (`not_ansCorrect_badState`,
  `not_isComodel_badState`). The witness is at `J₁` and the admissible `Ξst` (`admEff_Ξst`). There
  the handler whose `put` keeps the old state fails the update–lookup law at a program Core's
  kernel types (`d_stProg`). Its co-operations are no comodel.
- **The unary laws at the answering class** (`Instance/UnaryLaws.lean`). A clause
  `λ(a, k). c a to b. k.resume b` whose code runs quietly runs in place (`quiet_tailClause`). So
  the tail-resumptive law and algebraicity hold there (`tailLaw_quiet`, `algLaw_quiet`; at `J₁`,
  `I.tailLaw_quiet_J₁`, `I.algLaw_quiet_J₁`).
- **Runs** (`Instance/Runs.lean`).
  - Quiet runs (`Quiet`: chains of head steps with no finaliser event) and their closure lemmas.
  - Quiet runs that meet run alike (`runsAlike_of_quiet`, through `runsAlike_of_join`).
  - β, `letpair`, `appE`, `resumeE`, the handler's hop and κ's resume, each as a quiet chain.
  - A complete run from a chain is the chain's path (`complete_chain_eq`, through `rstep_det`).

**Fails as written: `AlgLaw` at `J₁`** (`not_algLaw_J₁`, `not_algLaw_ΞA`; `status_unaryLaws`).
- **The witness.** `algFireProg` is typed by Core's kernel (`d_algFireProg`) at the admissible
  `ΞA`. An inner handler at an `unr` operation holds its persistent continuation in a finaliser
  frame, and its clause raises to an outer handler that aborts.
- **The failure.** Both sides answer `()`. Their traces show `fire D` at finalisers that differ as
  terms (`finE_DL_ne`): each `D` mentions the continuation its side captured. At a linear or affine
  operation, no finaliser at `F 1` holds the continuation.
- **The decision is the user's.** Either observe a finaliser's start without its code (D4 read at
  the trace's events), or restrict `unr` (decision 63). Under either, the law beyond the answering
  class is still OPEN.

**Open.**
- **`TailLaw` at our instance.** Not proved, not refuted. By `algFireProg`'s mechanism no witness
  types: an `unr` outer handler forces the tail clause's continuation context to be persistent,
  while our instance's `resume` forces only `U` slots. That is a reading of the rules, not a
  theorem.
- **`EtaHold`.** Not proved. `[handle]`'s `hnS` keeps a forwarding handler's own name out of its
  clauses' row, so by that reading no typed program installs `fwdH true l`. Not checked by an
  inversion.
- **D1.h2, `I4Typing` at `J₁`** (`i4Typing_J₁`). Not derived, and no obstruction is verified. It
  needs:
  - inversions of Core's typing at `bindE`, at `effHandleV` (`hndTerm`) and along `capPass`'s
    spine (`bind`, `effLet`, `unitE`, `tensorE`, `sumE`, and `effPerform` under `effSub`), taken
    through `ret`/`ofRet` and the `ν` rules, which apply at any term;
  - the clause typing read back to `co_j`'s type;
  - a typing of an `n`-free subterm at the row without `n`, an induction over `CDerives` (none
    found in Core);
  - `ansCall`'s typing through `withswap` at `Mut x S`;
  - then `I4a`'s conclusion at `J₁`.

  This plan's cost note (§5, Risk) names only the spine's inversions.
- **D1.h2, `I4Runs`.** STATED (`I/Interface.lean`), not proved. Its proof needs a simulation:
  `n`-free code runs under the handler frame on one side and under the lend's frames on the other,
  through continuations that outer handlers capture and resume. The borrow form's cell is placed at
  a location the other run never uses. Not built. A restriction to straight-line bodies
  (`handle_fold` against a fold of `ctlForm`) was not built either: it would cover no body that
  performs an operation an outer handler catches.
- **`ctlForm_fold`** (§5's `Base/Answering.lean`). Not built. The fold at native `hnd` is
  `quiet_fold`, for `ansHnd` at our instance's encodings. `ctlForm` is Base's term: its clauses
  are let-bound before the handler, and no lemma relates the two terms.

**Added hypotheses, and their scope.**
- **`PureCo co`** (`ansCorrect_of_comodel`). Each co-operation is closed, and at a closed state and
  argument it runs quietly to a pair of closed values. Co-operations that allocate or show events
  would make the two sides' memories or traces differ. `stateCo` meets it (`pureCo_stateCo`), and
  so does `badStateCo` (`pureCo_badStateCo`).
- **`hlen` and `hwf`** (the same theorem). `co` has at most `2³²` co-operations, and each
  equation names operations of `co` and values bound before it (`Eqn.WF`). `stateTheory` meets
  both (`stateTheory_wf`).
- **`LiveOK` and the closedness of typed closed values.** Both hold at `J₁` (`I.liveOK_J₁`,
  `closed_of_derV_J₁`).
- **`I4Runs`, beyond `I4Typing`'s hypotheses on the forms.** Data state, operations and body
  answer; `s₀` at a value judgement; a data answer of the program. Its docstring names the
  mechanism each excludes. None is checked by a witness.

**Readings to confirm.**
1. **`AnsCorrect` binds the continuation outermost** (`lets (vs ++ [k])`). The parameters sit at
   `j + p` under the results, and `k` is a closed value, as they are.
2. **`IsComodel` is read through the co-operations' own runs** of each side from each state: both
   sides reach one final state and one continuation argument. This is the run-level reading of
   Ahman–Bauer's equality of co-operation composites on the carrier.
3. **`Theory` is `Lab → List Eqn`.** `stateTheory T` gives the four laws at every label whose
   signature is `stateSig T`, decided classically.
4. **`I4Runs` compares the values reached** from the configuration, at a data answer of the
   program. That is this plan's "reach the same values … a data answer".
5. **`I4Typing`'s `s₀`.**
   - `I4Typing` carries no judgement of `s₀`.
   - The control form reads `s₀` in `bindE s₀ …`, at the row `S`.
   - The borrow form reads it under `alloc'`, through `lolliE`, at a value judgement. `I4a`
     carries that judgement.

   I have not derived `I4Typing` at an `s₀` typed only at an effectful row, and I have not
   verified that any obstruction is real. Whether `I4Typing` takes `I4a`'s premise is the user's
   call.

**Unspent hypotheses.** `AnsCorrect`'s and `IsComodel`'s typing premises (the state's and the
parameters' `derV`) are spent only for closedness (`hJV`); no type is read, and `state_isComodel`
holds at every carrier.

**Unused uniqueness and functionality results.** `det_ourInst` is not used. Every run here is a
chain of head steps that allocates nothing, which `rstep_det` reads.

**Untranscribed in the run-up.**
- `ctlForm_fold`.
- `i4Typing_J₁`'s inversions, the row strengthening at an `n`-free subterm, and `ansCall`'s
  typing.
- `I4Runs`'s two-context simulation.
- The inversions that would settle `TailLaw` and `EtaHold`.
- §5's reuse list, unread by this piece: the borrow form's run facts (`op_tail`, `op_answer`,
  `handle_fold`, `clauseRun`, `seqCalls`), which serve `I4Runs`; `ewp_handle`;
  `steps_plug_split`.

**Next.**
1. The user's call on `AlgLaw`'s observation (a finaliser's start without its code, or `unr`
   restricted), and on `I4Typing`'s `s₀`.
2. `I4Typing` at `J₁`: the inversions and the row strengthening, then `I4a` at `J₁`.
3. `I4Runs`: the two-context simulation.
4. `TailLaw` and `EtaHold`: the inversions that turn the readings into theorems, or the witnesses.
5. Piece 6 (`BumpSim`).

---

## Piece 6 run: the step-for-step simulation (OQ-43)

**What ran.** Piece 6 at Core's machine, with D1–D6 applied. Every result is a fact about Core's
machine (Core σ=[], read at no world). Nothing in `Core/` changed, and no BoLo definition or borrow
guarantee was touched. `lake build Targets` passes with AxiomCheck and Audit, and every new
result's axioms are within `[propext, Classical.choice, Quot.sound]`. Commit: `3870da8`.

**Proved** (`Targets/B/BumpSim.lean`).
- **B5 at every typing system and borrow world, from B4′** (`releasedOnceReuse_of_soundContracts`).
  So B5 holds at today's unr-free kernel (`releasedOnceReuse_tier1NU`), at `tier1Open`
  (`I.tier1Core_releasedOnceReuse`) and at `J₁` (`I.releasedOnceReuse_J₁`), at BoLo. With it
  **`B.Guarantees J₁.read B.coreB`** (`I.guarantees_J₁`) and `B.Guarantees tier1Open.read B.coreB`
  (`I.tier1Core_guarantees`). `I.tier1_J₁_of` and `I.tier1Core_of` no longer take `BumpSim`.
- **The step-for-step simulation at the configurations a bump run reaches** (`bumpSimAt`), and the
  bump run that follows a complete run (`bump_follows_at`, `bump_follows`'s proof over it).
  - Renaming along a function commutes with the term operations: `Kont.mapLoc`, `mapLoc_shift`,
    `mapLoc_subst`, `kont_mapLoc_plug`, `kont_mapLoc_shift`, `kappa_mapLoc` (the capture step's
    `κ` copies `K`), `clauseAt_mapLoc`, `cancelVal_mapLoc`, `errNext_mapLoc`, the host step
    (`host_call_mapLoc`: literals in, literals out), `countNext_mapLoc`, `countTryNext_mapLoc`,
    `boundedFixNext_mapLoc`; a renamed context has the handlers, catchers and names it had
    (`hasHnd_mapLoc`, `catches_mapLoc`, `hndNames_mapLoc`).
  - The array steps under a block renaming: `tabFill_mapLoc`, `dropFill_mapLoc`, `idxAns_mapLoc`,
    `splitAns_mapLoc` (`split`'s second part at the end location `ℓ + i`).
  - `head_image`: a head step that allocates nothing, renamed along a map injective on the live
    heap that moves the window `[ℓ, ℓ + 2³²)` above each location the redex mentions as a block, is
    a head step of the pushed memory. A renamed redex is a redex (`head_mapLoc_exists`), so Core's
    `plug_decomp` puts the given step at it (`step_at_image`), and `head_det` makes it the renamed
    step (`sim_det`).
  - The allocations: the bump step places its cell (`sim_alloc`) or block (`sim_tab`) above every
    name, every window and `X`, and the new map translates onto the given step's
    (`push_upd_fresh`, `push_fill_fresh`).
  - The platform's answers (`sim_plat`): a data argument and a data answer, which no renaming moves.
- **The protocol on every run** (`platData_of_safe`). The platform restricted to data arguments
  (`Platform.restrict`) keeps its protocol (`restrict_respects`). Where it does not get stuck, a
  stop of the platform's operation is at a data argument (`platData_of_safeAt`), and a run under
  the platform whose stops are at data arguments is a run under the restriction (`pstep_restrict`).
  B4′ quantifies over every platform that keeps its protocol, the restriction among them.

**`BumpSimAt` is `BumpSim` with four hypotheses added and one conclusion conjunct**, each
discharged where B5 applies it (`bump_follows_at`):
- `P.Respects`: B5 quantifies over the platforms that keep their protocol.
- `FinDom cB.μ`: every memory a run from `init` reaches is finite (`finDom_pstep`).
- `AffineAbove g cB.μ cB.e (k + 1)`, with `AffineAbove g' cB'.μ cB'.e k` added to the conclusion.
  `AffineAbove g μ e k`: `g` moves as a block the window `[ℓ, ℓ + (k + 1) · 2³²]` above every named
  location `ℓ`; a run with `k` steps to go keeps it at `k` (`bump_follows_at`). A step's array
  arithmetic adds less than `2³²` to a named location (`head_mentions`, `named_step`), so the
  windows narrow by `2³²` a step (`affineAbove_step`); the identity meets it at `init` at every `k`
  (`affineAbove_id`). It implies `BlocksAffine` (`blocksAffine_of_affineAbove`).
- `PlatData P cB`: the platform's stops are at data arguments (`platData_of_safe`).

None is vacuous: B5 is proved through them, for every typed program and every complete run.

**`BumpSim`, over every related configuration: not proved, and not used.** Its hypotheses carry
none of the invariants a bump run keeps. Checked in scratch, and not kept in the build: its
conclusion fails at two cells `5` and `6` holding `()`, related to themselves by their swap, at the
term `(λx. (5, x)) 2` (`Platform.none`, `X = ∅`). The β step forms the pair `(5, 2)`, which
`BlocksAffine` reads as an array value, and `g'` must agree with the swap at `5` and `6`, so
`g' 6 = 5 ≠ g' 5 + 1`. The configuration is outside what a bump run of `bump_follows_at` reaches:
the swap breaks `AffineAbove` at `5`. `FinDom` and `PlatData` rule out an infinite memory and a
platform answering an argument by its locations; I have not checked that `BumpSim` fails at either.

**Unspent hypotheses.** `BumpSimAt`'s `BlocksAffine g cB.μ cB.e` is not read (`AffineAbove`
implies it); it is kept because `BumpSim` states it. `P.Respects` is read through `typed` (the
platform's answer is data) and, for the restriction, `uniq` and `total`; `nz`, `lin` and `data`
are only passed on to the restriction. B4′'s `Terminates` is not read: B5 uses `SafeRuns` only.

**Unused uniqueness and functionality results.** `det_ourInst` and `AStep1.deterministic` are not
used; the given step is fixed by `plug_decomp` and `head_det` (allocations by `head_alloc_inv`,
`head_tab_inv`).

**Untranscribed in the run-up.** None that this piece needs. TwoRun's `head_rename`, `step_sim`
and `run_sim` (which do not build) were read as a guide; their renaming is rebuilt over
`Expr.mapLoc`, with the effect steps, the array steps under blocks and the platform's answers.

**Next.** What `I.Tier1 J₁` still needs, unchanged by this piece: A's (E) properties at `J₁`, S5's
bridges at `noFinRaise`, S6, `Accepts` and `Rejects`.


---

## Round 2 outcome

**Where tier 1 stands.** `I.Tier1 J₁` is not proved. It follows from five open conditions
(`I.tier1_J₁_of`): A's (E) properties at `J₁`, S5's bridges at `noFinRaise`, S6, `Accepts` and
`Rejects`. Round 2 applied the user's decisions of 2026-10-07 (D1–D6) and ran pieces 5 and 6.
**`B.Guarantees J₁.read B.coreB` is proved** (`I.guarantees_J₁`), as are S0–S4 and `LiveOK` at
every effect context. Every result is at Core σ=[]. No BoLo definition changed and no borrow
guarantee was weakened: `fundamentalC`, `adequacyC` and `adequacyD` keep their statements with the
new rules' cases. HEAD is `31bc8f3`, on `tier1-effects`, not pushed.

| step | status | verifier | commits |
|---|---|---|---|
| R1: D1–D4, D6 | LANDED. S1 (`rowNU_of_wf`, `rowAlgebra_ourInst_tier1Open`), S2, S3, `LiveOK` (`Inst.safety_ourInst_tier1Open`, `Inst.effSafe_ourInst_tier1Open`, `Inst.liveOK_tier1Open`), S0, S4, B2 at BoLo (`adequate_core`), B3/B4 (`sound_tier1NU`), `EffSafeDrive` (`effSafeDrive_tier1NU`); each new hypothesis shown needed (`safety_needs_tie`, `liveOK_needs_tie`, `adequateDrive_needs_nuOk`, `effSafeDrive_needs_nuOk`, `noIntercept_needs_finRow`, `subClosed_needs_wf`); the invalid S1 refutation removed; encoding defect (`i` and `i + 2³²` one operation) repaired by `opJunk` | pass | 134d83d |
| R2: D5, `J₁` by Core rules | LANDED, PARTIAL. SPEC §24: `CDerives.letPoly`, `CDerives.effHandleV`, `effThen` at `F 1`, with `fundamentalC` cases `letPoly_compatC`, `handleV_compatC`, `thenA_compatC`; `J₁` built (`j1_read`, `fl_core_J₁`, `rowAlgebra_ourInst_J₁`, `sPropsNoCancel_J₁`); `I.Tier1 J₁` reduced (`tier1_J₁_of`). S6 route 8.4 probed and stopped (`not_ghostCoupling`) | pass | d365b49, 828da25, 4ba8385, d5d2254 |
| R3: piece 5, h2/h4 and the unary laws | PARTIAL. h4 through the comodel (`ansCorrect_of_comodel`), global state (`state_isComodel`, `I.state_correct_J₁`, non-vacuity `not_ansCorrect_badState`), `TailLaw` and `AlgLaw` at the answering class (`tailLaw_quiet`, `algLaw_quiet`). `AlgLaw` fails at `J₁` as defined (`not_algLaw_J₁`; see the finding). `TailLaw`, `EtaHold`, `I4Typing`, `I4Runs` (stated) open | **fail: one major finding (open, below)** | 6e38745, 3d861cb, bdbea9d |
| R4: piece 6, `BumpSim` (OQ-43) | LANDED. `bumpSimAt` at the configurations a bump run reaches; B5 from B4′ at every typing system and world (`releasedOnceReuse_of_soundContracts`); `I.guarantees_J₁`; `tier1_J₁_of` and `tier1Core_of` no longer take `BumpSim`. `BumpSim` over every related configuration not proved and no longer used | pass | 3870da8, 31bc8f3 |

**Kernel changes** (effect side only; SPEC §24, Entry 23):
- **Polymorphic let** (`CDerives.letPoly`, `Core/PolyLet.lean`): binds a closed λ-value and
  substitutes it, so one function is used at several rows. Row polymorphism is this let, not a `∀`
  over rows in Core's types (reading 2 below).
- **`[handle]` at a value form** (`CDerives.effHandleV`, `Core/EffRules.lean`): the handler is a
  value form over the persistent part of the context. The old two-variable rule is now the theorem
  `CDerives.effHandle`, with its statement unchanged.
- **`[then]` at option A** (D3's kernel half): `effThen` types its finaliser at `F 1`, so a
  finaliser's raises are handled locally. Check 2's four derivations, whose finalisers let a raise
  escape, were removed.

The machine, the relation and the borrow rules are unchanged.

> **OPEN VERIFIER FINDING (major), R3.** `not_algLaw_J₁` and `not_algLaw_ΞA` hold of `J₁` as
> defined, but the witness `algFireProg` types its inner handler of operation 5 at
> `R5 = Row.ofEff 5 Eu 0 ++ Sx` with `Eu = [(.unr, unit, unit)]`, while `ΞA` declares 5 `lin`.
> So `R5` is not tied to `ΞA` (`¬ RowAt ΞA R5`; not yet a Lean fact). The failure rests on `J₁`'s
> inner judgements being untied to `Ξ` (R2's reading 1) and on an `unr` continuation held by a
> finaliser. Under D1 and D6 the witness probably does not type. Status.lean (the piece-5 bullet,
> the AlgLaw/TailLaw/EtaHold row, `status_unaryLaws`) and the piece-5 section above present it as a
> failure at an admissible context. Not yet done: state that dependence in those places, prove
> `¬ RowAt ΞA R5`, list tying `J₁`'s inner rows to `Ξ` as the D1-consistent repair next to the two
> offered (observe a finaliser's start without its code; restrict `unr`), and keep `AlgLaw` at the
> tied, unr-free class OPEN. Until then, do not cite `not_algLaw_J₁` as a failure at an admissible
> context.

**Gate.** `make gate` at `31bc8f3` passed ("ci-local: ALL PASSED"): build, compile scaling,
hygiene and axioms, axiom report, corpus parse and check (22 pending programs failing as
recorded), sugar pairs, typed IR, book doc-tests (82 passed, 1 ignored, 0 failed) and book build.
The source stage ran only on goldens not yet verified (`make gate-full` not run). Lean's
unused-tactic linter flags `skip` at `Core/Steps.lean:627` and `:644`. Outside the gate, 19
experiment libraries outside the default targets fail to build, none from these commits; two
touch them: Grades lacks the `letPoly` and `effHandleV` cases (it already lacked `countFold`,
`countTry` and `effThen`), and LoopBorrow's `decide +kernel` gets stuck evaluating the checker.

**Readings for the user to confirm.**
1. D4's no-interception condition is `FinRow FR` on every finaliser a cancel or unwind fires.
2. D4's "use" of `κ` is a step applying `κ` to a data value (`UseAt`).
3. D4's "observationally": `RunsAlike` at data answers; `EffSafeDrive` at a finished drive
   (`DoneDrive`).
4. D2 is carried as positivity (`CTy.NuOk`); distinct keys imply it at a platform answering the row.
5. `J₁`'s kernel is Core's whole `CDerives`, with its inner judgements not tied to `Ξ` (bears on the
   R3 finding).
6. Row polymorphism is the polymorphic let; "general `[handle]`" is a value-form handler over a
   persistent context.
7. `AnsCorrect` binds the continuation outermost; `IsComodel` is read through the co-operations'
   own runs; `Theory` is `Lab → List Eqn`; `I4Runs` compares reached values at a data answer.

**Decisions for the user.**
- `AlgLaw`: tie `J₁`'s inner rows to `Ξ` (pending the R3 finding), observe a finaliser's start
  without its code, or restrict `unr` (decision 63).
- S6: route 8.4 needs a BoLo change (a resource kind not lowered to the heap, or `wpTS` checking
  run-end conditions), which the user's rule excludes. Route 8.2 (`CfgTyped`) is the remaining
  kernel-free route; 8.3 is AGREE Q9.
- Whether `I4Typing` takes `I4a`'s premise on `s₀`.

**Remaining.**
- A's (E) properties at `J₁`: the runs and the eight schema lemmas. The callbacks `λ_. M` need
  weakening by an unused live slot or a λ with a dead binder at an effectful type; neither is
  derived, and no obstruction is verified.
- S5 at `noFinRaise`: `noIntercept_of_core`, `unwindOrder_of_core`, and `FinRowsAt`.
- S6 (above). `Accepts`, `Rejects` (needs inversions over `CDerives`).
- `TailLaw`, `EtaHold` (inversions), `I4Typing` at `J₁`, `I4Runs` (a two-context simulation),
  `ctlForm_fold`.
- `RowVarKernel J₁`, `FLOpen` at polymorphic slots, `EffSafeDriveOfFL` at a generic world.

**Unspent hypotheses.** `AdmEff` is used by no proved S property beyond S1's `Ξ.NU`; `letPoly`'s
`hV` is read only by `okE_of_derives`; `BumpSimAt`'s `BlocksAffine` is never read; of
`P.Respects`, `nz`, `lin` and `data` are only passed on; B4′'s `Terminates` is not read; the typing
premises of `AnsCorrect` and `IsComodel` give only closedness.

**Unused uniqueness/functionality results.** `det_ourInst` (in R2's probe, R3 and R4) and
`AStep1.deterministic`.

**Untranscribed in the run-up.** The schema lemmas and the (E) runs; `RowVarKernel J₁`;
`noIntercept_of_core`, `unwindOrder_of_core`, `cancellation_of_core`; `CfgTyped`; the composite
programs' derivations; the `CDerives` inversions `Rejects`, `TailLaw`, `EtaHold` and `I4Typing`
need; the row strengthening for `n`-free subterms; `I4Runs`'s simulation and the borrow form's run
facts (`op_tail`, `op_answer`, `handle_fold`, `clauseRun`, `seqCalls`); `ctlForm_fold`.

**Next.**
1. Resolve the R3 finding (`¬ RowAt ΞA R5`; correct Status and the piece-5 section).
2. A's (E) properties at `J₁`.
3. S5's bridges at `noFinRaise`.
4. `Accepts` and `Rejects`.
5. The user's call on S6 and `AlgLaw`.

## Round 3: the capture cell (decision S6)

**Where tier 1 stands.** `I.Tier1 J₁` **fails as written** since the capture cell
(`I.not_tier1_J₁`): its A conjunct asks S4 at every admissible effect context, and S4's catch law
fails at `ΞA` (`Inst.not_handlerSem_J₁_ΞA`). S6 at `J₁` is reduced to two ownership properties of
the cell. No BoLo definition changed and no borrow guarantee was weakened: `fundamentalC`,
`adequacyC` and `adequacyD` keep their statements. Every result is at Core σ=[]. On
`tier1-effects`, not pushed.

| step | status | commits |
|---|---|---|
| the machine and Core (SPEC §25, Entry 24) | LANDED. A handler value carries its operations' tags (`hndVal`, `capTag`); `[op]` hands `kappaAt`: at a linear or affine operation `κ` with a unit cell allocated by the ordinary allocator (`kappaCell`, `kappaC`), freed by the resume and by an affine cancel; a linear `κ`'s cancel branch has no step. Core's effect lemmas re-proved (`ewp_kappaCell`, `ewp_kappaC_resume`, `ewp_kappaC_cancel`, `ewp_handle` with the tags' hypothesis, `handleV_compatC`); kernel and corpus counts unchanged (`zeroCell`) | 96562bc |
| the A level at the cell | LANDED. S6 per capture event (`ContUseEv`, `CatchEvAt`, `caughtEv`) in `SProps`; its tooth R1 (`not_contUseEv_of_der_R1`, `teeth_JR_ΞA`); route 8.4's obligation in Core's relation (`I.not_semC_R1`); runs around one cell (`CellQuiet`, `Calm`, `runsAlike_of_calm`, `finDom_reach`), so the answering-class laws and D1.h4 hold at every operation (`calm_tailClause`, `calm_opStep`, `calm_fold`) | fa225d5 |
| S6 at `J₁` | REDUCED (`I.contUseEv_J₁_of`): a capture event allocates `κ`'s cell (`catchEv_cell`); a use releases it three steps later, a linear `κ`'s cancel reaching a branch with no step (`use_frees_cell`); complete runs end at the empty memory (`I.leakFreeAt_J₁`); S6 follows from these and `OnlyOwnerFrees` and `NoDanglingUse` (`contUseEv_of_cells`), both OPEN | 68e0d04 |
| S4 at the cell | **FAILS AS WRITTEN at `J₁`** (`not_handlerSem_J₁_ΞA`): at `ΞA`, Core's handled program at the linear `tick` reaches the catch, from which the store-keeping steps reach only the catch and the clause at `κ` before its cell, while the clause at `capture l H K` runs, keeping the store, through terms naming neither `perform` nor `alloc`. Proved where every resuming operation is unrestricted (`handlerSem_orow`, `CatchUnr`) | 68e0d04 |

**The two open properties** (`Targets/I/ContUseJ1.lean`), on every complete run of a typed program
at a data answer under a runner that keeps its protocol and answers the row:
- `OnlyOwnerFrees`: the first release of a capture event's cell after its allocation is three
  steps after a use of the event's `κ`. Route: a run invariant — until `κ` is applied, its cell's
  location occurs only inside copies of `κ` — kept by every head step (substitution copies `κ`
  whole; `κ` is closed), with host answers, runner answers and array arithmetic naming no such
  location. Not built.
- `NoDanglingUse`: a use of `κ` comes after a capture event that handed `κ`, with no release of its
  location since. Route: B5's simulation (`releasedOnceReuse_of_soundContracts`) runs every complete
  run as the image of a bump run, where a use after the release frees a location the memory does
  not hold and has no step; the transfer needs the maps to agree on `κ`'s locations between its
  hand-off and its use. `BumpSimAt`'s construction keeps the maps on named locations;
  `ReleasedOnceReuse`'s statement does not expose it. Not built.

**Findings.**
1. S4's catch law, read at `capture` and store-keeping, fails as written at `J₁` at `ΞA`
   (machine-checked, above); so `Tier1 J₁` (machine-checked). The restatement is the user's: S6's
   reading per capture event is one candidate (the catch, the allocation, the hand-off).
2. The answering-class laws and D1.h4's comodel reduction needed runs that are quiet only around a
   cell; with finite memories on every run they hold at linear and affine operations as before.
3. `ContUse` (S6 read at `capture`) is kept as the earlier reading; it is not refuted here.
4. S5's statements read `capture` and `cancelOf`; they are not checked here against the cell.

**Readings for the user to confirm** (pending):
1. `J₁`'s kernel is Core's whole `CDerives`.
2. Row polymorphism is the polymorphic let; the general `[handle]` is the handler value form over a
   persistent context.
3. D4's readings: the no-interception condition is `FinRow FR`; a use of `κ` is a step applying
   `κ` to a data value; "observationally" is `RunsAlike` at data answers and `EffSafeDrive` at a
   finished drive.
4. Decision S6's reading: a capture event is a catch of a resuming operation, its `κ` the value the
   clause is first handed after it (`CatchEvAt`); counts are per `κ` value, on complete runs from a
   typed program at a data answer.

**Unspent hypotheses.** `AdmEff`'s `ClosedLife` and `Rich` are not read by S6's reduction (its
`NU` is, through `catchEv_cell`); `ContUseEv`'s `DataTy A` is read only through leak freedom; the
runner's `Respects` only gives `Live`.

**Unused uniqueness/functionality results.** `AStep1.deterministic`; B5's step maps (`RelAt`),
which `NoDanglingUse`'s route reads.

**Untranscribed in the run-up.** The sealing invariant of a capture cell's location; the coherence
of B5's maps on a `κ`'s locations from hand-off to use; S2's teeth R2–R4 at the cell (their runs are
not written out); S4's restatement.

**Remaining.**
- S4's restatement (the user's), then its proof at `J₁`.
- `OnlyOwnerFrees` and `NoDanglingUse` at `J₁` (routes above).
- A's (E) properties at `J₁`; S5's bridges at `noFinRaise`; `Accepts` and `Rejects`; the earlier
  round's open items.

## Round 3, step T2: `J₁`'s inner rows tied (decision R)

**Where tier 1 stands.** Unchanged in kind: `I.Tier1 J₁` **fails as written** through S4's catch
law at `ΞA` (`I.not_tier1_J₁`, re-established at the tied `J₁`). Decision R is applied: our
instance reads `J₁` at an effect context with the rows of its handlers and operations tied to the
context, as D1 ties a program's row. The open verifier finding on `not_algLaw_J₁` is settled, both
ways the decision named: the round-2 witness is outside the tied kernel (machine-checked, down to
an inversion of the tied kernel), and algebraicity still **fails as written at the tied `J₁`**, at
`ΞA`, by a witness at the affine `wait`. Nothing in `Core/` changed, no BoLo definition changed, and
no borrow guarantee was weakened: `J₁.read` (what B and the pins read) is Core's whole kernel, as
before. Every result is at Core σ=[]. On `tier1-effects`, not pushed.

| step | status | commits |
|---|---|---|
| R: the tie | LANDED. `CDerivesAt Ξ` (`Instance/TiedKernel.lean`): Core's `CDerives` with `RowAt Ξ` at `[perform]`, `[raise]` and `[handle]`; a tied derivation is Core's (`toCDerives`). `OurTyping.derAt`, the judgement at an effect context, read by `ourInst`; `J₁`'s is `J1DerAt` (`Instance/J1.lean`), every other typing system's is its `der`. Re-established at the tied `J₁`, every statement unchanged: the let law, S1, S0, S2, S3, `LiveOK`, S4 where resuming operations are unrestricted, leak freedom, S6's reduction, global state's model, the answering-class laws, the failures of S4 and of the bad state | 612dd94 |
| R: the finding | SETTLED. The round-2 witness `algFireProg`: `¬ RowAt ΞA R5` (`not_rowAt_R5`); no tied handler of `5` carries `unr` (`not_tied_hnd5_unr`); the tied `J₁` at `ΞA` types it at no type (`not_der_algFireProg_J₁`). Algebraicity FAILS AS WRITTEN at the tied `J₁` (`not_algLaw_J₁`, `not_algLaw_ΞA`), by `algAffProg` | 612dd94 |

**Gate.** `lake build Targets` passes with AxiomCheck and Audit; every new result's axioms are within
`[propext, Classical.choice, Quot.sound]`. `make gate` passed once, at 612dd94's tree ("ci-local
--source: ALL PASSED"); it builds the library, which this step does not touch.

**The tie** (`Targets/Instance/TiedKernel.lean`, `Targets/Instance/J1.lean`).
- **Which rows.** The decision names handlers' and operations' rows: `RowAt Ξ` at `[perform]` and
  `[raise]` (the row the operation is found in) and at `[handle]` (the handled row `(n)↑E ⊙ Σ`).
  These are the rules that read an operation's signature off a row. `[sub]`, `[let]`, `[then]` and
  the borrow constants' rows are Core's, untied.
- **At a handler** the tie makes `E` a prefix of `Ξ n` (`sig_prefix_of_rowAt`), so the handler
  value's tags (SPEC §25) are a prefix of `Ξ`'s qualifiers of `n` (`hndTags_of_rowAt`).
- **`J₁` at `Ξ`** (`J1DerAt`): `J1Der` with Core's kernel read as `CDerivesAt Ξ`, at the row
  environments tied to `Ξ` (`EnvAt`, as D1 reads a program's row: a polymorphic function performing
  at `[op] ⊙ ρ` is typed only where `ρ` is tied), its polymorphic slots closed by λ-values typed at
  their instances at tied rows (`ClosingAt`, `PolyInstAt`). `ourInst orowRF Ξ J₁` is, by definition,
  `ourInst orowRF Ξ (OurTyping.ofDer (J1DerAt Ξ))` (`ourInst_J₁`), so InstanceSafety's results apply
  through `coreClosed_J₁At`.
- **`OurTyping`** gains `derAt : EffCtx → …`, the judgement at an effect context. `ourInst` reads it
  where it read `der`; `J.read`, `RowVarKernel`, `FLOpen` still read `der`. `ElabClosed` (piece 2's
  route) is restated over `derAt` at every context, since its consumer reads our instance.
- **Where the tie lives.** `CDerivesAt` is a Targets-side copy of Core's judgement, as `CDerivesNU`
  is, with `toCDerives` its map into Core. Putting the tie into Core's `CDerives` (a row predicate
  as a parameter) is the other way; it would reach every Core proof, and was not taken.
- **Inversions of the tied kernel** (each one induction, `cdat_terms`): `derAt_hnd` (`[handle]` is the
  only rule concluding a handler term; its tags are a prefix of `Ξ`'s and its body is typed),
  `derAt_let` (a `let` types its body, or its body with the λ-value in place at `[let-poly]`, or the
  λ-value itself at a call-by-value application), `derAt_lam` (a λ-value whose body is an
  application types the body; no term constant is such a λ-value). `derAt_withH` reads a `withH`
  through them. Cost: about 130 lines, with the term simp set (`cdat_terms`, `cdnu_terms` with the
  handler at a value form).

**The finding, settled** (`Targets/Instance/UnaryLaws.lean`, `status_unaryLaws`).
- **The round-2 witness is outside the tied kernel.** `algFireProg` handles `5` at `[unr]` where
  `ΞA` declares `tick` linear: `not_rowAt_R5`, `not_tied_hnd5_unr`, and
  `not_der_algFireProg_J₁ : ∀ C, ¬ (ourInst orowRF ΞA J₁).der [] algFireProg C`. Its refutation
  measured `J₁` before decision R and is not kept (Status, "Retired and restated").
- **Algebraicity fails as written at the tied `J₁`** (`not_algLaw_J₁`, at every context declaring
  `exn` at `1` and `wait` at `2`; `not_algLaw_ΞA`). The witness `algAffProg` is typed with every
  handler's and operation's row tied (`d_algAffProg`):
  `handle_exn (handle_wait algL2 with holdCancelCl) with (λ_. ())`, where
  `holdCancelCl = λ(a, k). raise exn then y. k.resume y unwind (handle_exn (k.cancel) with λ_. ())`.
  The clause's `then` branch resumes the affine `κ`, the finaliser cancels it; the finaliser is at
  `F 1` because it handles the cancel's `exn` itself (option A admits it). Both sides answer `()`;
  each run allocates `κ`'s cell, fires the finaliser, which mentions the side's `κ`, releases the
  cell and ends. Every complete run of the right side fires a finaliser holding the frame
  `□ to x. (ret x to y. ret ())` and the left's does not, at every pair of cells (`finE_D2_ne`).
- **What this says about the repairs.** Tying rows does not exclude it, and at an admissible context
  no tied row has a resuming `unr` operation (`rowNU_of_rowAt`), so restricting `unr` does not
  either. The round-2 docstring's "at a linear or affine continuation no finaliser at `F 1` can hold
  it" was not machine-checked and does not hold of affine continuations: a finaliser can use `κ` by
  its cancel branch when it handles the cancel's row (`d_holdD`). The repairs left are the user's: observe a
  finaliser's start without its code (D4 read at the trace's events), or keep continuations out of
  finalisers (a premise on `[then]`'s finaliser context).
- **Runs with events** (`Targets/Instance/CellRuns.lean`): the complete runs from an allocation are,
  at some free location, the allocation there and what follows (`obsFrom_alloc_ex_iff`); along a
  chain of head steps, the chain's observable events and what follows its end
  (`obsFrom_chain_obs_iff`, `obsFrom_head_iff`). The location the allocation picks appears in the
  finaliser's code, so the refutation is read at every location, not through `obsFrom_alloc_iff`'s
  location-free form.

**Findings.**
1. Algebraicity fails as written at the tied, unr-free class (above); the restatement is the user's.
2. `TailLaw`: the round-2 note that no witness types by the `unr` mechanism does not extend to the
   affine one. Whether a `TailLaw` witness types through a finaliser that uses its `κ` is not
   checked. Status records `TailLaw` as OPEN, not proved and not refuted.
3. A tied handler's signature is a prefix of `Ξ n`, not necessarily all of it. A's `handle` encodes
   the handler frame with `Ξ`'s whole tags (`qsOf`), so a typed program's handler of a proper prefix
   is not an A-level handler frame: S4's catch law and S6's capture events (`CatchEvAt`) do not read
   its catches. Whether the tie should ask a handler's signature to be all of `Ξ n` is a reading for
   the user (below).

**Readings for the user to confirm** (pending; the user has not objected to 1–3):
1. `J₁`'s kernel is Core's whole `CDerives`: `J₁.read`, which B and the pins read. At an effect
   context our instance reads `CDerivesAt Ξ` (decision R).
2. Row polymorphism is the polymorphic let; the general `[handle]` is the handler value form over a
   persistent context.
3. D4: the no-interception condition is `FinRow FR`; a use of `κ` is a step applying `κ` to a data
   value (`UseAt`); "observationally" is `RunsAlike` at data answers.
4. Decision R's scope: the tie at `[perform]`, `[raise]` and `[handle]`; row environments and
   polymorphic instances read at tied rows; `[sub]`, `[let]`, `[then]` and the borrow constants'
   rows untied.
5. A tied handler's signature is a prefix of `Ξ n` (finding 3).
6. Decision S6's reading (round 3): a capture event is a catch at an A-level handler frame.

**Unspent hypotheses.** The tie is read by no positive result: S0–S3, the let law, S1, leak freedom,
S6's reduction and the comodel results hold at the untied kernel too, and reach the tied one through
`toCDerives`. It is read only by the exclusion (`not_tied_hnd5_unr`, `not_derAt_algFireProg`).
`not_algLaw_J₁`'s `h1 : Ξ 1 = Eab` is read only by the witness's typing.

**Unused uniqueness/functionality results.** `det_ourInst`, `AStep1.deterministic`; the runs read
`rstep_det` (through `obsFrom_head_iff`) and `rstep_alloc_inv`.

**Untranscribed in the run-up.** `TailLaw` checked against the finaliser mechanism; `EtaHold`'s
inversion (the tied kernel's inversions are its pattern); `I4Typing`'s inversions (`derAt_hnd` gives
the handled body's typing); S4's and now algebraicity's restatements.

**Remaining.**
- The user's restatements: S4's capture laws; algebraicity's observation of finalisers (or a premise
  keeping continuations out of finalisers); whether a tied handler declares all of `Ξ n`.
- `OnlyOwnerFrees` and `NoDanglingUse` at `J₁`; `TailLaw`, `EtaHold`.
- A's (E) properties at `J₁` (their programs typed by `CDerivesAt Ξ` at a rich context); S5's bridges
  at `noFinRaise`; `Accepts` and `Rejects`.

## Round 3, step T3: A's (E) properties at `J₁` (decision E)

**Where tier 1 stands.** Unchanged in kind: `I.Tier1 J₁` **fails as written** through S4's catch
law at `ΞA` (`I.not_tier1_J₁`). Its (E) conjunct also **fails as written**: `EProps` fails at `J₁`
at every effect context (`not_eProps_J₁`), through E7, E8 and E9 at option A. Decision E is
applied: the callbacks `λ_. M` are typed by a new Core rule, SPEC §26's `[λ-dead]`. No BoLo
definition changed and no borrow guarantee was weakened: `fundamentalC`, `adequacyC` and
`adequacyD` keep their statements, with `[λ-dead]`'s case (`lamDead_compatC`). Every result is at
Core σ=[]. On `tier1-effects`, not pushed.

| step | status | commits |
|---|---|---|
| the callbacks (SPEC §26, Entry 25) | LANDED. `CDerives.lamDead`: `Δ; x̸, Γ ⊢ M : F_Σ B ⟹ Δ; Γ ⊢ λx. M : 1 ⊸ F_Σ B`, the binder's slot dead; `fundamentalC`'s case `lamDead_compatC` (from `lam_compatC`, the unit binder's slot read dead, `gDenC_unit_dead`); `Weaken`'s case; the tied kernel's copy (`CDerivesAt.lamDead`) and its maps. At our instance a callback is `d_cbDead`. Weakening by an unused live slot is not derived | f2c98d6 |
| E1, E7, E8, E9 | E1 PROVED at every admissible effect context (`noColouring_J₁`). E7, E8, E9 FAIL AS WRITTEN at every effect context (`not_cancelPolicy_J₁`, `not_unwindPolicy_J₁`, `not_storedK_J₁`), so `EProps` (`not_eProps_J₁`) | 1361bb5 |
| E4, E5, E6 | E4, E6 PROVED at every admissible effect context (`deepHandler_J₁`, `tunnel_J₁`); E5 PROVED at every admissible one with no `unr` `exn` signature (`nestedHandlers_J₁`) | 8befb94 |
| E2 | E2d PROVED at every admissible effect context with no `unr` operation, at every label list (`e2d_J₁`, `higherOrderPoly_e2d_J₁`); E2a, E2b, E2c NOT DERIVED | e968072 |
| E10 | `timeout` typed once, its schema and its call PROVED (`derV_timeoutR_J₁`, `polyUseOpen_timeoutR_J₁`, `callsThrough_timeoutR`); `retry` and the loop NOT DERIVED | 50a93ce |
| E3 | NOT DERIVED; runs not attempted | — |

**Per property** (`Targets/Instance/E*.lean`; `status_eProps_J₁`).
- **E1** (`noColouring_J₁`): `hof` typed once at `U(∀ρ:any. U(1 ⊸ F_ρ bool) ⊸ F_ρ bool)`
  (`derV_hof_J₁`); its schema (`polyUse_hof_J₁`: the callback is `[λ-dead]`'s, `hof`'s closing read
  at the instance of the use's row, `der_callPoly_J₁`); it calls its callback catching nothing
  (`callsThrough_hof`); E1's and E1′'s programs typed (`der_threeUses_J₁`, `der_usesS_J₁`) and run
  to their answers showing nothing (`runsTo_noColour`, `runsTo_noColourS`), E1′ around the affine
  `wait`'s capture cell, released when the closure the handler answered resumes `κ`.
- **E2**: `sumGen` typed once at `U(∀ρ:any. U(1 ⊸ F_{yield ⊙ ρ} 1) ⊸ F_ρ bool)`
  (`derV_sumGen_J₁`), its handler at each instance at the first matches of the row without `yield`
  (`Row.firsts`, `Row.dropName`); its schema at every `yield ⊙ ε`, `ε` without `yield`
  (`polyUseOpen_sumGen_J₁`); E2d's body typed (`der_body2d_J₁`) and run to `(tt, inr ())`
  (`runsTo_prog2d`): three catches around their cells, the second inside the first's clause, the
  raise passing `sumGen`'s reinstalled handler. `twice`, `compose` and `retryP` are not derived
  (finding 2).
- **E3**: not derived (finding 4).
- **E4** (`deepHandler_J₁`): `deepGen` typed at `tick`'s row (`der_deepGen_J₁`; the clause
  `tick (); resume k ()` is a `[let]` at a row of one linear operation, `d_tickingCl`); its run
  answers `()` showing two ticks (`runsTo_deepGen`): each yield is caught around `κ`'s cell, the
  runner answers the clause's `tick` (`obsFrom_io_iff`), and the resume releases the cell and
  reinstalls the handler (`obsFrom_dgCatch`).
- **E5** (`nestedHandlers_J₁`): `withLog`, a state-passing handler of the linear `log`, typed and
  run outside `toResult` (to `(inr (), tt)`) and inside it (to `inr ()`): the raise passes
  `withLog`'s reinstalled handler, which the unwind drops with its state (`calm_p1`, `calm_p2`).
- **E6** (`tunnel_J₁`): `fwrap` typed once, its handler at the row without `exnᵢ` (`d_fwrap`,
  `Row.dropName`); its schema at every row without `exnᵢ` (`polyUseLacks_fwrap_J₁`); it calls its
  callback under its own handler only (`callsThrough_fwrap`); `tunnel`'s raise of `exnₒ` passes it
  and is caught outside (`runsTo_tunnel`).
- **E7, E8, E9**: fail as written (finding 1).
- **E10**: `timeout` above; `retry` (finding 2) and the loop (finding 4) are not derived.

**Run tools added** (`Targets/Instance/ERuns.lean`): a platform operation the context does not
catch, answered by the runner, shows its event and continues from the answer (`obsFrom_io_iff`);
a program runs to `v` showing `tr` when its complete runs are exactly those (`runsTo_of_obsFrom`).

**Findings.**
1. **`EProps` fails as written at `J₁`** (machine-checked, at every effect context): E7, E8 and E9
   each ask for a typing of a program whose finaliser raises to its context (E7b, E8b, E9c), and
   `[then]` types a finaliser at `F 1` (option A, D3); no derivation types them (`not_der_e7b_J₁`, `not_der_e8b_J₁`,
   `not_der_e9c_J₁`, by the inversions `derAt_then`, `derAt_raise`, `derAt_hnd`). So the (E)
   hypothesis of `I.tier1_J₁_of` cannot be met at `J₁`. The restatement (E7–E9's programs, or
   option A) is the user's.
2. **Core forces a `U C` slot only.** `twice` (E2a) uses its argument twice, so its slot is at
   `!U C`; `compose` (E2b) holds `g₂` across `g₁ () to _.`, a `[let]` at the callbacks' row whose
   continuation's context must drop at a row with a non-linear operation (`Row.Weak → Ctx.Drops`),
   so `g₂` is at `!U C`; `retryP` (E2c) and `retry` (E10) call a function from a handler's clause,
   whose context is persistent (`[handle]` at a value form). Each then forces that function, and
   `CDerivesAt.force` reads a slot at `U C`; no rule forces a `!U C` slot (`bangE` derelicts an
   expression, and `force` takes a slot). Not derived; no obstruction verified. Options, for the
   user: a Core rule forcing a `!U C` slot (dereliction at `force`; its `fundamentalC` case from
   `bangE`'s and `force`'s), or the instance writing `force` of a variable as a derelicting `let`
   (every program's encoding changes), or restated programs.
3. **`[let]` at a row with an `unr` operation asks a persistent continuation context, abortive
   operations included.** `withLog`'s clause (E5, `toResult` outside) and `sumGen`'s clause (E2d)
   hold a `bool` across the resume; `bool` is not `!`, so their `[let]` needs a row with no `unr`
   operation. `AdmEff` admits `unr` at abortive operations (`Ξ.NU`), so E5 is proved where no `exn`
   signature is `unr` (`NoUnrExn`) and E2d where no operation is (`NoUnr`); `ΞA` meets both
   (`status_noUnr_ΞA`). Whether the two typings fail at an `unr` `exn` label is not derived, and no
   obstruction is verified. Options, for the user: restrict `unr` at abortive operations (decision
   63; the standing "on friction, restrict or remove `unr`"), or read `[let]`'s side condition at
   resuming `unr` operations only, with its `fundamentalC` case.
4. **`unfold`'s value is not typed.** Our instance writes `unfold f g s` as the stepped codata value
   `etaN C ⟨f, g⟩ s` (`unfoldE`), whose code applies Core's recursive handle `selfNu` (the
   self-application `selfV`, `Core/Fix.lean`). The tied kernel types coiteration only as the
   constant `unfold_C` (`[unfold]`) and a `&`-computation only in `⟨M, N⟩`'s form (`withI`); no rule
   concludes a type for `etaN`. §4 above records that `unfold`'s unrolled states need a rule of
   their own. So E3's typings and E10's loop are not derived; no obstruction verified. Options, for
   the user: a Core rule typing `etaN C g s` at `U(νX. C)` (its semantic case from
   `unfold_compatX`), or the instance writing `unfold f g s` as `⟨π₁ (unfold_C c s), π₂ (unfold_C c
   s)⟩` (typed by `withI`, the projections and `[unfold]`; the machine's loop lemmas change). E3's
   runs (`RunsForever` at a driven loop) need tools not built here.

**Readings for the user to confirm** (pending):
1. `J₁`'s kernel is Core's whole `CDerives` (`J₁.read`), read at an effect context as the tied
   kernel `CDerivesAt Ξ` (decision R).
2. Row polymorphism is the polymorphic let; the general `[handle]` is the handler value form over a
   persistent context.
3. D4: the no-interception condition is `FinRow FR`; a use of `κ` is a step applying `κ` to a data
   value (`UseAt`); "observationally" is `RunsAlike` at data answers and `EffSafeDrive` at a
   finished drive.
4. Decision E's "a dead binder at an effectful type" is `[λ-dead]` at `1 ⊸ F_Σ B` (SPEC §26).
5. An (E) property holds at an effect context when it holds at every label list with the stated
   signatures (`ForLabels`); at our instance an abortive signature reads `aff` and `unr` alike
   (`clsOf`), so an `unr` `exn` label is one of E5's labels (finding 3).

**Unspent hypotheses.** `AdmEff`'s `ClosedLife` is read by no (E) result; its `Rich` only gives the
labels; `Ξ.NU` is read through the closings' instances (`der_callPoly_J₁`) and `yield`'s signature
(`sig_aff_iff`). `NoUnr` is read only by `derV_sumGen_J₁`, `NoUnrExn` only by E5's second program.

**Unused uniqueness/functionality results.** `det_ourInst`, `AStep1.deterministic`. The runs read
`rstep_det` (through `obsFrom_mstep_iff`), `rstep_alloc_inv` (`obsFrom_alloc_iff`) and the runner's
step's uniqueness (`obsFrom_io_iff`, by `perform_cases`, `plug_perform_inj`, `opPayload_inj`).

**Untranscribed in the run-up.** A rule or encoding for forcing a `!U C` slot (finding 2); a typing
of `unfold`'s value (finding 4); `RunsForever`'s tools at a driven loop; inversions of the tied kernel
at `force` and at `etaN` that would machine-check findings 2 and 4; `RowVarKernel J₁`.

**Gate.** `lake build Targets` passes with AxiomCheck (every new result's axioms within `[propext,
Classical.choice, Quot.sound]`, `#print axioms` for each) and Audit. `make gate` passed once
("ci-local --source: ALL PASSED"), on the library as this step leaves it (SPEC §26's rule).

**Remaining.**
- The user's calls: E7–E9 (finding 1); forcing a `!U C` slot (finding 2), then E2a–E2c and E10's
  `retry`; `unr` at abortive operations (finding 3); `unfold`'s value (finding 4), then E3 and E10's
  loop, with `RunsForever`'s tools.
- From earlier rounds: S4's restatement; S5's bridges at `noFinRaise`; `OnlyOwnerFrees`,
  `NoDanglingUse`; `TailLaw`, `EtaHold`; `Accepts`, `Rejects`; `RowVarKernel J₁`.

## Round 3, step T4: S5's bridges (decision S5)

**Where tier 1 stands.** Unchanged in kind: `I.Tier1 J₁` **fails as written** through S4's catch
law at `ΞA` (`I.not_tier1_J₁`). Its S5 hypothesis also **fails as written**: S5
(`Cancellation noFinRaise`) fails at `J₁` and at today's kernel, at every effect context declaring
`exn : 1 ↠ 0` at the name `1`, the admissible `ΞA` among them (`I.not_cancellation_admissible`,
`status_cancellation_J₁`). The cause is in A's trace definitions, not in our machine: a trace stops
only at `[]`, and its `fire` constructor reads the administrative steps after a fire step whole.
Read prefix-closed (a candidate restatement, `A.CancellationPfx`), S5's unwind is PROVED at `J₁` and
at today's kernel at every effect context, and its no-interception is PROVED given `CancelsStd`, an
added hypothesis that is OPEN at `J₁`. Nothing in `Core/`, BoLo or SPEC changed, and no borrow
guarantee was weakened. Every result is at Core σ=[]. On `tier1-effects`, not pushed.

| step | status | commits |
|---|---|---|
| a closed program runs from every finite memory (B) | LANDED: `ownWorld`, `runs_of_rel`, `runs_of_rel_unit` | 826b968 |
| S5's traces at our machine (the Instance) | LANDED: `unwind_pfx`, `cancel_pfx` (every path is a trace once at most one step of the run is appended); the bridges `unwindOrderPfx_of_core`, `noInterceptPfx_of_core`, `cancellationPfx_of_core` | 826b968 |
| S5 at `J₁` and today's kernel (I) | read prefix-closed: the unwind PROVED at every effect context (`unwindOrderPfx_J₁`, `cancellationPfx_tier1Open`), the no-interception PROVED given `CancelsStd` (`noInterceptPfx_J₁_of`). As written: **FAILS** (`not_unwindOrder_of_types`, `not_cancellation_J₁`, `not_cancellation_tier1Open`, `not_cancellation_admissible`) | 826b968 |
| `FinRowsAt` | OPEN; not on the bridges' route (D4's `FinRow` names the finalisers S5 fires) | — |

**What typing gives about a fired finaliser** (`I.finOK_of_finRow`; `Targets/B/HeapFrame.lean`).
- D4 made the no-interception condition part of S5: each finaliser S5 fires meets `FinRow FR`, a
  closed program typed at a row of abortive operations of `FR`'s labels. At option A that row
  admits nothing.
- At a typing system whose closed programs are Core's (`CoreClosed`: `J₁` and today's kernel), the
  row is tied to the effect context (D1). A tied row that admits no label's operation finds nothing,
  so it is empty (`row_nil_of_find_none`). Core's kernel types the finaliser at `F 1`
  (`der_cases`), and FL puts it in Core's relation there.
- A program in Core's relation at `F A`, at the empty resource, runs to a value from every memory
  with finitely many cells (`runs_of_rel`). The memory is the lowering of the `TW` world that owns
  each of its cells (`ownWorld`, built by `TW.alloc` from `∅`, through `alloc_world`), and that
  world is `wpG`'s frame. A given run is a prefix of `wpG`'s run under the allocator that replays it
  (`wpG_seg`), and the pure row allows no stop. At `F 1` the value is `()` (`runs_of_rel_unit`).
- Reached memories are finite (`finDom_reach`). So every fired finaliser S5 names runs to `()` from
  the memory it fires at (`FinOK`).

**The traces at our machine** (`Targets/Instance/CancelRuns.lean`).
- A step of `Kf[t]`, where `t` steps at the same memory, is `t`'s step under `Kf`, with the same
  label and runner state (`ostep_unplug`, `rstep_unplug`, through Core's `plug_cmp` and
  `head_nested`). So while the fired finaliser has a step, the whole run is its run alone (A's
  `Alone`).
- **The unwind** (`unwind_pfx`, by strong induction on the path; its finaliser phase `pend_pfx`).
  - `Std K` has no finaliser frame (the trace's `out`), or an innermost one with none inside
    (`std_split`).
  - The raise is Core's, at a value (`raise_live`, from `LiveOK`), and `[finalise]` is the only
    step (`rstep_fire_inv`, labelled `fire D`). The β-step `(λ_. D↑) () ↦ D` is the only next step.
  - `D` runs alone. At `()`, `(); raise p ↦ raise p` (`[1↦]`), and the unwind goes on through the
    rest of `K`.
- **The cancel** (`cancel_pfx`; its finaliser phase `fin_pfx`), from
  `ccatch (hnd H K[raise (0, (0, (N, none)))])`, with `K` free of `ccatch` and `cfin` and no handler
  named `0` in `hnd H ∘ K`.
  - With no finaliser frame left, `[cancel]` answers `()` (the trace's `answer`).
  - Otherwise the innermost finaliser frame holds a pair of values (`ubind_pair_live`: otherwise the
    configuration would not go on, against `LiveOK`), and `[finalise-cancel]` fires `finE D`
    (`rstep_fireC_inv`).
  - The β-step follows when `D` is a λ. `D` runs alone under `cfin` to `()`, and `[cfin-ret]`
    (labelled `finEnd none`) hands the cancel on, with nothing kept.
- Each phase gives, for every path `q`, a `q'` of length at most one such that `q ++ q'` is a path
  and a trace. `q'` is the β-step, when `q` stops right after a fire step.

**The finding: S5 as written fails, at A's trace definitions** (`Targets/I/S5J1.lean`).
- `CancelTrace.fire` and `UnwindTrace.fire` take the fire step, a `PurePath c₁ q₀ c₂` of
  administrative steps, and the finaliser at `c₂`; a trace stops only at `[]`. So a path that stops
  inside `q₀` follows no trace, although the traces' docstring says "a trace may stop anywhere".
- At our machine `[finalise]` leaves `D (); raise p` and `[finalise-cancel]` leaves `cfin s (D ())`.
  That is one β-step from `D` whenever `D` is a λ, and A's `thenF` always makes it one.
- **Machine-checked** (`not_unwindOrder_of_types`). The witness is
  `fireProg = handle_exn (raise exn () then x. x unwind ((); ()))`, typed by `J₁` with its rows tied
  (`d_fireProg`) and by today's kernel (`d_fireProgNU`), at every effect context declaring
  `exn : 1 ↠ 0` at `1`.
  - Every premise of `UnwindOrder noFinRaise` holds at its raise under the finaliser frame
    (`fireProg_premises`): the configuration is reached by `look`'s run, the context is one A-level
    finaliser frame holding no handler, the finaliser `(); ()` is a closed program at the pure row,
    and the runner answers nothing.
  - The path of the fire step alone follows no unwind trace (`not_unwindTrace_one`): `(); ()` is at
    no evaluation position of `((λ_. (); ()) ()); raise p` (`fireAfter_ne`, through `evalSubs`).
  - At `ΞA`, which is admissible, this refutes S5 at `J₁` (`not_cancellation_ΞA`) and at today's
    kernel.
- At the same configuration the prefix-closed reading holds (`unwindOrderPfx_fireProg`).
- **The restatement is the user's.** The candidate is `A.CancellationPfx`
  (`Targets/A/CancelPrefix.lean`): every path is a prefix of a trace, that is, some continuation of
  it, itself a path, is a trace. The target implies it (`cancellationPfx_of`). A repair at the
  definitions themselves would let a trace stop inside each administrative path (`fire`'s `q₀`,
  `returned`'s `q₁`). At our machine only a stop between the fire step and `D`'s start is missed: a
  stop before `returned`'s one-step `q₁` is a `running` trace.

**What S5's no-interception reads at our instance.**
- It starts at `cancel (capture l H K)`. At our instance `capture` is `kappa`, the `κ` the catch
  hands at an operation the handler's tags read `unr`.
  - At an admissible context a typed program performs only operations `Ξ` declares resuming, and a
    handler with `Ξ`'s tags (as `capture`'s are) tags them `lin` or `aff`. By that reading no typed
    program reaches NoIntercept's premise there.
  - This is not machine-checked: it needs a run invariant on the payloads of `perform`s and on
    handler values.
- The cancels that arise at an admissible context are of the capture cell's affine `κ` (SPEC §25).
  They reach `cancelOf` after the step that frees the cell, so NoIntercept's `PureSteps` premise
  excludes them.
- `cancel_pfx` is stated at `cancelOf`, at any reached configuration, so it covers them too.
  NoIntercept's restatement at the cell's `κ` is the user's.

**Added hypotheses, and their scope.**
- **`CancelsStd`** (the cancel bridge's). At a configuration a typed program reaches that cancels
  `capture l H K`, the context `K` holds no `ccatch`, no `cfin` and no handler named `0`.
  - Source: SPEC §19's "its handlers are dying, so they catch nothing", read at the capture (no
    operation is caught across a cancel or a cancel-mode finaliser), and I3.c's `NoInterception`
    read on the captured context.
  - Scope: it is about the context the continuation was captured in, not about the cancel run, so it
    does not assume the trace.
  - OPEN at `J₁`. Its handler half needs that a runner's answers in a typed program's run are data
    (B's `platData_of_safe` gives this of the arguments; it is not transported to A's runs here).
    Its `ccatch`/`cfin` half needs that no operation escapes a fired finaliser, which is
    `FinRowsAt`'s kind of whole-run fact.
  - Non-vacuity is not shown. At an admissible context its premise is, by the reading above, never
    met.
- The instance-level bridges also take `LiveOK` (PROVED at `J₁` and today's kernel), that label
  names are not `0` (`orowRF`'s labels), and `FinRow → FinOK` (PROVED at both, `status_finOK`).

**`FinRowsAt`: OPEN, and not on S5's bridges' route.**
- D4 put the fired finalisers' typing into S5's statement, and `finOK_of_finRow` gives what the
  traces need.
- `FinRowsAt` asks about every finaliser a typed program's run fires, with no typing hypothesis on
  it. It still serves Core's I3.b (`FinaliserOrder`, from it by `finaliserOrder_A`) and the
  `ccatch`/`cfin` half of `CancelsStd`.
- Its routes are unchanged:
  - a run-time typing with preservation (route 8.2). That is BRIEF §10's side mechanism, so stop and
    report;
  - an effect-side kernel change that makes an operation escaping a fired finaliser stuck. Then FL
    and B's stuck-freedom (`stuck_of_rel`) give it, as the capture cell made S6's obligation a fact
    of Core's relation.
- *A draft of the second, for the user (not applied).*
  - SPEC §19: `[finalise]` becomes `ubind (N, D) K[raise p] ↦ guard (D ()); raise p`, and
    `[finalise-cancel]` becomes `… ↦ cfin s (guard (D ()))`.
  - A new frame `guard □` with `guard v ↦ v` and no rule at an operation its body leaves uncaught.
    It is a run-time form, with no typing rule.
  - `then_compatC` would read `D` at `F 1` (option A), where `D`'s run makes no stop, so `guard`
    never blocks a typed program. `fundamentalC`, `adequacyC` and `adequacyD` keep their
    statements, and the lowering erases `guard`.
  - It would give `FinRowsAt (fun _ => False) J₁` from FL. With an invariant that every `κ`'s
    captured context is free of `cfin` (no hop captures across `guard`), it would also give
    `CancelsStd`'s `ccatch`/`cfin` half.

**Readings for the user to confirm** (pending; the user has not objected to 1–3):
1. `J₁`'s kernel is Core's whole `CDerives` (`J₁.read`), read at an effect context as the tied
   kernel `CDerivesAt Ξ` (decision R).
2. Row polymorphism is the polymorphic let; the general `[handle]` is the handler value form over a
   persistent context.
3. D4: the no-interception condition is `FinRow FR`; a use of `κ` is a step applying `κ` to a data
   value (`UseAt`); "observationally" is `RunsAlike` at data answers.
4. Decision S5's bridges are read at S5 as written. Where S5 as written fails, the bridges are proved
   at the candidate `CancellationPfx`, and S5 itself is reported, not restated.
5. `CancelsStd`'s source is SPEC §19's dying handlers, read at the capture.

**Unspent hypotheses.**
- S5's `Answers R ε` is read by no bridge: the traces hold under every runner that keeps its
  protocol, and `Respects` is read only through `Live`, for `LiveOK`.
- The program's typing is read only through `Live` (closedness, `GoesOn`).
- `CancelTrace`'s region `N` (`Region l K`) is read by nothing: at option A no finaliser's raise
  reaches `keep`.
- `AdmEff` is read by nothing: the bridges and the prefix-closed results hold at every effect
  context.
- `FinRow`'s row is read only to show it empty.

**Unused uniqueness/functionality results.** `det_ourInst` and `AStep1.deterministic`. Read:
`rstep_det`, `innerCatch_unique`, `plug_opE_eq`, `step1_raise`, `head_ubind_raise`, `plug_cmp`,
`head_nested`, and `ResU.Lower.functional` (inside `wpG_seg`).

**Untranscribed in the run-up.**
- S5 at a set of endings other than `noFinRaise` (the `superseded` case and `ended` with an error);
  the target reads `noFinRaise`.
- `CancelsStd`'s discharge (above), and a run invariant showing that NoIntercept's premise is
  unreachable at an admissible context.
- `FinRowsAt` (above).

**Gate.** `lake build Targets` passes with AxiomCheck and Audit. Every new result's axioms are
within `[propext, Classical.choice, Quot.sound]`, with a `#print axioms` line for each. `make gate`
passed once, at 826b968 ("ci-local --source: ALL PASSED"); it builds the library, which this step
does not touch.

**Remaining.**
- The user's calls: S5's restatement (prefix-closed traces, `CancellationPfx`); NoIntercept at the
  capture cell's `κ`; a route for `CancelsStd` and `FinRowsAt` (the `guard` frame drafted above, or a
  run-time typing).
- From earlier rounds: S4's restatement; `OnlyOwnerFrees`, `NoDanglingUse`; E7–E9, forcing a
  `!U C` slot, `unr` at abortive operations, `unfold`'s value; `TailLaw`, `EtaHold`; `Accepts`,
  `Rejects`; `RowVarKernel J₁`.

## Round 3, step T5: `Accepts` and `Rejects` at `J₁` (decision AR)

**Where tier 1 stands.** Unchanged in kind: `I.Tier1 J₁` **fails as written** through S4's catch
law at `ΞA` (`I.not_tier1_J₁`), and its (E) and S5 hypotheses fail as written too (T3, T4). Decision
AR is applied: **`Accepts J₁.read .abortive` and `Rejects J₁.read` are PROVED** (`I.accepts_J₁`,
`I.rejects_J₁`), so `I.Tier1 J₁` follows from A's (E) properties, S4, S5 and S6 at every admissible
effect context (`I.tier1_J₁_of_ESU`). Nothing in `Core/`, BoLo or SPEC changed, and no borrow
guarantee was weakened. Every result is at Core σ=[]. On `tier1-effects`, not pushed.

| step | status | commits |
|---|---|---|
| runs with memory, computed (base) | LANDED: `runM`, `memAt`, `memOp`, `runM_sound` (`Targets/Base/LookMem.lean`) | 1af8dc0 |
| `Rejects` at Core's kernel | PROVED: thirteen inversions of `CDerives`; `not_der_at05`, `not_der_at06`, `not_der_at08`, `not_der_at13`, `rejects_tier1` (`Targets/I/Rejects.lean`) | 29ed0d0 |
| `Accepts` and `Rejects` at `J₁` | PROVED: the eight runs computed (`run_*`), `compositeT1_tier1`, `I.accepts_J₁`, `I.rejects_J₁`, `I.tier1_J₁_of_ESU`; the rejections at the tied kernel too (`I.rejects_tied`) (`Targets/I/AcceptsRejects.lean`); Status, AxiomCheck, README | 3f18d49, 78fe527 |

**`Accepts`** (`Accepts J₁.read .abortive` is `CompositeT1 tier1`: `J₁.read` is Core's kernel,
`j1_read`, and at `.abortive` the tier-2 conjunct asks nothing).
- Each of the eight programs was already typed at its data answer, safe and terminating under the
  empty platform (`acceptedT1_*`, from B's `soundRetAt_tier1_none`). What was missing is `AcceptedAt`'s
  last conjunct: one complete run answering the stated value.
- **The runs are computed.** `runM` adds the four memory steps (`alloc`, `free`, `load`, `store`) to
  `look`'s steps, at a memory kept as a list of cells, allocating one past the largest location in
  use. The kernel evaluates each program's run to its answer at the empty list (`run_*`, by `rfl`;
  25 to 169 steps). `runM_sound` makes each a run of Core's machine (`Steps`), and `prun_of_steps` a
  run under the empty platform. `logOutside`, `logInBorrow`, `takeProg` and `tickAnsProg`'s answers
  were not determined by adequacy (their flags), and are now theorems; the interpreter's `*_eval`
  stay evidence.

**`Rejects`** (no type at all: `∀ C, ¬ J₁.read.closed atXX C`).
- **The inversions, and their cost** (CLAUDE.md: "Do not invert `CDerives` casually"). Thirteen
  inductions on `CDerives`, about 2200 lines (`Targets/I/Rejects.lean`), 17 s to build. Fourteen of
  Core's rules conclude with their premise's term: the value rules `!E`, `[]I`, `[]E`, the two `⊑`,
  `roll`, `unroll`; `return`, `ofRet`, `[sub]`, `ν`'s two; at a λ-value the two thunk rules. Each
  inversion carries a class of judgements through them: a value read at `T` is read at the views of
  `T` and rows over them (`ValCls`); a computation type that is no row's, no `&` and no `ν` is left by
  none (`JR.rigid`; `ν`'s rules are at `&`-trees only, `CTy.NuOk`). Views keep a type's head (boxes
  stripped, `μ` unrolled) unless it is `!`, `Imm` or `Mut` (`VView.hnf`); persistence is the head's
  (`Hnf.persistent`). The term shapes: a variable, a pair, `()`, an application (`⊸E`, `[app]`,
  `[let]`, the polymorphic let, `∀E`, the projections), a λ-value (through the rule that types its
  body, or as a λ-constant at its axiom's type), `let (x, y)`, `;`, `then`, `handle`, `alloc`, the
  primitives. With them, every free variable of a typed term has a live slot (`fv_live`), so a
  variable used on both sides of a split is persistent (`splitP_both`).
- Every refutation holds at every context and judgement, not only at the empty context and a
  computation type.
- **AT06** (`not_der_at06`): `[handle]` types the clause tuple at `clausesTy`, so the clause at
  `!U(A ⊗ kTy ⊸ F_Σ R)`; a λ-value at a `!` thunk is typed over a persistent context (`lam_bang`), and
  the clause uses the cell, whose slot is a view of a `Ref`. RESTRUCTURE §3.4's reason.
- **AT13** (`not_der_at13`): `κ` is at `kTy` at `lin`, a thunk of an `&`; `forget`'s axioms take `!`,
  `Imm`, `Mut`, `Unk` and `ArrayImm`, and as a λ it drops a persistent argument only
  (`not_forget_kappa`). RESTRUCTURE §3.4's reason.
- **AT05** (`not_der_at05`): through its three bindings, each possibly the polymorphic let, `w c f`
  is typed in a context `At05Ctx` describes (`at05_core`). As a λ, `withborU dFlag` uses its source on
  both sides of its `then` (`wb_generic`), and the source is the cell, a `Ref`; as an unwinding
  constant, `w c` is read only at `cb ⊸ F_Σ R` (`at05_M`), `cb = U(∀'x ⊏ @b. L ⊸ F_Σ(['x] B))` with `L`
  a borrow, where `λm. (m, m)` uses `m` on both sides of a split (`not_at05F_cb`). RESTRUCTURE §3.4's
  reason ("`Mut` has no copy rule"), and it holds at the `Imm` lend too: the `copy` axiom types the
  λ-value `copy`, not a body under a borrow.
- **AT08** (`not_der_at08`): see finding 1.

**Findings.**
1. **AT08's rejection rests on `load`, which has no rule of its own in Core's kernel**
   (machine-checked: `der_prim`, `not_der_load`, `not_der_load_app`); reads go through `withload` and
   `swap`. The clause applies `load` to the cell holding `κ`, so no derivation reaches it. The reason
   RESTRUCTURE §3.4 gives for AT08 (`kTy` at `lin` and `aff` neither droppable nor persistent; an
   `Imm` view of a thunk cannot be forced) is not what refuses the program as written, so this
   conjunct of `Rejects` does not pin that discipline. A restatement of AT08's program, reading the
   cell by `withload` or `swap`, is the user's.
2. `Accepts`' runs replace the interpreter's evidence for the tier-1 composite: their answers are
   theorems at Core's machine.
3. `Rejects` is stated at `J₁.read`, Core's whole kernel; at an effect context our instance reads the
   tied kernel `CDerivesAt Ξ`, whose derivations are Core's (`toCDerives`), so the rejections hold
   there too (`I.rejects_tied`).
4. The existing inversions are over today's kernel (`CDerivesNU`, `Instance/Inversion.lean`) and the
   tied kernel (`CDerivesAt`, `Instance/TiedKernel.lean`); `Rejects` reads Core's `CDerives`, so the
   inductions are rebuilt on it, reusing their helpers (`forceE_cases`, `soloP_slot`, `effOf_inj`,
   `effOf_ne_nu`, `effOf_ne_amp`, `effOf_isRet`, `qualsVal_inj`).

**Readings for the user to confirm** (pending; the user has not objected to 1–3):
1. `J₁`'s kernel is Core's whole `CDerives` (`J₁.read`), read at an effect context as the tied
   kernel `CDerivesAt Ξ` (decision R).
2. Row polymorphism is the polymorphic let; the general `[handle]` is the handler value form over a
   persistent context.
3. D4: the no-interception condition is `FinRow FR`; a use of `κ` is a step applying `κ` to a data
   value (`UseAt`); "observationally" is `RunsAlike` at data answers.
4. Decision AR's "some complete run" is read on a run of Core's machine under the allocator that
   takes one past the largest location in use, as a `PRun` under the empty platform.

**Unspent hypotheses.**
- `AcceptedT1`'s safety and termination are passed to `AcceptedAt` as they are; the computed run
  reads neither.
- `[handle]`'s consumed handler context (`Ctx.DeadP Γ₁`, in `der_hnd`) is read by no refutation:
  AT06's persistence comes from the clause's `!U` type (`bangThunkV`), not from it.
- `lam_bang`'s persistent context is read by AT06 only; `der_bind`'s `CtxLe` outputs by AT05 and AT06
  only.
- `tier1.closed`'s row context (`RowCtx.Models []`) is spent only to instantiate it.

**Unused uniqueness/functionality results.** `det_ourInst`, `AStep1.deterministic` and `rstep_det`:
the runs are computed, so no determinism is read. Read: `Hnf.unique` (through `Hnf.eq_self`),
`Inst.effOf_inj`, `qualsVal_inj`.

**Untranscribed in the run-up.**
- `RejectsAT07` (AT07's stuck run; not a conjunct of `Combined`); `Tier2Programs` (no tier-2 typing
  system).
- AT08's program in the reading RESTRUCTURE §3.4 intends (finding 1).

**Gate.** `lake build Targets` passes with AxiomCheck and Audit; every new result's axioms are within
`[propext, Classical.choice, Quot.sound]`, with a `#print axioms` line for each. `make gate` passed once, at 3f18d49 ("ci-local --source: ALL
PASSED"); it builds the library, which this step does not touch. `lake build Targets` passes at
78fe527.

**Remaining.**
- The user's calls: S4's restatement; algebraicity's (or keeping continuations out of finalisers);
  E7–E9 and option A; S5's restatement (`CancellationPfx`); AT08's program (finding 1).
- From earlier rounds: `OnlyOwnerFrees`, `NoDanglingUse`; `CancelsStd`, `FinRowsAt`; forcing a `!U C`
  slot, `unr` at abortive operations, `unfold`'s value; `TailLaw`, `EtaHold`; `RowVarKernel J₁`.

## Round 3 outcome

**Where tier 1 stands.** `I.Tier1 J₁` is not proved, and it **fails as written**
(`I.not_tier1_J₁`): since the capture cell, S4's catch law fails at `ΞA`
(`Inst.not_handlerSem_J₁_ΞA`). With `Accepts` and `Rejects` proved, it follows from A's (E)
properties, S4, S5 and S6 at every admissible effect context (`I.tier1_J₁_of_ESU`); (E) and S5 also
fail as written at `J₁` (steps T3, T4). `B.Guarantees J₁.read B.coreB` still holds. Every result is
at Core σ=[]. No BoLo definition changed and no borrow guarantee was weakened: `fundamentalC`,
`adequacyC` and `adequacyD` keep their statements with the new rules' cases. HEAD is `193f4f2`, on
`tier1-effects`, not pushed. The untracked `GHOST-RESOURCE.md` was left alone.

| step | status | verifier | commits |
|---|---|---|---|
| T1: S6, the capture cell | LANDED, PARTIAL. SPEC §25: a linear or affine `κ` owns a unit cell from the ordinary allocator; resume frees it, an affine cancel frees it, a linear cancel has no step; kernel and corpus counts unchanged. S6 stated per capture event (`ContUseEv`, `CatchEvAt`); R1 refused by Core's relation (`I.not_semC_R1`, the route-8.4 obligation); `catchEv_cell`, `use_frees_cell`, `leakFreeAt_J₁`; S6 reduced to `OnlyOwnerFrees` and `NoDanglingUse` (`I.contUseEv_J₁_of`). S4 proved where resuming operations are `unr` (`CatchUnr`); fails as written at `ΞA` | pass | 96562bc, fa225d5, 68e0d04, 009c9c0 |
| T2: decision R, inner rows tied | LANDED. `CDerivesAt Ξ` (`Instance/TiedKernel.lean`) ties perform, raise and handle to `Ξ`; `toCDerives`; `J1DerAt`; every round-2 result re-established at the tied `J₁`. Round 2's finding settled: `algFireProg` does not type at the tied `J₁` (`not_rowAt_R5`, `not_der_algFireProg_J₁`). `AlgLaw` still fails as written at the tied `J₁` through an affine witness (`algAffProg`, `not_algLaw_J₁`). `TailLaw` recorded OPEN | pass | 612dd94, 9e4a67d |
| T3: decision E, A's (E) properties | PARTIAL. SPEC §26: `[λ-dead]` (`CDerives.lamDead`, `lamDead_compatC`). Proved: E1, E4, E6 at every admissible context; E5 given `NoUnrExn`; E2d given `NoUnr`; E10's `timeout`. `EProps` fails as written at `J₁` under option A (E7–E9's finalisers raise). E2a–c, E3, E10's `retry` and loop not derived, no obstruction checked | pass | f2c98d6, 1361bb5, 8befb94, e968072, 50a93ce, 8ebedbb |
| T4: decision S5, the bridges | PARTIAL. Bridges built for the prefix-closed reading (`unwindOrderPfx_of_core`, `noInterceptPfx_of_core`, `cancellationPfx_of_core`); `unwindOrderPfx_J₁` with no added hypothesis; no-interception given `CancelsStd` (open); finalisers meeting no-interception run to `()` (`finOK_of_finRow`). S5 fails as written (`not_cancellation_J₁`, witness `fireProg`): A's trace `fire` needs the β-step after `[finalise]`. `FinRowsAt` not delivered | **fail: one major finding (open, below)** | 826b968, 3903aa8 |
| T5: decision AR | LANDED. `I.accepts_J₁` (runs by `runM`, `runM_sound`, by `rfl`); `I.rejects_J₁`, `I.rejects_tied` (13 inductions on `CDerives`, `I/Rejects.lean`). AT08 is refused for lack of a bare-`load` rule, not for RESTRUCTURE §3.4's reason | pass | 1af8dc0, 29ed0d0, 3f18d49, 78fe527, 193f4f2 |

**Kernel changes** (effect side only):
- **SPEC §25, Entry 24: the capture cell.** `hndVal` carries the operations' qualifier tags; at a
  `lin` or `aff` operation `[op]` allocates a unit cell owned by `κ`; resume frees it, an `aff`
  cancel frees it (matching `contShare`'s `q ≠ lin` gate). Zero-size, so the lowering allocates
  nothing; corpus and kernel counts unchanged. Core's effect lemmas re-proved.
- **SPEC §26, Entry 25: `[λ-dead]`.** `λx. M` at `1 ⊸ F_Σ B` with `x`'s slot dead
  (`CDerives.lamDead`, `lamDead_compatC`), for A's callbacks `λ_. M`.

The tie of decision R lives in a Targets-side copy of the judgement (`CDerivesAt`), not in Core.

> **OPEN VERIFIER FINDING (major), T4.** Decision S5 named "S5's two bridges plus `FinRowsAt`".
> `FinRowsAt` was not delivered: the step drafted an effect-side kernel change (a `guard` frame
> around fired finalisers, SPEC §19) and left it unapplied for the user, although effect-side
> kernel changes are not a cost and nothing machine-checked blocks the route. This also leaves the
> `ccatch`/`cfin` half of `CancelsStd` undischarged. The bridges do not need `FinRowsAt`, but
> `FinaliserOrder` (I3.b) and `CancelsStd` do. Not yet done: apply the guard frame with its SPEC
> entry, re-prove `then_compatC`, `EffCancel` and `fundamentalC`'s effect cases with
> `adequacyC`/`adequacyD` unchanged, confirm the lowering erases `guard` (counts unchanged), prove
> `FinRowsAt noFinRaise J₁`, and discharge `CancelsStd`'s `ccatch`/`cfin` half; or report a
> machine-checked obstruction.

**Gate.** `make gate` at `193f4f2` passed; the source stage ran ("ci-local --source: ALL
PASSED"): build, compile scaling (8×/1× ratio 11.9, limit 16), hygiene and axioms, axiom report,
corpus parse, check (22 pending programs failing as recorded), compile, kernel compile, sugar
pairs, typed IR, book doc-tests (82 passed, 1 ignored, 0 failed), book build. `lake build Targets`
passes with AxiomCheck and Audit; every new axiom set is within
`[propext, Classical.choice, Quot.sound]`.

**Readings for the user to confirm** (pending; carried from round 2 and added this round).
1. `J₁`'s kernel is all of `CDerives` for `J₁.read`, and `CDerivesAt Ξ` at an effect context.
2. Row polymorphism is the polymorphic let; the general `[handle]` is the handler value form.
3. D4: `FinRow FR` as no-interception, `UseAt` as a use of `κ`, comparison at data answers.
4. S6 is read per capture event (`ContUseEv`).
5. The tie covers perform, raise and handle only; a tied handler may declare a prefix of `Ξ n`.
6. `[λ-dead]` is decision E's "dead binder"; an `unr` `exn` label counts among E5's labels.
7. "Some complete run" (`Accepts`) is a run whose allocator takes one past the largest location.

**Decisions for the user.**
- S4's catch law: restate for a catch that allocates the cell.
- `AlgLaw`: observe a finaliser's start without its code, or keep continuations out of finalisers.
- Whether a handler must declare all of `Ξ n`.
- E7–E9 against option A; forcing a `!U C` slot (a Core rule, or a derelicting `let`); `unr` at
  abortive operations in `[let]`'s side condition; typing `unfold`'s value (`etaN`).
- S5: the prefix-closed reading (`CancellationPfx`); no-interception at the cell's `κ`.
- AT08: read the cell through `withload` or `swap` so it tests the continuation rule.

**Remaining.** The T4 finding (`FinRowsAt` by the guard frame; `CancelsStd`); `OnlyOwnerFrees`
and `NoDanglingUse` (S6); S2's teeth for R2–R4 under the cell; S5 at the cell machine; E2a–c, E3,
E10's `retry` and loop (with `RunsForever`); `TailLaw`, `EtaHold`, `I4Typing`, `I4Runs`;
`RowVarKernel J₁`.

**Unspent hypotheses.** `AdmEff`'s `ClosedLife` (read by no S6 or (E) result) and `Rich` (labels
only); `DataTy A` only through leak freedom; `Respects` only for `Live`; the tie, read only by
exclusion proofs; `Answers R ε` (passed to `CancelsStd`); `CancelTrace`'s region `N`;
`AcceptedT1`'s safety and termination; `[handle]`'s `DeadP` in the refutations.

**Unused uniqueness/functionality results.** `det_ourInst`, `AStep1.deterministic`, B5's
per-step `RelAt` maps; `rstep_det` unused in T5.

**Untranscribed in the run-up.** The cell-sealing invariant; coherence of B5's maps between
hand-off and use; S4's and `AlgLaw`'s restatements; `TailLaw` against the finaliser mechanism;
`EtaHold`'s and `I4Typing`'s inversions; forcing a `!U C` slot; a typing of `etaN`; `RunsForever`;
`CancelsStd`'s discharge; `FinRowsAt`; AT07's stuck run; `Tier2Programs`.

**Next.**
1. Resolve the T4 finding: the guard frame and `FinRowsAt noFinRaise J₁`.
2. `OnlyOwnerFrees` and `NoDanglingUse`.
3. The user's restatements above, then the (E) programs they unblock.

## Fix-up outcome

A short proof-side fix-up before tier 1 is wired into the language: the statements that predate the
capture cell (SPEC §25) and the pieces round 3 left undelivered. Steps F1–F5; the goal is that
`I.tier1_J₁_of_ESU`'s premises hold except where a user decision is pending (E7–E9 under option A;
S6's `OnlyOwnerFrees` and `NoDanglingUse`, a separate unit). On `tier1-effects`, not pushed.

**Where tier 1 stands (after F3).** `I.Tier1 J₁` **fails as written** through A's (E) properties
(E7–E9 under option A; `I.not_tier1_J₁`, `status_tier1_J₁`). **S4 is RESTATED at the capture cell
and PROVED at `J₁` at every effect context** (`I.handlerSem_J₁`). **S5 is RESTATED prefix-closed and
PROVED at `J₁` at every effect context given `CancelsNoCtl`** (`I.cancellation_J₁_of`), its unwind
with no added hypothesis. So `I.Tier1 J₁` follows from A's (E) properties, `CancelsNoCtl` and S6 at
every admissible effect context (`I.tier1_J₁_of_ENU`), and `I.Tier1Core` from S5 at today's kernel
(`I.tier1Core_of_S5`), where S5's unwind is proved and its no-interception given `CancelsNoCtl`
(`I.cancellation_tier1Open`). No change to `Core/`, BoLo, the machine or the relation; every existing
Core and BoLo theorem builds unchanged. Every result is at Core σ=[].

| step | status | commits |
|---|---|---|
| F1: S4's catch law at the capture cell | LANDED. A carries a continuation's cell (`Cell`, `captureAt`, `cellFree`, `withCell`); the catch law hands `capture l H K` keeping the store, or `κ` at one fresh unit cell with the store gaining that cell and nothing else (`CatchLaw`, `JoinAcross`); deep resume and an affine cancel at a cell release it (`ResumeCellLaw`, `CancelCellLaw`). PROVED at our instance at every effect context (`handlerSem_ourInst`), so at `J₁` (`I.handlerSem_J₁`) and today's kernel. S4 with no cell kept (`HandlerSemNoCell`), equal to S4 at every cell-free instance (`handlerSem_iff_noCell`); teeth (`not_handlerSem_toy`); not vacuous at `J₁` (`I.catchLaw_progT_cell`, `status_cellLaws_J₁`) | af7d30d |
| F2: algebraicity, a finaliser's start observed but not its code | LANDED, given `CfinQuiet`. `AlgLaw` compares the two sides with each `fire D` read as `fire ()` (`Ev.start`, `RunsAlikeStart`); `AlgLawCode` (the code observed) kept, implies it, refuted at `J₁` and `ΞA` (`not_algLawCode_J₁`, `not_algLawCode_ΞA`). PROVED at `J₁` at every effect context given `CfinQuiet` (no configuration a typed program reaches is at a `[cfin-raise]` step; option A; F4's `guard` frame is its route): the two sides run step for step alike (`Instance/AlgSim.lean`, `algLaw_of_good`; `I.algLaw_J₁_of`). At `algAffProg`'s configuration the restated law holds (`algLaw_algAffProg`) | 2caf85a |
| F3: S5 read prefix-closed, a trace's fire step with its β-step | LANDED, given `CancelsNoCtl`. `NoIntercept` and `UnwindOrder` read every run from the start as a prefix of a trace; S5 read whole kept (`CancellationWhole`), implies it, refuted at `J₁`, today's kernel and `ΞA`. At our instance the extension a run needs is nothing or the β-step after a fire step (`FireExt`). PROVED at `J₁` and today's kernel at every effect context: the unwind outright (`I.unwindOrder_J₁`), the no-interception given `CancelsNoCtl` (`I.noIntercept_J₁_of`); `CancelsStd`'s handler half PROVED as a run invariant (`I.cancelsNZ_J₁`, `Targets/I/CancelsNZ.lean`). Teeth kept: at `J₄` the run from the cancel is a prefix of no cancel trace (`noIntercept_needs_finRow`). Tier 1 from (E), `CancelsNoCtl` and S6 (`I.tier1_J₁_of_ENU`) | 4ae897e |

### F1: S4 at the capture cell

**The statement** (`Targets/A/Soundness.lean`, `Targets/A/System.lean`).
- The capture cell is the one-shot continuation object of Affect §3.1 (and Hazel's): allocated at
  the catch, released by the continuation's use. A now carries it: a type of cells (`Cell`), `κ` at
  a cell (`captureAt k l H K ℓ`, indexed by the operation's class, whose cancel branch it is), a
  location the store does not hold (`cellFree c ℓ`), and the store with a unit cell at `ℓ`
  (`withCell c ℓ`). At our instance: locations, `kappaC (k = affine) ℓ`, `μ ℓ = none`, `μ.upd ℓ ()`.
- `JoinAcross c c' t`: `c` reaches a common reduct with `t` at `c'`'s store by store-keeping steps but
  one, a step that leaves the store of `c'`. At `c' = withCell c ℓ` that step is the allocation; at
  `c = withCell c' ℓ` the release.
- The catch law (`CatchLaw`): at a catch of a resuming operation the clause gets the argument and
  either `capture l H K` with the store kept (`PureJoin`, as before), or `captureAt o.cls l H K ℓ`
  at a location `ℓ` the store does not hold, across one step to `withCell c ℓ`
  (`JoinAcross c (withCell c ℓ)`). Literature-simple: Affect's
  `(handle K[do v] with h, σ) → (h (v, cont ℓ K), σ[ℓ ↦ ·])`, `ℓ` fresh.
- **Not weakened beyond the cell.** The store change allowed is exactly one fresh unit cell, and the
  `κ` handed at it is pinned as `capture l H K` is: deep resume at a cell (`ResumeCellLaw`) releases
  the cell and runs `handle l H K[w]`, and an affine `κ`'s cancel at a cell (`CancelCellLaw`)
  releases it and starts `cancelOf l H K`. Without these two the catch law would hand a `κ` no law
  reads. A linear `κ`'s cancel has no law: its cancel branch has no step (SPEC §25), and S6 says it
  is never cancelled. The return, abortive, deep-resume, cancel and finaliser laws are unchanged.
- `HandlerSem` is the nine laws (`RetLaw`, `CatchLaw`, `AbortLaw`, `ResumeLaw`, `ResumeCellLaw`,
  `CancelLaw`, `CancelCellLaw`, `ThenLaw`, `FinLaw`). **`HandlerSemNoCell`** is S4 with no cell (the
  seven laws, the catch store-keeping, `CatchKeep`), kept as a record.

**Teeth** (every instance; `Targets/A/UnaryLaws.lean`).
- At an instance with no cells the two statements are the same (`handlerSem_iff_noCell`), so every
  refutation of S4 with no cell at such an instance refutes S4 (`not_handlerSem_of_noCell`). The
  statements differ only at a cell.
- No refutation of S4 at a bad instance existed before this step; one is built: at `toy` with a
  `handle` that ignores its clauses (no cells), the catch never meets its clause applied to the
  argument and `κ`, so S4 with no cell fails (`not_handlerSemNoCell_toy`) and so does S4
  (`not_handlerSem_toy`).

**At our instance: PROVED at every effect context** (`Targets/Instance/HandlerCell.lean`), given
`LiveOK`, at a row form whose names are not `0` and whose signatures are indexable by `UInt32`
(`orowRF`'s are).
- The earlier proof is split into one theorem per law (`Targets/Instance/Machine.lean`:
  `retLaw_ourInst`, `catch_unr_ourInst`, `abortLaw_ourInst`, `resumeLaw_ourInst`,
  `cancelLaw_ourInst`, `thenLaw_ourInst`, `finLaw_ourInst`), shared by S4 and by S4 with no cell
  (`handlerSemNoCell_ourInst` under `CatchUnr`).
- The catch law (`catchLaw_ourInst`) by the operation's qualifier: at `unr` the tag is `2`, the catch
  hands `kappa` and keeps the store (`catch_unr_ourInst`); at `lin` or `aff` (`catch_cell_ourInst`):
  the `[op]` step (store-keeping) hands `kappaCell`; the reached memory is finite (`finDom_reach`), so
  some `ℓ` is free (`exists_fresh_of_live`); the allocation of `()` at `ℓ` is the one step to
  `withCell c ℓ`; `κ`'s β-step at `ℓ` gives `kappaC (cellAff q) ℓ` (`kappaCBody_subst`), which is
  `captureAt o.cls … ℓ` since the class of a resuming `lin`/`aff` operation is `linear`/`affine`.
- Deep resume at a cell (`resumeCellLaw_ourInst`): `resume` binds `w`; `kappaC`'s β, case and `;`
  reach `free ℓ` quietly (`kappaC_resume_parts`); the release gives back the memory without `ℓ`
  (`del_upd_fresh`); quietly on to `hnd H K[w]`. Cancel at a cell (`cancelCellLaw_ourInst`): the same
  through the cancel branch (`kappaC_cancel_parts`, new beside the resume's) to
  `ccatch (hnd H K[raise (0, (0, (N, none)))])`. A handler of non-values gives the stuck junk `()`,
  excluded by `LiveOK`.
- `handlerSem_ourInst`, `handlerSem_orow`; `I.handlerSem_J₁` at `J₁` (`liveOK_J₁`, now in
  `Targets/I/J1.lean`, one declaration); at today's kernel from `liveOK_tier1Open`
  (`status_machShape_handlerSem_tier1Open`).

**Not vacuous at `J₁`.**
- The catch law (`I.catchLaw_progT_cell`): at the admissible `ΞA`, `progT` reaches the catch of the
  linear `tick` (`live_progT_catch`), every premise of the law holding there; the store-keeping
  alternative fails (`not_pureJoin_progT`, the refutation of S4 with no cell, now a lemma), and the
  catch allocates `κ`'s cell.
- The laws at a cell (`status_cellLaws_J₁`): E4's `deepGen` reaches its clause's `resume` of `κ` at
  its cell with the cell held (`resumeCell_deepGen`: the catch, the allocation, the runner's `tick`,
  the β-step); `algAffProg` reaches its finaliser's cancel of the affine `κ` at its cell
  (`cancelCell_algAffProg`). Each is a configuration a typed program reaches at which every premise
  of the law holds.

**S4 with no cell, kept** (`not_handlerSemNoCell_J₁_ΞA`): fails at `J₁` at `ΞA`, by `progT`; holds
where resuming operations are unrestricted (`handlerSemNoCell_orow`, `I.handlerSemNoCell_J₁`).

**Tier 1 re-derived.** `I.not_tier1_J₁` is now through (E) (`Inst.not_eProps_J₁` at `ΞA`; moved to
`Targets/I/AcceptsRejects.lean`). `I.tier1_J₁_of_ECU` discharges `hS4`; `I.tier1_J₁_of_ESU` and
`I.tier1_J₁_of` keep their statements. SPEC §25's *Open* note on S4 updated; the register's P1 and
P11 rows updated.

**The premises of `I.tier1_J₁_of_ESU`, after F1.**

| premise | status | Lean |
|---|---|---|
| `hE`: A's (E) properties at every admissible `Ξ` | **FAILS AS WRITTEN** (E7, E8, E9 under option A); the user's decision (E7–E9's programs or option A) | `Inst.not_eProps_J₁`, `status_eProps_J₁` |
| `hS4`: S4 at every admissible `Ξ` | **PROVED** (at every effect context) | `I.handlerSem_J₁` |
| `hC`: S5 at every admissible `Ξ` | **FAILS AS WRITTEN** (`fire` reads the β-step after `[finalise]`; F3's restatement); read prefix-closed, the unwind PROVED, the no-interception given `CancelsStd` (F4's guard frame for its `ccatch`/`cfin` half) | `I.not_cancellation_admissible`, `status_cancellation_J₁` |
| `hU`: S6 at every admissible `Ξ` | OPEN: reduced to `OnlyOwnerFrees` and `NoDanglingUse` (not this unit) | `I.contUseEv_J₁_of` |
| `Accepts`, `Rejects` | PROVED | `I.accepts_J₁`, `I.rejects_J₁` |

**Readings for the user to confirm** (pending).
1. S4's restatement at the cell: a catch may allocate exactly one fresh unit cell, and hands `κ` at
   it; `κ` at a cell is pinned by deep resume and affine cancel at a cell, which release it. The
   catch's first alternative (`capture l H K`, store kept) stays, for an operation whose `κ` owns no
   cell (at our instance, an unrestricted resuming one).
2. `κ` at a cell is indexed by the operation's class: a linear `κ`'s cancel has no law.
3. The laws at a cell read a store that holds the cell with the unit value (`withCell c ℓ`, `ℓ` free
   in `c`).

**Unspent hypotheses.** `ResumeCellLaw`'s class `k` is read by nothing at our instance (the resume
branch is the same at every class). `hnz` is read only by the abortive and finaliser laws, `hlen`
only by the catch and abortive laws. `LiveOK` gives closedness (values, handler values, the junk
cases) and `GoesOn`; the finiteness that gives a free location comes from `Live` itself (a run from
`init`).

**Unused uniqueness/functionality results.** `rstep_det`, `AStep1.deterministic`: the proofs build
runs and read no determinism. Read: `det_ourInst` (in `not_pureJoin_progT`), `Targets.head_alloc_inv`
(in `no_pureStep_alloc`).

**Untranscribed in the run-up.** A-level laws on `withCell`/`cellFree` (that `withCell` keeps the
term and commutes with `setT`): not stated; the laws read `withCell` only through `setT` and `term`,
and the instance's are by `rfl` (good faith). A refutation of S4 at a bad instance with cells (a
catch allocating two cells, or handing a `κ` its resume does not release): not built.

**Gate.** `lake build Targets` passes with AxiomCheck (`#print axioms` of each new result, every set
within `[propext, Classical.choice, Quot.sound]`) and Audit. `make gate` is the separate stage's.

**Remaining** (F2–F5, then the user's calls).
- F2: algebraicity observing a finaliser's start, not its code; F3: S5 read prefix-closed, the trace's
  fire step with its β-step; F4: the guard frame, `FinRowsAt`, `CancelsStd`'s `ccatch`/`cfin` half;
  F5: AT08 rejected by the continuation rule.
- The user's: E7–E9 against option A; S6's `OnlyOwnerFrees` and `NoDanglingUse`; the earlier rounds'
  open items (forcing a `!U C` slot, `unr` at abortive operations, `unfold`'s value, `TailLaw`,
  `EtaHold`, `RowVarKernel J₁`).

### F2: algebraicity, a finaliser's start observed but not its code

**The statement** (`Targets/A/UnaryLaws.lean`).
- `Ev.start` reads a finaliser's start `fire D` as `fire ()` and every other event as it is; two
  events read alike exactly when they are equal or both a finaliser's start
  (`Ev.start_eq_start_iff`), and they are observable alike (`Ev.obs_of_start_eq`).
- `RunsAlikeStart t₁ t₂` is `RunsAlike` with each trace read through `Ev.start` (`ObsStartFrom`,
  `obsStartFrom_iff`: a complete run's answer and its trace mapped by `Ev.start`). `AlgLaw` reads it:
  `(op v to x. M) to y. N` runs as `op v to x. (M to y. N)`, a finaliser's start observed, not its
  code. D4's reading applied to the trace's events: the two sides capture different continuations,
  and a finaliser that holds its side's `κ` is a different term on each side, though it starts at
  the same point of each run.
- **Kept as a record**: `AlgLawCode`, the statement before (traces compared event by event, `fire D`
  by `D`). It implies `AlgLaw` (`algLaw_of_algLawCode`, through `runsAlikeStart_of_runsAlike`); its
  refutations stay (`not_algLawCode_J₁`, `not_algLawCode_ΞA`, formerly `not_algLaw_J₁`,
  `not_algLaw_ΞA`; `not_algLawCode_toy`).
- **Teeth**: `AlgLaw` fails where `bind` does not associate with `perform` (`not_algLaw_toy`); `toy`
  shows no event, so a finaliser's code plays no part.
- The alternative repair, keeping continuations out of finalisers, is a surface rule; not applied.

**At `J₁`: PROVED at every effect context, given `CfinQuiet`** (`I.algLaw_J₁_of`,
`status_algLaw_J₁`).
- **The relation** (`Targets/Instance/AlgSim.lean`). `AlgRel M N` relates terms equal constructor by
  constructor except where the left holds `(x to x. M) to y. N` and the right `y to x. (M to y. N)`,
  at related `x` and `y`; `AlgRelK` relates contexts (the left's frames `□ to x. M`, `□ to y. N`
  against the right's `□ to x. (M to y. N)`), `AlgRelH` memories. Kept by shifting and substitution
  when `M` and `N` are closed under their binders (`AlgRel.shift`, `AlgRel.subst`); the machine reads
  related terms alike — a frame's handler name and what it stops, a clause, a tag, a literal, an
  allocation (`AlgRelK.hasHnd`, `AlgRelK.catches`, `AlgRelK.hndNames`, `clauseAt_rel`, `capTag_eq`,
  `AlgRel.host_call_eq`, `AlgRel.allocs_eq`) — and on terms with no λ it is equality
  (`AlgRel.eq_of_lamFree`). The continuation a catch hands each side (`kappaAt_rel`), and everything
  a clause builds from it, is related.
- **A head step** (`AlgRel.head`): every rule of Core's machine steps alike at a related redex and
  memory, an allocation at the same location. Its label agrees read without a finaliser's code
  (`labelOf_start`), a cancel-mode finaliser's error agreeing when it holds no λ.
- **A machine step** (`ostep_sim`, through `AlgRel.plug_inv`): the left's step is the right's by the
  same rule at the related redex, but at the left's inner `x to x. M` at a value, where the left's
  β-step and the right's β-step at `y to x. (M to y. N)` both reach `M[x] to y. N` (`algR_beta`).
- **Runs**: forward (`rstep_fwd`, `rpath_fwd`; the runner answers alike at an argument with no λ),
  and back (`rstep_bwd`, `rpath_bwd`: the left goes on by `LiveOK`; its step is the right's by Core's
  unique decomposition and determinism, `plug_decomp` and `head_det`; an allocation is re-taken at
  the right's location, `AlgRel.head_back_alloc`). Complete runs end at related values, equal when
  the left's answer is data (`obsStartFrom_iff_rel`).
- **What a typed program's runs give** (`AlgGood`; `Targets/I/AlgJ1.lean`): closed and going on
  (`LiveOK`); answering data (`lamFree_answer_of_coreClosed`: the run under the runner's platform
  continues to an end or a stop, a value takes no step); asking the runner at data
  (`lamFree_io_of_coreClosed`: every run of a program in Core's relation keeps the protocol of the
  platform restricted to data arguments, `platData_of_start`, after B5's `platData_of_safe`; the
  operation is the platform's, since a stop it does not answer would be a stop of the row the runner
  answers); a cancel-mode finaliser's raise keeping an error with no λ, read from `CfinQuiet`.
- `algLaw_of_good`: algebraicity at every typing system whose typed programs' runs are `AlgGood`.

**The added hypothesis, `CfinQuiet`**: no configuration a typed program reaches is at a
`[cfin-raise]` step.
- Source: option A (SPEC §19, decision D3): `[then]` types a finaliser at `F 1`, so it handles its
  raises itself.
- Scope: the configurations the law reads (`Live`). It is read only where a cancel-mode finaliser
  raises past its `cfin` frame: there the kept error is an event's value (`finEnd (some …)`), which
  could hold the side's `κ`.
- **Not proved here, and its non-vacuity at `J₁` is not shown.** Core's relation gives it inside
  `[then]`'s compatibility (`ewp_cfin` at an abort-only table with no entry); no lemma carries that
  to the configurations of a run (`wpG_seg` sees a run's segments whole). F4's `guard` frame makes it
  a run invariant: every `cfin` frame then holds `guard e` or a value, so no `[cfin-raise]` redex
  arises. F4 must then extend `AlgRel.head` with `guard`'s rule and the changed `[finalise]` results.

**The witness, on the right side** (`algLaw_algAffProg`, `algAffProg_start`; `status_unaryLaws`).
At the configuration `algAffProg` reaches with the law's left side under its two handlers (typed at
`F 1` with its rows tied, reached under every runner), each side's complete runs answer `()` and show
one finaliser's start at whatever cell `κ`'s allocation picks (`obsFrom_algAffL`, `obsFrom_algAffR`,
from `obsFrom_algSide`). Read without the code the two coincide; read with it they differ
(`finE_D2_ne`, `not_algLawCode_J₁`).

**The premises of `I.tier1_J₁_of_ESU`**: unchanged by F2 (algebraicity is beside done; F1's table
stands).

**Readings for the user to confirm** (pending).
1. Algebraicity observes a finaliser's start, not its code (`Ev.start`): D4 read at the trace's
   events. Keeping continuations out of finalisers, the alternative, is not applied.
2. A cancel-mode finaliser's end keeps its error as observed (`finEnd r` is not read through
   `Ev.start`); at option A no typed run reaches one with an error (`CfinQuiet`).
3. `TailLaw` and `EtaHold` still compare `fire D` by `D` (`RunsAlike`); whether they read the same
   observation is the user's.

**Unspent hypotheses.** `AlgLaw`'s grading (`(S.sig l)[i]? = some o`, `o.cls ≠ .abortive`) is read
by nothing at our instance: the two sides run alike at every operation. `der`'s typing is read only
through `LiveOK`, the data answer and the platform's protocol. `AdmEff` is read by nothing (every
effect context).

**Unused uniqueness/functionality results.** `rstep_det`, `det_ourInst`, `AStep1.deterministic`:
the converse reads Core's `plug_decomp` and `head_det` directly.

**Untranscribed in the run-up.** `CfinQuiet` at `J₁` (F4's `guard` frame); `TailLaw` and `EtaHold`
against the start observation.

**Gate.** `lake build Targets` passes with AxiomCheck (`#print axioms` of each new result, every set
within `[propext, Classical.choice, Quot.sound]`) and Audit. Nothing in `Core/`, BoLo, the machine or
the relation changed. `make gate` is the separate stage's.

**Remaining** (F3–F5, then the user's calls).
- F3: S5 read prefix-closed, the trace's fire step with its β-step; F4: the guard frame,
  `FinRowsAt`, `CancelsStd`'s `ccatch`/`cfin` half, and with it `CfinQuiet` at `J₁` (and
  `AlgRel.head`'s `guard` case); F5: AT08 rejected by the continuation rule.
- The user's: E7–E9 against option A; S6's `OnlyOwnerFrees` and `NoDanglingUse`; the readings above;
  the earlier rounds' open items (forcing a `!U C` slot, `unr` at abortive operations, `unfold`'s
  value, `TailLaw`, `EtaHold`, `RowVarKernel J₁`).

### F3: S5 read prefix-closed, a trace's fire step with its β-step

**The statement** (`Targets/A/Soundness.lean`, `Targets/A/CancelWhole.lean`).
- S5's two statements read every run from the start of a cancel or of an unwind as a prefix of a
  trace: from `RPath R c q`, `NoIntercept` and `UnwindOrder` conclude
  `∃ q', RPath R c (q ++ q') ∧ Trace (q ++ q')`. This is how a safety property is read
  (Alpern–Schneider): a finite run satisfies it when some continuation of it is an allowed trace.
- The trace definitions are unchanged. Their docstrings now say where a trace stops: before a fire
  step or the answer (`stop`), while a finaliser runs alone (`running`), and anywhere after the
  answer. The earlier "a trace may stop anywhere" was not true of the definitions. A trace's fire
  step carries the administrative steps that start the finaliser (`fire`'s `PurePath c₁ q₀ c₂`);
  at our machine that is the β-step of `D ()`.
- **Kept as a record**: S5 read whole (`NoInterceptWhole`, `UnwindOrderWhole`,
  `CancellationWhole`: every run a trace). It implies S5 (`noIntercept_of_whole`,
  `unwindOrder_of_whole`, `cancellation_of_whole`), and its refutations stay
  (`not_unwindOrderWhole_of_types`, `not_cancellationWhole_J₁`, `not_cancellationWhole_tier1Open`,
  `not_cancellationWhole_ΞA`, `not_cancellationWhole_admissible`; witness `fireProg`).
- **The trace's fire step with its β-step.** At our instance the extension S5 asks of a run is
  nothing, or exactly one `tau` step when the run stops at a fire step: the β-step that starts the
  fired finaliser (`FireExt`, carried through `unwind_pfx`, `pend_pfx`, `cancel_pfx` and `fin_pfx`).
  No trace constructor that stops inside `q₀` is added: under the prefix-closed reading a run may
  already stop there, and every step it takes must still be a trace's.

**Not weakened beyond the stop.**
- Every step a run takes is a step of the trace it is a prefix of; only where a run may stop
  changes. A run stuck where no trace stops still fails S5: its only continuation is itself.
- At our instance the extension is exactly the β-step after a fire step (`FireExt`).

**Teeth** (`Targets/Instance/Checks.lean`, `status_noIntercept_needs_finRow`).
- The no-interception condition is still needed. `J₄` types one program, with no `ccatch`, `cfin`
  or handler named `0`. Its run reaches a cancel whose region's finaliser performs the operation the
  dying handler catches. The run from the cancel's start is a prefix of no cancel trace at any set of
  endings, whatever continuation is taken.
- After the dying handler's catch, every path is a prefix of the computed run to `()`
  (`rpath_prefix_chainPath`: every path from a chain of head steps that ends at a value is a prefix
  of the chain's path, by `rstep_det`). No configuration of that run holds an operation at an
  evaluation position (`p5x₃_noPerform`, by `decide`). So the finaliser would start at no
  configuration after the catch (`purePath_end`).

**At `J₁` and today's kernel, at every effect context** (`status_cancellation_J₁`).
- The unwind: PROVED with no added hypothesis (`I.unwindOrder_J₁`, `I.cancellation_tier1Open`).
- The no-interception: PROVED given `CancelsNoCtl` (`I.noIntercept_J₁_of`, `I.cancellation_J₁_of`).
- `CancelsStd` is split in two (`cancelsStd_of`): `CancelsNoCtl` (no `ccatch` or `cfin` frame in a
  cancelled continuation's context; OPEN, F4) and `CancelsNZ` (no handler named `0` there;
  PROVED).
- **`CancelsNZ` is a run invariant** (`Targets/I/CancelsNZ.lean`; `cancelsNZ_of_coreClosed`,
  `I.cancelsNZ_J₁`, `I.cancelsNZ_tier1Open`):
  - a typed program names no handler `0` (`hndNZ_of_der`, through I3.c's `okE_of_derives`);
  - no machine step creates one (`hndNZ_step1`; the stored values too, `HeapNZ`);
  - the runner answers with data. Every run of a program in Core's relation asks the platform at
    data arguments only (`platData_of_start`, from F2). A driven program's run does too
    (`driveData_of_reach`, new: the drive's invariant holds under the restricted platform,
    `driveSafe_of_reach`, `driveSafe_cont`, `platData_of_cont`). The protocol answers a data
    argument with data (`Platform.Respects.typed`, `hndNZ_of_dataVal`);
  - so every configuration a typed program reaches names no handler `0`, and neither does its memory
    unless it is a driven program's answer (`hndNZ_reach`);
  - a cancel of `kappa n H K` reaches, three steps later, `ccatch (hnd H K[raise …])`
    (`kappa_cancel_run`), which holds `K`; so `K` names no handler `0` (`hasHnd0_of_knz`). The
    handler is a value, or the cancel is stuck (`LiveOK`).
- Tier 1: `I.tier1_J₁_of_ENU` (`status_tier1_J₁_of_ENU`), from A's (E) properties, `CancelsNoCtl`
  and S6 at every admissible effect context.

**The witness, on the right side** (`I.unwindOrder_fireProg`). At `fireProg`'s raise under its
finaliser frame, the path of the fire step alone is a trace once the β-step is taken. Read whole it
follows no trace (`not_unwindTrace_one`, `not_cancellationWhole_ΞA`).

**`CancelsNoCtl`, the hypothesis left.**
- Statement: at a configuration a typed program reaches that cancels `capture l H K`, `K` holds no
  `ccatch` and no `cfin` frame.
- Source: SPEC §19's "its handlers are dying, so they catch nothing", read at the capture: no
  operation is caught across a cancel or a cancel-mode finaliser.
- Scope: the context the continuation was captured in, not the cancel run it starts, so it does
  not assume the trace.
- OPEN. A context holds a `cfin` or `ccatch` frame only if an operation escaped a fired finaliser,
  or a cancel run, and was caught outside it: a whole-run fact of `FinRowsAt`'s kind. F4's `guard`
  frame makes such an escape stuck, so that FL and stuck-freedom exclude it.

**What S5's no-interception reads (unchanged by F3).**
- Its premise is a cancel of `capture l H K`, with store-keeping steps to `cancelOf l H K`. At our
  instance `capture` is `kappa`, the `κ` a catch hands at an operation its handler's tags read
  `unr`.
- At an admissible context the cancels that arise are of the capture cell's affine `κ` (`kappaC`).
  They reach `cancelOf` through the step that releases the cell, which the premise's store-keeping
  steps exclude. By round 3's reading (not machine-checked), no typed program reaches the premise
  at an admissible context, so a non-vacuity witness for the no-interception at `J₁` is not shown.
- `cancel_pfx` is stated at `cancelOf`, so the instance's traces cover the cell's cancels too.
  Restating S5's no-interception at the cell's `κ`, as F1 did S4's cancel law (`CancelCellLaw`), is
  the user's decision: raised in round 3 and not part of F3.

**The premises of `I.tier1_J₁_of_ESU`, after F3.**

| premise | status | Lean |
|---|---|---|
| `hE`: A's (E) properties at every admissible `Ξ` | **FAILS AS WRITTEN** (E7, E8, E9 under option A); the user's decision | `Inst.not_eProps_J₁`, `status_eProps_J₁` |
| `hS4`: S4 at every admissible `Ξ` | **PROVED** (at every effect context) | `I.handlerSem_J₁` |
| `hC`: S5 at every admissible `Ξ` | **RESTATED** prefix-closed (F3); **PROVED given `CancelsNoCtl`** (at every effect context): the unwind outright, `CancelsStd`'s handler half proved; `CancelsNoCtl` OPEN (F4's `guard` frame) | `I.cancellation_J₁_of`, `I.unwindOrder_J₁`, `I.cancelsNZ_J₁`, `status_cancellation_J₁` |
| `hU`: S6 at every admissible `Ξ` | OPEN: reduced to `OnlyOwnerFrees` and `NoDanglingUse` (not this unit) | `I.contUseEv_J₁_of` |
| `Accepts`, `Rejects` | PROVED | `I.accepts_J₁`, `I.rejects_J₁` |

**Readings for the user to confirm** (pending).
1. "The trace's fire step with its β-step" is read as above: the fire step's administrative steps
   (`q₀`) carry the β-step, and S5 read prefix-closed lets a run stop between them; at our instance
   the extension is exactly that step (`FireExt`). No constructor stopping a trace inside `q₀` is
   added.
2. `CancelsStd`'s handler half is proved; its `ccatch`/`cfin` half, `CancelsNoCtl`, is left to F4.
3. S5's no-interception at the cell's `κ` stays the user's (above).

**Unspent hypotheses.**
- S5's `Answers R ε`: read by no bridge, nor by `cancelsNZ_of_coreClosed`. The runner's answers are
  bounded through `R.Respects` and the platform it gives, not through `Answers`.
- `AdmEff`: read by nothing (every effect context).
- `CancelTrace`'s region `N`: read by nothing (at option A no finaliser's raise reaches `keep`).
- `FinRow`'s row: read only to show it empty.
- In `hndNZ_reach`, the program's typing is read twice: through `der_cases` (Core's relation, for the
  platform's protocol) and through `CoreClosed` (Core's derivation, for I3.c).

**Unused uniqueness/functionality results.** `det_ourInst` and `AStep1.deterministic`. Read:
`rstep_det` (in `rpath_prefix_chainPath` and the traces), `innerCatch_unique` (in
`ubind_pair_live`), `Row.find_mem` (in `hndNZ_pstep`), `plug_inj_ctx` (in the `J₄` check).

**Untranscribed in the run-up.**
- `CancelsNoCtl` at `J₁` (F4's `guard` frame).
- S5's no-interception at the cell's `κ` (the user's), and a non-vacuity witness for the
  no-interception at `J₁`.
- S5 at a set of endings other than `noFinRaise` (`superseded`, `ended` with an error); the target
  reads `noFinRaise`.

**Gate.** `lake build Targets` passes with AxiomCheck (a `#print axioms` line for each new result,
every set within `[propext, Classical.choice, Quot.sound]`) and Audit. Nothing in `Core/`, BoLo,
SPEC, the machine or the relation changed. `make gate` is the separate stage's.

**Remaining** (F4–F5, then the user's calls).
- F4: the `guard` frame, `FinRowsAt`, `CancelsNoCtl` (with it S5's no-interception at `J₁`), and
  `CfinQuiet` at `J₁` (with `AlgRel.head`'s `guard` case). F5: AT08 rejected by the continuation
  rule.
- The user's: E7–E9 against option A; S6's `OnlyOwnerFrees` and `NoDanglingUse`; S5's
  no-interception at the cell's `κ`; the readings above; the earlier rounds' open items (forcing a
  `!U C` slot, `unr` at abortive operations, `unfold`'s value, `TailLaw`, `EtaHold`,
  `RowVarKernel J₁`).

## Frame-deadness unit outcome

The unit implements decisions D1–D4 of 2026-10-08 (`FINALISERS.md`). Steps M0–M5; this section is
updated as each lands. On `tier1-effects`, not pushed.

| step | status | commits |
|---|---|---|
| M0: GhostEnd and ProbeD1 build at SPEC §25's `hndTerm` | LANDED | dc10293 |
| M1: frame deadness in the machine (SPEC §19, 0.44) | LANDED (below) | 185025b |
| M2: the typing of finalisers with effects (SPEC §27) | not started | |
| M3: S5's `pend`, the cell clause, algebraicity, no dropped error | not started | |
| M4: E7–E9 at `J₁` | not started | |
| M5: AT08 by the continuation rule | not started | |

### M1: frame deadness

**The machine** (`Paper/S3_Dynamics/Definitions.lean`).
- `κ`'s cancel branch runs `ccatch (K†[raise (0, (0, none))])`. `K†` (`Kont.dead`) is `K` without
  its handler frames and its `ccatch` frames (`Kont.DeadFrame`), so a dead frame catches nothing, a
  raise or an operation alike, and a finaliser's effects reach the nearest live instance of their
  name. `kappa`, `kappaC`, `kappaCBody`, `kappaCell` and `kappaAt` no longer take the operation's
  name.
- The cancel's state is the kept error alone, the first winning: `cancelVal err`, and
  `errNext err m j w = err.or (some (m, j, w))`. The name list `N`, `namesVal`, `Kont.hndNames` and
  the by-name suppression are gone. `[cfin-raise]` is at a name other than `0`; the new
  `[cfin-cancel]` (`Head.cfcancel`) passes a running finaliser's `cfin`, keeping the earlier error.
- SPEC §19 *Cancels* revised, with §24 and §25 updated and the changelog's 0.44 entry. The
  interpreter follows (`Support/Dynamics/Interpreter.lean`). The backend's cancel mask is removed
  (`Backend/Clos/`): the lowering keeps the first error.

**Kernel programs.** Every row of `corpus/kernel-counts.expected` but `cancel-suppressed` is
unchanged, answers and counts. `cancel-suppressed` (`prog`) leaves the compiled list: its run ends
at `raise (2, (0, ()))`, which no handler catches (`prog_run`, `prog_final`, `prog_eval`).
`cancel-reentered` (`progRe`) and `cancel-propagated` (`progOut`) join, `inr ()` at `0 0 0`. The
corpus and its goldens are unchanged.

**Core.**
- The relation's cancel state follows the machine: `errOk`, `cancelTab` and `contShare` read no
  name list, and `cancelOwed ls K` is `K†`'s cancel run at the empty error table.
- Re-proved: `ewp_cfin`, `cancel_then`, `ewp_frame_then`, `ewp_frame_plain`, `ewp_ccatch`,
  `ewp_handle`, the `κ` lemmas, and the cases of `Core/Steps.lean` and `Core/Demonic.lean`
  (`[cfin-cancel]` in unique decomposition and determinism). New: `dead_comp`, `hasHnd_dead`,
  `catches_dead`, `dead_plain`, `dead_ubindK`, `dead_hndK`.
- `then_compatC` takes the finaliser at the pure row, `[then]`'s rule since SPEC §24 (the former
  `thenA_compatC`, now without `S.Uniq`). The abortive-row rule fails under dead regions:
  `not_thenAbort_compatC` at `prog`'s `[then]` (`Core/EffCancel.lean`).
- `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD` keep their statements, and so does
  every borrow rule. BoLo's printed rules are untouched.
- The runs (`Core/EffCancel.lean`, `Steps` from any memory, and the interpreter by `decide`):
  `prog` (the dead `2` catches nothing; the error is re-raised and stops), `prog₃` (`inj₂ ()`),
  `progOut` (the error past the dead `2` to the live `2` outside), `progRe` (the region re-enters
  the site `3`; its instance there is dead, and the error reaches the live `3` outside),
  `progFinOp` (the finaliser's operation passes the dead inner `4` and the cancel's delimiter; the
  live `4` outside resumes it: `inj₁ ()`), `progNC₁` (the outer `4` cancels the finaliser's
  continuation; `[cfin-cancel]`), `progDrop`, `progKeep`.

**Targets.** `lake build Targets` passes, AxiomCheck and Audit included. No target's statement
changes. In detail:
- **S5's bridges read the dead region**: `cancel_pfx` at `K†`, which keeps `K`'s finalisers
  (`fins_dead`) and holds no handler (`hasHnd_dead`), so `noIntercept_of_core` reads
  `CancelsNoCtl` alone and no longer the labels' nonzero names. `CancelsNZ` is kept, reworked
  through `κ`'s resume branch, which holds `K` shifted (`hasHnd_shift`). `noIntercept_J₁_of` and
  `cancellation_tier1Open` keep their statements.
- **Core's `FinaliserOrder`** no longer reads `NoInterception` (`cancelOrder_at`,
  `finaliserOrder_at`, `finaliserOrder_A`, `finaliserOrder_of_route`; `status_runTyping` drops the
  premise). A strengthening.
- **The label of `[cfin-cancel]`** is `finEnd` of the kept error of the cancel that passed the frame
  (`keptErrOf`, `labelOf_cfcancel`; `labelOf_cferr` at a name other than `0`). No trace here takes
  that step: `CancelsNoCtl` excludes it, until M3's `pend`.
- **Algebraicity's simulation** relates dead regions (`deadFrame_eq`, `AlgRelK.dead`), kept errors
  under `or` (`ErrRel.or`), and steps `[cfin-cancel]` alike (`AlgRel.head`, `labelOf_start`).
  `CfinQuiet` reads as before; at a name of `0` it now covers `[cfin-cancel]`.
- **B5's simulation** renames the new step (`head_image`; `dead_mapLoc`, `deadFrame_mapLoc`,
  `or_mapLoc`, `mentionsLoc_dead`).
- **Check 4, re-checked** (FINALISERS §1.10, re-check 1). `noIntercept_needs_finRow` is retired:
  its witness's finaliser performed the operation its region's handler caught, and that handler is
  now dead. Machine-checked in its place (`finAlone_dead`, `status_finAlone_dead`): at `J₄` the run
  from the cancel's start fires the finaliser, starts it, and stops at its operation, which no frame
  catches (`p5_stuck`); that run is a cancel trace at every set of endings and every region. The
  no-interception condition's teeth are OPEN until a finaliser can raise to a live handler (M2).
- **Re-check 2.** `cancelsNZ_J₁` and `cancelsNZ_tier1Open` keep their statements (above).
- Names: the `κ` lemmas lose the unused name argument (`kappaAt_cell`, `kappaC_resume_parts`,
  `kappaC_cancel_parts`, `quiet_kappa_resume`, `isVal_kappa`, `not_isVal_kappaCell`,
  `kappaCancelShape_cancelE`), and so do `I5beta`, `OnlyOwnerFrees`, `NoDanglingUse`,
  `catchEv_cell` and `use_frees_cell`, where the name no longer occurs.
- The Audit's pins of Core's relation are recomputed: each hashes the closure of its definition,
  and the machine in that closure changed.

**The experiments** (FINALISERS §1.10, re-check 3). Every library in `lakefile.toml` rebuilt and
compared with the build after M0 and before M1a: the same 17 modules fail, each at the same first
error (in `CBPVCore`, `CBPVWorld`, `CBPVMu`, `Experiments`' `CBPVSplit`, `CoeffectsStrict`,
`FrameEnd`, `FrameTheorems`, `Grades`, `LoopBorrow`, `Optics`, `Outlives`, `Places`, `Projection`,
`Records`, `Relaxed` and `SecondClass`, and so in the libraries that import them), and every other
library builds, `GhostEnd`, `ProbeD1` and `Targets` among them.
- `GhostEnd`: `ewp_frame_plain` loses `hN`. `opTableO`'s cancel part is `cancelOwed ls' K`, and
  `ewp_then_owner` runs its finaliser at the empty table, as Core's `cancel_then` does; so
  `ewp_then_owner`, `withborR_compat` and the `withborR` chain read no abortive table of the row and
  no uniqueness of its keys (README, step 3b).
- `ProbeD1`: W's `share` follows `contShare`'s signature; statement 6 (`ThenRow`) takes the
  finaliser at the pure row, Core's rule, recorded in its README.
- `Outlives`: pinned at `b1cde24` and failing before the unit for SPEC §23's reason. Its `[then]`
  rule is chosen (Core's, rule for rule) and recorded in its README, not applied.

**The hard stop, M1.**

| check | finding |
|---|---|
| (1) a law | none changed: D1–D4 are the decided algebra, and the rules implement them |
| (2) behaviour or counts | `prog` only, exempt (D1/D3). Every other kernel row and the corpus are unchanged; the two new kernel programs are additions |
| (3) runtime block | none: `Kont.dead` removes frames that catch nothing, `[cfin-cancel]` gives a step, and the mask (a suppression) is gone |
| (4) rejection | none in the kernel (the typing is unchanged, option A). ProbeD1's statement 6 and Outlives's rule move to the kernel's `[then]`, as FINALISERS §1.12 records |
| (5) weakened target | none. `then_compatC` and GhostEnd's `ewp_then_owner`, internal lemmas, take their finaliser at the pure row because the relation's cancel state changed (`not_thenAbort_compatC`). `noIntercept_needs_finRow`, a non-vacuity record whose witness D1 removes, is retired with the run machine-checked in its place |

**Unspent hypotheses.** `CancelsStd`'s handler half (`CancelsNZ`) is proved and no longer read by
S5's bridges. `noIntercept_of_core` no longer reads the labels' nonzero names. `CancelTrace`'s
region `N` is read by nothing (no finaliser's raise reaches `keep` at `noFinRaise`).

**Uniqueness/functionality results.** Read by M1's new steps: `AStep1.deterministic`
(`thenCancel_runs`, for `not_thenAbort_compatC`). Read as before: `rstep_det` and
`innerCatch_unique` (the traces). Not read: `det_ourInst`; `Check 4`'s stop reads
`no_ostep_op`, not determinism.

**Untranscribed in the run-up.** The A-level `acts` and `pend`, S5's cell clause, and
`labelOf`'s use by a trace (M3); `KeptKapFree` and `CfinEnds` (M3); the separation lemma
`e7c_of_then` and SPEC §27's rules (M2); the backend's cancel code for finalisers that suspend
(M2c).

**Remaining.** M2–M5 as planned. `CancelsNoCtl` stays a hypothesis of S5's no-interception until
M3; E7c's statement and docstring are M4's (it still describes the by-name suppression).
