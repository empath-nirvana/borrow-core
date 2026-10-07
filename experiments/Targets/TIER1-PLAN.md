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

**Where the track ends.** `I.Tier1 J₁` is not proved. `J₁` is not built (piece 2), and with B2's
drive conjunct failing as written, `I.Tier1 J₁` fails for every `J₁` and `I.Tier1Core` fails as
written (`I.not_tier1`, piece 3). Seven target statements fail as written at configurations built
in Lean; their restatements are the user's decision. Pieces 5 and 6 were not run. Every result is
at Core σ=[]. `lake build Targets` passes with AxiomCheck and Audit, every new result's axioms are
within `[propext, Classical.choice, Quot.sound]`, and nothing in `Core/` changed. HEAD after the
four pieces is `56f10a8`; none of it is pushed.

| # | piece | status | verifier | commits |
|---|---|---|---|---|
| 1 | Runs at our instance, and four statement checks | LANDED; S0, S4 and `FinaliserOrder` proved given `LiveOK`/`FinAlone`; checks 1–3 break S6, S5, `AlgLaw`/`TailLaw` as written | pass | 2a84ac7, bc4218b, 12d5e83, 188d4de |
| 2 | Law 1: `J₁` and the row `∀` | STOPPED at its stop condition; Law 1 at the relation proved (`ovalW_allR`, `FLOpen`); `J₁` not built | **fail: one major finding (open, below)** | dff0a57, 335046f |
| 3 | Adequacy through platform answers and loop iterations; S2, S3 | LANDED; B2's return conjunct proved at every protocol-keeping platform; B2's drive, S2, S3, `EffSafeDrive` fail as written | pass | d53c464 |
| 4 | `FinAlone` and S6 | PARTIAL; R1–R4 teeth and the clause refusals proved; `FinAlone` and `LiveOK` fail as written; route 8.2 not accepted, not built | pass (the route's review was the agent's own) | 789506a, 56f10a8 |
| 5 | The answering class: h2, h4, the unary laws | NOT RUN | — | — |
| 6 | `BumpSim` (OQ-43) | NOT RUN | — | — |

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

### Untranscribed in the run-up

`J₁` and `J1Der`; `CfgTyped`; the bridges `noIntercept_of_core`, `unwindOrder_of_core`,
`cancellation_of_core`; `platformOf`; pieces 5 (h2, h4, the unary laws) and 6 (`BumpSim`).

### Next

1. Resolve piece 2's verifier finding: prove `WF → Row.NU` at `AdmEff`, and correct Status.lean's
   S1 and `Tier1Core` rows.
2. Bring the decisions above to the user. Rows-to-`Ξ` comes first: it unblocks S2, S3 and `LiveOK`.
3. Piece 5 at `tier1Open` (h2, h4 through the comodel); it does not wait on `J₁` except where a
   program is a handler at the top.
4. Piece 6 (`BumpSim`), independent of the rest.
