# Targets: the effect calculus's end state, stated

This file says what "done" means for the effect calculus. "Done" is one proposition,
`EndStateAt J₂ W Adm RF` (§1.0), proved at a **named** typing system `J₂` and a **named** world
`W`, together with the audit of `W`'s definition (§4.4). Every other target in this file is one
of these:

- a conjunct of done or of the tier-1 milestone `Tier1End`;
- a named part of a conjunct, or a restricted instance of one;
- a corollary of done;
- a target **beside done**: stated at the same `J₂` and `W`, available, and not required (the
  freeze binder, the every-type conservativity, exactly-once release under location reuse);
- a binary or cross-language target outside the first pass.

For each target the file gives:

- the theorem, informally;
- the definitions it needs, over Core's existing syntax and semantics wherever they exist;
- its Lean statement as a `def … : Prop`, with every hypothesis explicit;
- the literature statement it follows, quoted;
- what existing Lean proves, at which world, and the restricted instance to prove now;
- why its hypotheses are met by real programs;
- for binary and cross-language targets, whether it is in the first pass.

It is the end state, not a plan, and it proves nothing. The Lean is in `experiments/Targets`:
every `def` below, the restricted instances of §9, and every conjunct's status in
`Targets/Status.lean` (§1.6). Where the Lean departs from a definition printed here, the
definition below is the corrected one and §Corrections says what changed.

A few targets are **named-only**: their statement needs a definition this design does not give
(a binary world, the backend's fuel-parametric stage interpreter, OQ-57's closing accounting).
Each is specified in prose with the missing definition named, recorded in `Status.lean` as OPEN,
and excluded from the elaboration check. Every other target is a `def … : Prop` that
elaborates.

**Contents.**
§0 conventions · §1 the end state and the architecture · §2 definitions ·
§3 the four top-level theorems · §4 the proof device and the laws of W ·
§5 the interaction interface I1–I5 · §6 the other properties ·
§7 the survey's A1–A7 and T0–T9 · §8 the survey's seventeen programs ·
§9 what to prove now · §10 what this design leaves open · corrections · unresolved review
findings · builder's notes · sources.

---

## 0. Conventions

**Status words** are the notebook's: *stated*, *evidence*, *proved at σ=[]*, *proved at W*,
*blocked*, *open*. `Status.lean` uses four: **PROVED**, **PROVED AT σ=[]**,
**PROVED AT A RESTRICTION** (the restriction named), **OPEN**.

**Worlds.** Every target names the world it is about.

| tag | meaning |
|---|---|
| [prog] | runs and typing only: the machine, a typing judgment, a platform. No semantic world. |
| [W] | about the world `M : SemWorld` of `EndStateAt J M …` (§1.3). W is not built here; it enters only as the `M` of `EndStateAt`, with every [W] conjunct at that same `M`. Done takes `M := W`, a named definition. |
| [Core σ=[]] | the instance `coreW` (§1.4): Core's relation `vC`/`cC` over `wpTS`/`wpG`/`ewpTS`. |
| [W₂] | a binary world. Named only, for out-of-pass targets. |
| [PAPER], [SIB], [GE] | as in the brief: paper-layer encodings, EffModelRel, GhostEnd relations. A GhostEnd theorem stated at Core's `cC`/`ewpTS` is [Core σ=[]]. |

**Names.** **T1** is the Soundness theorem (§3). **R-T1** is the lexical stop, the conjunct of
`wpG` at `Core/EffDefs.lean:40` (the name 05b uses). **Survey T1** is the survey's capture
lemma (§7).

**Entry layout.** Each target has parts (a)–(g):

- **(a)** the statement, informally;
- **(b)** the definitions it uses (D-numbers refer to §2);
- **(c)** the Lean `def`;
- **(d)** the literature shape, quoted from the primary source;
- **(e)** existing Lean and its world, and the restricted instance to prove now;
- **(f)** non-vacuity;
- **(g)** the pass mark.

**The rules, as applied here.**

- **Nothing breaks the borrow calculus.** The end state states the borrow guarantees for
  effectful programs: every-run safety, empty memory, exclusivity, lifetimes, exactly-once
  release. Where W must change BoLo (the world, the wp's stop condition, the relation at rows),
  the change is a field of `SemWorld`. What it must satisfy is a conjunct of the end state, never
  an assumption.
- **Multi-shot is ignored** (decision 63). The end state's typing pin is the **unr-free
  fragment**: `ExtendsNU` (§1.2) asks the typing system to extend `CDerivesNU`, Core's rules with
  no `[perform]`, `[let]`, `[then]`, `[sub]` or `[handle]` at a row holding a resuming `unr`
  operation (`Row.NU`). Every [W] law that reads a row or an entry is stated at `Row.NU` rows
  or non-`unr` entries, so W is unconstrained at resuming `unr` rows and nothing at W depends on
  them. `unr` programs are covered only where they already work: tier 1 at Core σ=[]
  (`Tier1End` keeps `tier1`, which has them). The survey's multi-shot programs are dropped (§8).
- **The core is linear.** Discard is an explicit cancel. A `lin` or `aff` continuation has no
  weakening: `kTy` at `lin`/`aff` is a thunk, and no `forget` constant has a thunk type. An `unr`
  continuation, `kTy … unr = !U(…)` (`Core/EffRules.lean:980`), can be forgotten
  (`CDerives.forgetBang`, `Core/Fundamental.lean:136`), but its share is the empty resource
  (`contShare`'s `unr` conjunct, `Core/EffDefs.lean:146`), so it holds nothing. So exactly-once
  release is a target (T1, D9, I3), not a conjecture.
- **Preservation is semantic.** In Core, preservation means every wp run ends in a `TW` world,
  and `TW.inv` holds of every such world. I2 and I3 are stated in that form, extended to W (§5).
- **No step-indexing** (decision 7). This is a constraint on how W is built, checked by an audit
  of W's definition (§4.4). The audit is part of done, which is why done names its `W`.
- **Open options stay open, or say which option they constrain.** Where a target cannot be
  stated without an option of an open question, the option is a parameter of `EndStateAt`
  (`Adm` for OQ-56, the row form `RF` for OQ-13's remaining question) or a field of `SemWorld`
  (`held` for OQ-9, `payStk` for OQ-46). The typing system's outlives judgment is a field of the
  typing system (OQ-28). Where a conjunct does constrain an open question it says so: `Mono`
  constrains OQ-8; the nil slice is pinned only structurally so that OQ-9 and the stop condition
  stay open; and the lend frames at W, stated in the printed rule's shape, decide OQ-9 for (a) if
  (b) cannot give that shape (§4.2, §5 I2, §10).

---

## 1. The end state and the architecture

### 1.0 The end state

Every [W] conjunct is about the **same** world `M`, and every [prog] conjunct about the **same**
typing system `J`. That is what makes each conjunct a fixed proposition: a degenerate `M` cannot
meet one conjunct while another `M` meets the next. The laws of §4.2 bound the relation from
above at every index and at every type former, the borrow types included (`RelShape` transcribes
Core's `Imm`/`Mut` clauses, §4.2). So a containment conjunct (I1, the FL cases,
`ConservativeWB`) cannot be met by an over-approximating relation. At a row holding a resuming
`unr` operation the relation is unconstrained, and no conjunct reads it there (§0).

```lean
/-- **Every guarantee**, for the typing system `J` at the world `M`, with OQ-56's admissibility
`Adm` and the class `c` of rows a lend may span.  Tier 1 and tier 2 are this proposition at two
typing systems and two classes. -/
def Guarantees (J : TypingJ) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  -- [prog]: the program-level guarantees
  ExtendsNU J ∧ OutExtends J.out ∧ Soundness J ∧ SoundnessContracts J ∧ ReleasedOnceAll J ∧
  EffSafe J ∧ NoInterception J ∧ FinaliserOrder J ∧
  -- [W]: the proof device and the laws every W satisfies
  WLaws M ∧ FL M J ∧ Adequate M ∧
  -- [W]: the interaction interface
  I1 M ∧ I2 M J.out Adm c ∧ I3 M ∧ I5 M ∧
  -- [W]: the other properties
  LifetimeSound M J.out ∧ Exclusive M ∧ P11 M ∧ ConservativeWB M

/-- **The end state at a typing system and a world.**  The row form is safe and is the one the
typing rules use; the admissibility contains R-CLOSEDOP; the typing system holds tier 2's
spanning rules, accepts the tier-2 programs and types answering effects as borrows; and it meets
every guarantee at `M`, lends spanning any unr-free row. -/
def EndStateAt (J : TypingJ) (M : SemWorld) (Adm : OpAdm) (RF : RowForm) : Prop :=
  RowAlgSafe RF ∧ RowLink RF ∧ AdmExtends Adm ∧
  Tier2Pinned J Adm ∧ AcceptsTier2 J ∧ I4a J Adm .any ∧ Guarantees J M Adm .any

/-- Some typing system and some world meet it.  Implied by done; not done (below). -/
def EndState (Adm : OpAdm) (RF : RowForm) : Prop := ∃ J M, EndStateAt J M Adm RF

/-- **Tier 1 at σ = []**: every guarantee for Core's typing at Core's relation, lends spanning
abortive rows only. -/
def Tier1End : Prop :=
  RowAlgSafe orowRF ∧ RowLink orowRF ∧ WBCore ∧ I4a tier1 admClosedOp .abortive ∧
  Guarantees tier1 coreW admClosedOp .abortive
```

**Done.** Done is `EndStateAt J₂ W Adm RF`, at the `Adm` that OQ-56 settles and the `RF` that
OQ-13's remaining question settles (§10), where:

- `W : SemWorld` is a **named definition**, the built world;
- `J₂ : TypingJ` is the kernel's tier-2 judgment, a named definition: its unr-free fragment if
  the kernel keeps `unr` (decision 63: "on friction, restrict or remove the `unr` qualifier");
- `audit_W` passes: the `run_meta` audit of `W`'s definition for step indices (§4.4).

`Status.lean` records done as PROVED only when both `theorem endState_W : EndStateAt J₂ W Adm RF`
and `audit_W` exist and pass. `EndState` (the existential) follows from done and is not done:
decision 7 constrains how W is defined, and an existential witness has no definition to audit.
A W with a step index hidden in `Stk` and a relation defined by recursion on it could meet every
law at σ ≠ [], so the law statements alone cannot carry decision 7.

`Guarantees` holds no binary or cross-language target. T2 (Laws), T3 (Abstraction), T4
(Lowering), I4.b and I4.c are stated in §3 and §5 and are outside the first pass (§9). `WBCore`
is tier 1's well-bracketing (P14.a), a fact about Core's `wpG`, so it is a conjunct of
`Tier1End` only.

**Beside done.** These are stated at the same `J₂` and `W`, recorded in `Status.lean` (OPEN until
proved), and are not conjuncts of done. Each is either something the notebook or the survey
names as a hypothesis or an open problem, or a statement that needs a construction an open
question leaves undecided (OQ-1, OQ-43, OQ-50, OQ-57). §10 asks the user whether the first two
should move into done.

| target | what it adds | why it is not in done |
|---|---|---|
| `FreezeBinder W act`, `BinderMachine` at block-affine permutations (§5 I2.c) | the binder reading of freeze | the notebook lists the binder's unifications as "hypotheses to check"; the brief asks I2 to make the reading *available*. Its lifetime half carries Restrat's `not_vDenNatural` risk |
| `EndStateBinder` | `EndStateAt` together with the two above | the named strengthening, for when the binder is proved |
| `Conservative W` (§6 P14) | Core-valid values stay valid at every type | A7 in full; the survey's §6 calls it open; the notebook's P14 statement is the class-restricted `ConservativeWB`, which is in done |
| `ReleasedOnceReuse J₂` (D9) | exactly-once release on runs that reuse locations | needs `BinderMachine` at block-affine permutations (OQ-43 (b)) |
| `CancelCloses` (named-only, §5 I3) | a cancel ends every lend the continuation holds, at W | its statement needs OQ-57's closing accounting |
| P8.b (named-only, §6) | each continuation used as its qualifier says | needs OQ-50's observation of use |
| `I4Typing J₂` (§5 I4) | the control form of an answering effect types its borrow form | the typing half of OQ-1 |

```lean
/-- The end state with the freeze binder. -/
def EndStateBinder (J : TypingJ) (M : SemWorld) (act : StkAct M) (Adm : OpAdm) (RF : RowForm) :
    Prop :=
  EndStateAt J M Adm RF ∧ FreezeBinder M act ∧ BinderMachine
```

**Corollaries.** The interface's program-level readings are named, and follow from done:

```lean
/-- A closed program at a data answer that the typing system types and every platform runs
safely to the end. -/
def TypedSound (J : TypingJ) (e : Expr) (A : VTy) : Prop :=
  J.closed e (.ret A) ∧ ∀ P : Platform, P.Respects → SafeRuns P A e ∧ Terminates P A e

/-- **I1 at the program level**: suspensions stored in a cell, moved, and then cancelled
(`storeCancel`) or resumed (`at17`). -/
def I1Prog (J : TypingJ) : Prop := TypedSound J storeCancel .unit ∧ TypedSound J at17 Flag

/-- **I2 at the program level**: lends spanning a once-resuming operation (`at02`, `at04`) and an
affine one whose continuation is cancelled (`at12`). -/
def I2Prog (J : TypingJ) : Prop :=
  TypedSound J at02 Flag ∧ TypedSound J at04 (.tensor Flag Flag) ∧ TypedSound J at12 Flag
```

`i1Prog_of_endState : EndStateAt J M Adm RF → I1Prog J` (from `ExtendsNU`, `AcceptsTier2` and
`Soundness`; `storeCancel` is unr-free) and `i2Prog_of_endState` are corollaries. `Status.lean`
records them as such, not as conjuncts.

### 1.1 Three layers

1. **Program level [prog].** The four top-level theorems and the typing pins live here:
   Soundness, Laws, Abstraction, Lowering, `Tier2Pinned`, `AcceptsTier2`. They mention the
   machine (`Head`, `Step1`, `Steps`), a typing system `J` (§1.2), and a platform `P` (a
   comodel, D5). They mention no world.
2. **The proof device [W].** The fundamental lemma `FL M J` and adequacy `Adequate M`, at the
   end state's `M`.
   - `SoundnessOfFL`: `FL M J → Adequate M → Soundness J`. Soundness is a corollary of FL.
   - `AdequateOfLaws`: adequacy follows from the laws of §4.2.
   - So at W, FL is the only hard theorem Soundness needs.
3. **The interaction interface [W].** I1–I5, P9, P10, P11 and P14 at the same `M`: the facts
   about suspension that FL's effect cases are made of. Each has the program-level corollary of
   §1.0 or §5.

### 1.2 The typing parameter

A typing system is a judgment with a **row context**: the row variables in scope, each with the
constraint it carries. Row variables are in the kernel (decision 62). Core's `VTy`/`CTy` have no
row-variable former yet, so a type that mentions row variables is represented by the **family of
its closed instances**: a function from row environments to Core's types. A judgment at a row
context holds of a term and families of contexts and types; its meaning is that every admissible
instance holds.

```lean
abbrev RVar := Nat

/-- No operation the row's lookup finds is a resuming `unr` one (decision 63: the end state is
stated over the unr-free fragment).  Read through `Row.find`, as the row's protocol reads it, so a
row the platform answers (`RowLe S P.ops`, every platform operation linear) is unr-free. -/
def Row.NU (S : Row) : Prop := ∀ n i o, Row.find S n i = some o → o.abort = true ∨ o.q ≠ .unr

/-- The class of operations a row admits.  `.any` is every unr-free row. -/
inductive RowClass | abortive | resumeOnce | any
def RowClass.Admits : RowClass → Row → Prop
  | .abortive,   S => ∀ o ∈ S, o.abort = true
  | .resumeOnce, S => ∀ o ∈ S, o.abort = true ∨ o.q = .lin
  | .any,        S => S.NU

/-- The constraint a row variable carries: the class of its operations, and an admissibility
condition on each operation (OQ-56's question, at a row variable). -/
structure RowCon where
  cls : RowClass
  adm : OpSig → Prop

abbrev RowCtx := List (RVar × RowCon)
/-- A row environment: each row variable is a closed row. -/
abbrev RowEnv := RVar → Row
def RowCtx.Models (Θ : RowCtx) (η : RowEnv) : Prop :=
  ∀ ρ c, (ρ, c) ∈ Θ → c.cls.Admits (η ρ) ∧ ∀ o ∈ η ρ, c.adm o

/-- The outlives judgments a typing system consults: `Δ ⊢ A ⊐ @a` (`lt`) and `Δ ⊢ A ⊒ @a`
(`le`).  Core's are `VOutlives` and `VOutlivesLe` (`Core/Types.lean:1755,1761`); neither has a
rule at `U C`, and whether tier 2 adds one is OQ-28. -/
structure OutJ where
  lt : LifeCtx → Lifetime.Life → VTy → Prop
  le : LifeCtx → Lifetime.Life → VTy → Prop
def OutJ.core : OutJ := ⟨VOutlives, VOutlivesLe⟩
/-- It extends Core's, and `⊐` gives `⊒` (`VOutlives.toLe`). -/
def OutExtends (O : OutJ) : Prop :=
  (∀ Δ a A, VOutlives Δ a A → O.lt Δ a A) ∧ (∀ Δ a A, VOutlivesLe Δ a A → O.le Δ a A) ∧
  (∀ Δ a A, O.lt Δ a A → O.le Δ a A)

/-- A judgment `Θ; Δ; Γ ⊢ e : j`, with `Γ` and `j` families over the row environment. -/
abbrev Judgment := RowCtx → LifeCtx → (RowEnv → Ctx VTy) → Expr → (RowEnv → Jdg) → Prop

/-- **A typing system**: a judgment, and the outlives judgments its rules consult.  Every rule
transcription (`RC_*`, `SpanRule*`) reads `J.out` wherever Core's rule reads `VOutlives` or
`VOutlivesLe`, so P9 (`LifetimeSound M J.out`) certifies exactly the outlives rules the typing
system uses. -/
structure TypingJ where
  der : Judgment
  out : OutJ
instance : CoeFun TypingJ (fun _ => Judgment) := ⟨TypingJ.der⟩

/-- A judgment with no row variable. -/
def TypingJ.at (J : TypingJ) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  J [] Δ (fun _ => Γ) e (fun _ => j)
/-- A closed program at a computation type. -/
def TypingJ.closed (J : TypingJ) (e : Expr) (C : CTy) : Prop := J.at LifeCtx.empty [] e (.comp C)

/-- **Tier 1**: Core's `CDerives` (`Core/Fundamental.lean:60`) at every admissible instance, at
Core's outlives judgments.  It has the `unr` rules, and is used only at Core σ=[]. -/
def tier1 : TypingJ :=
  ⟨fun Θ Δ Γ e j => ∀ η, Θ.Models η → CDerives Δ (Γ η) e (j η), OutJ.core⟩
```

**What the instance reading commits to.** It reads row polymorphism as prenex: a judgment with
row variables means all its admissible closed instances, on the same erased term. That is what
decision 62 together with D57 (rank-2 row polymorphism, "out of scope", read as "not now") and
F3 ("Higher-order code is served by specialisation at the callback's computation type",
`docs/effects-state/04-decisions.md` §7) ask for. The kernel's syntactic rules map into it because
substitution is a homomorphism of the row algebra: that is the third clause of Yoshioka et al.'s
Def. 3.5, which T0 states, and `RowLink` (D2) says that the row form's substitution, `⊙`, `(n)↑`
and `<` are the environment update, `++`, `Row.ofEff` and `RowLe` that the typing rules use. If
rank-n row polymorphism is ever added, a row variable must denote a semantic protocol table at W,
not a closed row (the quantification is impredicative), and `RowEnv` changes with it. §10 records
this.

**`J` extends Core's typing, as a rule system, without resuming `unr` operations.** A derivation
cannot be inspected for the rules it used (`CDerives` is a `Prop`), so restricting `unr` takes a
restricted copy of the rules:

```lean
/-- **Core's rules without resuming `unr` operations.**  `CDerives`'s constructors
(`Core/Fundamental.lean:60-375`) verbatim, with the premise `Row.NU` added at five of them:
`effPerform` (on `S`), `effLet` and `effThen` (on `S`), `effSub` (on the target row `S'`), and
`effHandle` (on `Row.ofEff n E 0 ++ S`).  Every `CDerivesNU` derivation is a `CDerives` one
(`CDerivesNU.toCDerives`). -/
inductive CDerivesNU : LifeCtx → Ctx VTy → Expr → Jdg → Prop
  -- builder transcription, as the docstring says

def tier1NU : TypingJ :=
  ⟨fun Θ Δ Γ e j => ∀ η, Θ.Models η → CDerivesNU Δ (Γ η) e (j η), OutJ.core⟩

def Tier1Sub (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, tier1 Θ Δ Γ e j → J Θ Δ Γ e j
def Tier1SubNU (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, tier1NU Θ Δ Γ e j → J Θ Δ Γ e j

/-- `J` is closed under every rule of `CDerives` that has a derivation premise or reads an
outlives judgment, at every row context, with types and contexts as families, the side conditions
at every admissible instance, every outlives judgment read as `J.out`, and the five effect rules
`CDerivesNU` restricts asked their row predicate `R` (`Row.NU` for the end state, `fun _ => True`
for the full rule set).  One conjunct per constructor (list below). -/
def RulesClosed (J : TypingJ) (R : Row → Prop) : Prop :=
  RC_tensorI J ∧ RC_sumI₁ J ∧ RC_sumI₂ J ∧ RC_thunkF J ∧ RC_thunkV J ∧ RC_ret J ∧ RC_bind J ∧
  RC_lam J ∧ RC_app J ∧ RC_withI J ∧ RC_proj₁ J ∧ RC_proj₂ J ∧ RC_unitE J ∧ RC_tensorE J ∧
  RC_sumE J ∧ RC_zeroE J ∧ RC_allI J ∧ RC_allE J ∧ RC_bangThunkF J ∧ RC_bangThunkV J ∧
  RC_bangE J ∧ RC_boxI J ∧ RC_boxE J ∧ RC_immSub J ∧ RC_mutSub J ∧ RC_withbor1U J ∧
  RC_withbor2U J ∧ RC_withbor3U J ∧ RC_sliceBorrowMU J ∧ RC_sliceBorrowIU J ∧ RC_lolliE J ∧
  RC_allEV J ∧ RC_ofRet J ∧ RC_roll J ∧ RC_unroll J ∧ RC_nuIn J ∧ RC_nuOut J ∧ RC_effSub J R ∧
  RC_effPerform J R ∧ RC_effRaise J ∧ RC_effLet J R ∧ RC_effThen J R ∧ RC_effHandle J R ∧
  -- premise-free, with an outlives side condition
  RC_withbor2 J ∧ RC_sliceBorrowM J ∧ RC_sliceBorrowI J ∧ RC_withloadU J ∧ RC_foldImm J

def Extends (J : TypingJ) : Prop := Tier1Sub J ∧ RulesClosed J (fun _ => True)
/-- **The end state's pin**: `J` extends Core's unr-free rules and is closed under them. -/
def ExtendsNU (J : TypingJ) : Prop := Tier1SubNU J ∧ RulesClosed J Row.NU
```

Each `RC_r` is the constructor `r`'s statement with every `CDerives Δ Γ e j` replaced by
`J Θ Δ Γ e j`, every type and context argument a family over `RowEnv`, every side condition
required at every `η` with `Θ.Models η`, and every outlives judgment read as `J.out`:
`VOutlives` as `J.out.lt`, `VOutlivesLe` as `J.out.le`, `CtxOutlives` as `CtxOutlivesJ J.out`
(`Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → J.out.lt Δ a s.ty`), and `S.Unwind x` as
`Row.UnwindJ J.out x S` (`Row.Unwind`, `Core/EffBorrow.lean:133`, with its `VOutlives` read as
`J.out.lt`). The builder writes them by transcription; three of them, written out, fix the
pattern:

```lean
def RC_effLet (J : TypingJ) (R : Row → Prop) : Prop :=
  ∀ Θ Δ (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) M N (A B : RowEnv → VTy) (S : RowEnv → Row),
    (∀ η, Θ.Models η → R (S η)) →
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    (∀ η, Θ.Models η → (S η).Weak → (Γ₂ η).Drops) →
    (∀ η, Θ.Models η → (S η).Unr → Persistent (Γ₂ η)) →
    J Θ Δ Γ₁ M (fun η => .comp (CTy.effOf (S η) (A η))) →
    J Θ Δ (fun η => ⟨A η, true⟩ :: Γ₂ η) N (fun η => .comp (CTy.effOf (S η) (B η))) →
    J Θ Δ Γ (.app (.val (.lam N)) M) (fun η => .comp (CTy.effOf (S η) (B η)))

def RC_effHandle (J : TypingJ) (R : Row → Prop) : Prop :=
  ∀ Θ Δ (Γ Γ₁ Γ₂ Γr Γc : RowEnv → Ctx VTy) e (S : RowEnv → Row) (E : RowEnv → List (Qual × VTy × VTy))
    (n : UInt32) (A R' : RowEnv → VTy) (ir ic : Nat),
    (∀ η, Θ.Models η → R (Row.ofEff n (E η) 0 ++ S η)) →
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η) ∧ Ctx.SplitP (Γ₁ η) (Γr η) (Γc η) ∧
      Ctx.SoloP (Γr η) ir (retTy (S η) (A η) (R' η)) ∧ Ctx.SoloP (Γc η) ic (clausesTy (S η) (R' η) (E η)) ∧
      (∀ o ∈ S η, o.n ≠ n) ∧ (E η).length ≤ 2 ^ 32) →
    n ≠ 0 →
    J Θ Δ Γ₂ e (fun η => .comp (CTy.effOf (Row.ofEff n (E η) 0 ++ S η) (A η))) →
    J Θ Δ Γ (hndTerm n ir ic e) (fun η => .comp (CTy.effOf (S η) (R' η)))

def RC_boxI (J : TypingJ) : Prop :=
  ∀ Θ Δ (Γ : RowEnv → Ctx VTy) e (a : Lifetime.Life) (A : RowEnv → VTy),
    (∀ η, Θ.Models η → CtxOutlivesJ J.out Δ (Γ η) a) →
    J Θ Δ Γ e (fun η => .val (A η)) → J Θ Δ Γ e (fun η => .val (.box a (A η)))
```

`tier1` meets `Extends` and `ExtendsNU` (pointwise from `CDerives`, and `CDerivesNU.toCDerives`).
The kernel's tier-2 judgment, an inductive extending `CDerivesNU`, meets `ExtendsNU` by
construction. Without `RulesClosed`, a `J` could hold tier 1 and the spanning constants yet type
nothing that uses them. Without the `J.out` reading, `J` could store a continuation by an outlives
rule that P9 never certifies.

**What the `unr` restriction costs.** `CDerivesNU` copies `CDerives`'s constructors into Targets.
The alternative is the kernel change decision 63 allows without asking ("restrict or remove the
`unr` qualifier"); after it, `CDerivesNU` is `CDerives` and the copy is deleted. §10 records this.
The five rules are the ones whose W case reads the protocol, the share at an `unr` entry
included, at the row: a frame through the row's stops (`[let]`, `[then]`), a stop at the row
(`[perform]`), a row grown to one with an `unr` entry (`[sub]`, which needs the share monotone in
the table), and forwarding through a handler (`[handle]`). `[raise]` stops at an abortive entry
and reads no share. A context variable, a thunk, a `[raise]` or an unrolled loop at an `unr` row
is still typed, and FL's structural cases at it read nothing of `unr`: no unr-free context runs
such a computation without one of the five restricted rules, so W may make its relation at such a
row anything the structural cases accept.

**Tier 2.** "Tier 1 and tier 2 are the same theorem over different typing rules" is literal:
`Tier1End` is `Guarantees tier1 coreW admClosedOp .abortive`, and `EndStateAt` asks
`Guarantees J M Adm .any` at a `J` that is pinned to tier 2 by `Tier2Pinned` and `AcceptsTier2`
(§5, I2; §8). The class is the second difference: tier 1's lends span abortive rows only.

### 1.3 The world W, abstractly

The signed-off structure says what W is: one Kripke world `W = (ρ, ls, σ)`, that is, resource ×
record list × lend stack. Effects change three things in BoLo:

- the world;
- the wp's stop condition;
- the relation at effect rows.

`SemWorld` has exactly those as fields, and two more: `held`, which says what the suspended
computations at an index hold, and `payStk`, which says at what lend stack a cell's stored payload
is read (OQ-46). Everything else is defined from them, the way Core defines it. The relation is
mode-indexed, as Core's `vCE` is (`Core/Relation.lean:119`): `val true` is the program's
relation, and `val false` the observable view an `Imm` payload is held at, with `U` relaxed to
`True`.

```lean
/-- The index of `W = (ρ, ls, σ)`: the record list and the lend stack.  The resource `ρ` is the
argument of every `WProp`. -/
abbrev Idx (Stk : Type) := List SRec × Stk

/-- Core's protocol tables (`Core/EffDefs.lean:50,104-118`), at any index. -/
abbrev TableI (I : Type) := I → Expr → (I → Expr → WProp) → WProp
def TableI.Mono {I} (Tb : TableI I) : Prop :=
  ∀ i t (Φ Φ' : I → Expr → WProp) ρ, (∀ i e ρ, Φ i e ρ → Φ' i e ρ) → Tb i t Φ ρ → Tb i t Φ' ρ
structure OpEntI (I : Type) where
  q : Qual
  abort : Bool
  PA PB : I → Val → WProp
abbrev OpTabI (I : Type) := UInt32 → UInt32 → Option (OpEntI I)

/-- **The planned world W, abstractly.**  `coreW` (§1.4) is the instance whose lend stack has
one point. -/
structure SemWorld where
  /-- σ.  What a lend stack holds is OQ-44's question; here it is a type. -/
  Stk   : Type
  nil   : Stk
  /-- What the suspended computations at an index hold: their open 6.64 frames and their
  tagged records.  Where they are kept is OQ-9's question; under its option (b) nothing is
  held at any index. -/
  held  : Idx Stk → List FrameRec × List SRec
  /-- The configurations W reaches at an index: the full resource and the open 6.64 frames
  visible to the running computation. -/
  Fam   : WRes → List FrameRec → Idx Stk → Prop
  /-- The stop condition: entry frames/index, exit frames/index, final term.  Core's is R-T1
  (`Core/EffDefs.lean:40`). -/
  Stop  : List FrameRec × Idx Stk → List FrameRec × Idx Stk → Expr → Prop
  /-- The Kripke order on indices, relative to a resource (Core's `Ext`,
  `Core/FrameRecords.lean:172`). -/
  Ext   : Idx Stk → Idx Stk → WRes → Prop
  /-- What a stop at a resuming operation owes its continuation (Core's `contShare`,
  `Core/EffDefs.lean:144`). -/
  share : OpTabI (Idx Stk) → OpEntI (Idx Stk) → UInt32 → Idx Stk → Kont →
            (Idx Stk → Expr → WProp) → WProp
  /-- The lend stack at which a cell at lifetime `b` reads its stored payload, given the stack of
  the index the cell is read at (OQ-46): option (a) keeps the entries longer-lived than `b`, as
  `ptoMutS` keeps the records (`Core/Relation.lean:43-47`); option (b) is `nil`. -/
  payStk : Life → Stk → Stk
  /-- The relation, mode-indexed as `vCE` is. -/
  val   : Bool → VTy → Idx Stk → LSub → Val → WProp
  comp  : CTy → Idx Stk → LSub → Expr → WProp
```

**Derived definitions.** Each is a transcription of Core's, with `TW … ∧ Tagged …` replaced by
`M.Fam`, R-T1 by `M.Stop`, and a record list `ls` by an index `i`.

```lean
/-- `ℓ ↦ M_α P` at W: `ptoMutS` (`Core/Relation.lean:43`) with the stored predicate read at the
index `(ls₀, M.payStk b i.2)`, `ls₀` the records of `i.1` strictly longer-lived than the cell. -/
def ptoMutSW (M : SemWorld) (l : Loc) (α : Life) (i : Idx M.Stk) (P : Idx M.Stk → Val → WProp) :
    WProp := fun ρ =>
  ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b) (Q : Val → SPropS Loc Val b)
    (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P (ls₀, M.payStk b i.2) ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ i.1 ∧ x.2 ⊐ b)) ∧ ∀ i' u' σ', P i' u' σ' → σ'.InStratum b

/-- `ℓ ↦ I_α P` at W: `ptoImmS` (`Core/Relation.lean:51`) the same way, at the cell's `⊓β̄`. -/
def ptoImmSW (M : SemWorld) (l : Loc) (α : Life) (i : Idx M.Stk) (P : Idx M.Stk → Val → WProp) :
    WProp := fun ρ =>
  ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P (ls₀, M.payStk s.meet i.2) u σ ∧ α ⊑ s.meet ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ i.1 ∧ x.2 ⊐ s.meet)
```

```lean
/-- W's one-run wp: `wpG` (`Core/EffDefs.lean:27`) over `M.Fam`, ending under `M.Stop`. -/
def wpGW (M : SemWorld) (i : Idx M.Stk) (e : Expr) (Q : Idx M.Stk → Expr → WProp) : WProp :=
  fun ρ => ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    M.Fam fρ ps i → ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (t : Expr) (μ μ' : Heap) (ps' : List FrameRec)
      (i' : Idx M.Stk),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧ (∃ k', ARun A k μ e k' μ' t) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧ NoOwn ρp ∧
      M.Fam fρ'p ps' i' ∧ M.Stop (ps, i) (ps', i') t ∧ Q i' t ρ'

def valPostI {I} (Q : I → Val → WProp) : I → Expr → WProp :=
  fun i t ρ => ∃ v : Val, t = .val v ∧ Q i v ρ

/-- W's effectful wp: the least fixed point of "run to a value in `Q` or to a stop `Tb` admits",
written in `Prop` as `ewpTS` is (`Core/EffDefs.lean:68-75`). -/
def ewpW (M : SemWorld) (i : Idx M.Stk) (e : Expr) (Tb : TableI (Idx M.Stk))
    (Q : Idx M.Stk → Val → WProp) : WProp := fun ρ =>
  ∀ P : Idx M.Stk → Expr → WProp,
    (∀ i e ρ, wpGW M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨ Tb i' t P ρ') ρ → P i e ρ) →
    P i e ρ

/-- The protocol of an operation table at W: `opTable` (`Core/EffDefs.lean:157`) with `M.share`
for `contShare`. -/
def opTabW (M : SemWorld) (T : OpTabI (Idx M.Stk)) : TableI (Idx M.Stk) := fun i t Φ =>
  BoLo.or
    (ex fun K => ex fun n => ex fun j => ex fun v => ex fun en =>
      ⌜t = K.plug (performE (.val (opPayload n j v))) ∧ K.HasHnd n = false ∧
        T n j = some en ∧ en.abort = false⌝ ⋆ (en.PA i v ⋆ M.share T en n i K Φ))
    (ex fun K => ex fun n => ex fun j => ex fun v => ex fun en =>
      ⌜t = K.plug (raiseE (.val (opPayload n j v))) ∧ K.Catches n = false ∧
        T n j = some en ∧ en.abort = true⌝ ⋆
        ((fun ρ => en.PA i v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ))

/-- The error a cancel carries, and the table of a cancel run (`errOk`, `cancelTab`,
`Core/EffDefs.lean:120-136`), at any index.  `Cl` is a condition on the index the cancel ends at
(I3.a's closing clause); Core's `cancelTab` is `cancelTabW T N (fun _ => True)`. -/
def errOkW {I} (T : OpTabI I) (N : List UInt32) (i : I) : Option Val → WProp
  | none => emp
  | some E => ex fun m => ex fun j => ex fun w => ex fun en =>
      ⌜E = opPayload m j w ∧ m ∉ N ∧ T m j = some en ∧ en.abort = true⌝ ⋆
        fun ρ => en.PA i w ρ ∧ NoOwn ρ
def cancelTabW {I} (T : OpTabI I) (N : List UInt32) (Cl : I → Prop) : TableI I := fun i t _ =>
  ex fun K => ex fun err =>
    ⌜t = K.plug (raiseE (.val (cancelVal N err))) ∧ K.Catches 0 = false ∧ Cl i⌝ ⋆
      (errOkW T N i err ⋆ fun ρ => NoOwn ρ)

/-- An operation's entry at W, and the table of a row (`OpSig.ent`, `Row.tab`,
`Core/EffRules.lean:43-47`). -/
def entW (M : SemWorld) (δ : LSub) (o : OpSig) : OpEntI (Idx M.Stk) :=
  ⟨o.q, o.abort, fun i v => M.val true o.A i δ v, fun i v => M.val true o.B i δ v⟩
def rowTabW (M : SemWorld) (S : Row) (δ : LSub) : OpTabI (Idx M.Stk) :=
  fun n j => (Row.find S n j).map (entW M δ)

/-- `𝒢⟦Γ⟧` and `Δ; Γ ⊨ e : j` at W at closed rows: `gDenC`, `SemC` (`Core/Relation.lean:218-232`,
`Core/Fundamental.lean:429`) with `M.val`/`M.comp`. -/
def gSepW (M : SemWorld) (i : Idx M.Stk) (δ : LSub) : Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ => if s.live then M.val true s.ty i δ v ⋆ gSepW M i δ Γ γ else gSepW M i δ Γ γ
def gDenW (M : SemWorld) (i : Idx M.Stk) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepW M i δ Γ γ
/-- `Δ; Γ ⊨ e : C` at W (corrected, §Corrections C1). -/
def SemWC (M : SemWorld) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ δ γ (i : Idx M.Stk) ρ, Δ.Models δ → gDenW M i δ Γ γ ρ → M.comp C i δ (substAll γ e) ρ
def SemW₀ (M : SemWorld) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .comp C => SemWC M Δ Γ e C
  | .val A => SemWC M Δ Γ e (.ret A)

/-- At a row context: every admissible instance. -/
def SemW (M : SemWorld) (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr)
    (j : RowEnv → Jdg) : Prop :=
  ∀ η, Θ.Models η → SemW₀ M Δ (Γ η) e (j η)
```

**What each field leaves open, and what constrains it.** The end state constrains each field by
the laws of §4.2 and the interface of §5. Most of them hold under every option of the open
question inside the field. These constrain an open question, or may, and say which:

- `Mono` (§4.2) excludes any placement of OQ-8's future-world quantifier under which W's relation
  is not monotone along `M.Ext`;
- the nil slice is pinned only structurally (`SliceShape`), with Core embedding into W rather than
  equal to it. An equivalence at σ = [] at a type a tier-2 value can inhabit would decide OQ-9
  and the stop condition (§4.2);
- the lend frames at W (`MutFrameW`, `ImmFrameW`, §5 I2) are stated in the printed rule's shape
  with stops; if OQ-9 (b) cannot give that shape, they decide OQ-9 for (a).

| field | Core (`coreW`) | the open question inside it |
|---|---|---|
| `Stk` | `Unit` | OQ-44 (what σ holds), OQ-57 (a closing-obligation list beside W) |
| `held` | `([], [])` | OQ-9 (lends carried open, or ghost-ended and re-lent), OQ-44 |
| `Fam` | `TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls` | OQ-9; bounded above by `Arises` (I2) |
| `Stop` | R-T1: `ps′ ≡ ps ∧ ls′ ≡ ls` | OQ-9, OQ-10, the stop condition at resuming rows; bounded above by `StopVisible` (I2) |
| `Ext` | `Ext` | OQ-8 (stack extension in the order, or at binder clauses); constrained by `Mono` |
| `share` | `contShare` | OQ-8 (Kripke at the share and `KapRel`, or at binder clauses); bounded above by `ShareResume` (I2) and `ShareCancel` (I3) at non-`unr` entries |
| `payStk` | `fun _ _ => ()` | OQ-46 (the stack a stored payload is read at) |
| `val`, `comp` | `vCE none`, `cC` | OQ-8; bounded by `RelLaws`, `DataVals`, `EffInterp`, `AdequateEvery`, `LifetimeSound` at every former and index, unconstrained at resuming `unr` rows |

### 1.4 Core is the σ = [] instance

```lean
/-- Core's relation as a world whose lend stack has one point. -/
def coreW : SemWorld where
  Stk := Unit
  nil := ()
  held _ := ([], [])
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1
  Stop a b _ := (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1)
  Ext i i' ρ := Ext i.1 i'.1 ρ
  share T en n i K Φ := contShare T.down en.down n i.1 K (fun ls t => Φ (ls, ()) t)
  payStk _ _ := ()
  val b A i δ v := vCE none b A i.1 δ v
  comp C i δ e := cC C i.1 δ e
```

`T.down`/`en.down` precompose the entries' predicates with `(·, ())`. The builder's first lemmas
are the transports, each by unfolding:

- `wpGW_core : wpGW coreW (ls, ()) e Q ρ ↔ wpG ls e (fun ls' t => Q (ls', ()) t) ρ`;
- `ewpW_core` with `ewpTS`;
- `opTabW_core` with `opTable`, and `cancelTabW_core : cancelTabW T N (fun _ => True)` with
  `cancelTab`;
- `ptoMutSW_core : ptoMutSW coreW l α (ls, ()) (fun i => P i.1) = ptoMutS l α ls P`, and
  `ptoImmSW_core` with `ptoImmS`.

### 1.5 How the conjuncts compose

| conjunct | follows from, or is used by |
|---|---|
| `Soundness J` | `SoundnessOfFL`: `FL M J` + `Adequate M`; `Adequate M` from §4.2 by `AdequateOfLaws` |
| `SoundnessContracts J` | `FL M J` + `ExtPre M` + `Conservative M` (the externs' contracts are Core's, at any type) + `Adequate M` (§Corrections C2); at row-abortive externs, `ConservativeWB M` in place of `Conservative M` |
| `ReleasedOnceAll J` | the occupancy argument of D9 alone: it holds at every `J` (§Builder's notes); its typing content is `SoundnessContracts J`'s `Final` and `Terminates` |
| `EffSafe J` | `FL M J` + `AdequateEvery M` at the empty world |
| FL's effect cases | I1 (`[handle]` hands the clause a value of `kTy`); I5 (β at resume, the frame rules at `[let]`/`[then]`); I2 (the frames at W, and the spanning rules: their FL cases `SpanBorrows` consume `Arises`, `ShareResume`, `ShareCancel`); P9 (outlives side conditions, at `J.out`); P11 (`[handle]`) |
| `SpanBorrows M J.out Adm c` (in I2) | also follows from `FL M J` + `Tier2Pinned J Adm` at `c = .any`; it is in I2 so that I2 states the spanning lends, not only FL |
| `Exclusive M` | `Arises M` by `TW.valid`, `TW.inv` |
| `ConservativeWB M` | `Mono M` + the embedding at σ = [] at row-abortive types; not from `SliceShape` alone (§4.2) |
| `HandleCompat M` | `FL M J` + `Tier1SubNU J` (it is FL's `[handle]` case at unr-free rows) |
| `AcceptsTier2 J` | `ExtendsNU J` + `Tier2Pinned J Adm` whenever `Adm` admits closed data operations (it checks the pins are not vacuous) |
| `RowAlgSafe RF ∧ RowLink RF` | T0: the safety conditions of the row form the typing rules use |
| `I1Prog J`, `I2Prog J` | corollaries of done: `AcceptsTier2`/`ExtendsNU` + `Soundness` |
| T3 Abstraction | FL₂ + Adequate₂ (binary, named-only; out of the first pass) |
| T2 Laws, T4 Lowering | binary or cross-language; out of the first pass |

### 1.6 Files, `Status.lean`, hygiene

The builder adds this library:

```toml
[[lean_lib]]
name = "Targets"
srcDir = "experiments/Targets"
roots = ["Targets"]
```

| file | contents |
|---|---|
| `Targets/Defs/Effects.lean` | D1–D4: effect contexts, rows and row contexts, `Row.NU`, the effect algebra, `RowForm` and its instances, `Kont.fins` |
| `Targets/Defs/Typing.lean` | §1.2: `OutJ`, `TypingJ`, `CDerivesNU`, `tier1`, `tier1NU`, the `RC_*` transcriptions, `Extends`, `ExtendsNU` |
| `Targets/Defs/Runs.lean` | D5–D9: `Platform`, `PStep`, `RStep`, `VTy.Data`, `DataVal`, `Final`, `DivFree`, `SafeRuns`, `Terminates`, `SafeDrive`, `StopsIn`, `PRun`, `ReleasedOnce` |
| `Targets/Defs/World.lean` | §1.3–§1.4: `SemWorld`, `ptoMutSW`/`ptoImmSW`, the derived definitions, `coreW`, the transports |
| `Targets/Defs/Binder.lean` | D11: the location and lifetime actions, `StkAct`, `BlockAffine`, `StepsIn` |
| `Targets/Defs/Ctx.lean` | D12: observations and contextual approximation (binary) |
| `Targets/Defs/Programs.lean` | D13–D14: answering implementations, `ctlForm`, `capPass`; the acceptance terms |
| `Targets/Statements/*.lean` | every conjunct as a `def … : Prop`; `Guarantees`, `EndStateAt`, `EndState`, `EndStateBinder`, `Tier1End`; the targets beside done |
| `Targets/Audit.lean` | the step-index audit (§4.4), run on `coreW` now and on `W` when it is built; the pin of Core's relation (§6 P14) |
| `Targets/Restricted/*.lean` | the proofs of §9 |
| `Targets/Status.lean` | the record below |

**`Status.lean` format.** The file opens with the definition of done and its two parts, then one
section per conjunct of `EndStateAt` and of `Guarantees`, then the targets beside done, then the
corollaries, then the named-only targets.

- **Done:** `example (J : TypingJ) (M : SemWorld) : Prop := EndStateAt J M admClosedOp orowRF`
  checks the statement elaborates. Done is recorded PROVED only when
  `theorem endState_W : EndStateAt J₂ W Adm RF` (at the named `J₂`, `W`) exists **and**
  `audit_W` passes; until then it is OPEN. `EndState` (∃) is recorded as implied by done, never as
  done.
- **Tier 1:** `theorem status_tier1End : Tier1End` closes the tier-1 milestone when every tier-1
  section is proved.
- **Each conjunct, at the end state:** OPEN until done is proved.
- **Each conjunct, at tier 1 or σ = []:** `theorem status_<id>_core : <conjunct> coreW` for a [W]
  conjunct, or `theorem status_<id>_tier1 : <conjunct> tier1` for a [prog] conjunct, recorded
  PROVED AT σ=[] or PROVED AT A RESTRICTION with the restriction in the name and the record, e.g.
  `status_soundRet_tier1_none : SoundRetAt tier1 Platform.none` or
  `status_I2_core_abortive : I2 coreW OutJ.core admClosedOp .abortive`. A conjunct whose content
  is vacuous at `coreW` (nothing is held at σ = []) is recorded PROVED AT A RESTRICTION, never
  PROVED.
- **Generic:** `theorem status_<id> : ∀ M, <laws> → <conjunct> M` where a conjunct follows from
  the laws for every world (PROVED, generic).
- **Beside done:** one section each (§1.0's table), OPEN with `example : Prop := …`, or PROVED
  AT A RESTRICTION where §9 proves one.
- **Corollaries:** `I1Prog`, `I2Prog`, P8.a; each with its derivation from done.
- **Named-only:** each by name, with its specification and the missing definition, in the
  docstring; no `example`, excluded from the elaboration check.

The file's docstring carries the table of §9.

**Hygiene.**

- There is no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or
  `implemented_by`.
- Open targets are `def`s, not theorems. Every statement this file writes as a target, the
  generic composition lemmas and the machine lemmas included, is a `def … : Prop`; its proof, when
  it exists, is a `theorem` of that `def`.
- `#print axioms` of every proved result is within `[propext, Classical.choice, Quot.sound]`.
- Build with `lake build Targets` only.
- The library imports `Core`'s modules, `Restrat` (for `Restrat.Emb`) and `GhostEnd` (for
  `ewpTS_M_antiFrameR`, the anti-frame at a resuming table). Import the `Core` modules needed, not
  the root: a scratch `import Core` against this branch's built oleans failed (`Core.Embedding`
  and `Core.Examples` both carry `CFree.eq_def`), and `import Core.EffRules` elaborated. If
  `lake build Targets` fails in an import, copy the declarations needed locally and record the
  duplicate. Location renaming is re-defined locally, because `TwoRun` does not build on main
  (`experiments/README.md` is stale on that); that is a known duplicate of `TwoRun/Rename.lean`,
  recorded here.

---

## 2. Definitions: what an effect is, mathematically

### D1. Signature, effect, row, row variable

- **Operation** (existing). `OpSig ⟨n, i, q, A, B⟩` (`Core/Types.lean:147`) is the operation `i`
  of the name `n`, `A ↠^q B`. `q ∈ {lin, aff, unr}` is the continuation's qualifier, the control
  class. The operation is abortive iff `B = 0 ∧ q ≠ lin` (`OpSig.abort`,
  `Core/EffRules.lean:40`).
- **Signature** (Plotkin–Power, Plotkin–Pretnar Def. 4.2). The operations of one name:
  `E : List (Qual × VTy × VTy)`, numbered by `i` (`Row.ofEff n E 0`, `Core/EffRules.lean:969`).
- **Effect.** A name with its signature. Names are static, one per handler site (decision 57 R3,
  checked by the elaborator). So each program fixes an **effect context**
  `Ξ : UInt32 → List (Qual × VTy × VTy)`, proper in Yoshioka et al.'s sense (Def. 5.3): one
  signature per label, its types well formed.
- **Row** (existing). `Row := List OpSig` (`Core/EffRules.lean:33`), a finite sum of operation
  entries keyed by `(n, i)`, looked up first-match (`Row.find`). A row with `Row.Uniq` is a
  finite partial map. `F_Σ A = CTy.effOf Σ A`.
- **Row variable** (decision 62). `RVar`, with the constraint it carries (`RowCon`) and the
  instance reading of §1.2.
- **Subeffecting** (existing). `[sub]` is `RowLe` (`Core/EffRules.lean:699`).

New:

```lean
abbrev EffCtx := UInt32 → List (Qual × VTy × VTy)
/-- Two rows with the same operations: equal first-match lookup. -/
def RowEq (S S' : Row) : Prop := ∀ n i, Row.find S n i = Row.find S' n i
def Row.Has (S : Row) (n i : UInt32) : Prop := (Row.find S n i).isSome
```

**The semantic object.** `F_Σ A` is read by `ewpTS` at `opTable (Row.tab Σ δ)`
(`cC_effOf`, `Core/EffRules.lean:73`): the least fixed point of "run to a value in `𝒱⟦A⟧`, or to
a stop at an operation of `Σ` owing its continuation". It is the free model of `Σ` over `𝒱⟦A⟧` in
the resource world: computation trees whose branches are runs.

### D2. The effect algebra (for T0)

Yoshioka–Sekiyama–Igarashi Def. 3.5, at our kinds. Labels are effect names, with no typelike
arguments, because an operation's types mention no row variable (OQ-61 leaves effect-recursive
signatures open). Effects carry row variables, and kinding is well-formedness under the row
variables in scope. The data and the laws are separate, so that T0 states the laws of the kernel's
algebra instead of presupposing them.

```lean
/-- An effect algebra's data. -/
structure EffAlg where
  Lab   : Type
  Eff   : Type
  Var   : Type
  /-- `Γ ⊢ ε : Eff`, `Γ` the row variables in scope. -/
  WF    : List Var → Eff → Prop
  WFLab : List Var → Lab → Prop
  comp  : Eff → Eff → Option Eff       -- ⊙, partial
  unit  : Eff                          -- 0
  lift  : Lab → Eff                    -- (L)↑
  eqv   : Eff → Eff → Prop             -- ∼
  subst : Var → Eff → Eff → Eff        -- `subst α S ε` is ε[S/α]

/-- `α ↦ S ⊢ εs : Eff`: the effects are well formed with `α` in scope, and `S` where `α` is. -/
def EffAlg.SubstOK (EA : EffAlg) (α : EA.Var) (S : EA.Eff) (εs : List EA.Eff) : Prop :=
  ∃ Γ₁ Γ₂, (∀ ε ∈ εs, EA.WF (Γ₁ ++ α :: Γ₂) ε) ∧ EA.WF Γ₁ S

/-- **Def. 3.5**: the data form an effect algebra. -/
structure EffAlg.Laws (EA : EffAlg) : Prop where
  -- first bullet: ⊙, 0 and (−)↑ preserve well-formedness; ∼ is an equivalence that preserves it
  comp_wf   : ∀ Γ ε₁ ε₂ ε, EA.WF Γ ε₁ → EA.WF Γ ε₂ → EA.comp ε₁ ε₂ = some ε → EA.WF Γ ε
  unit_wf   : ∀ Γ, EA.WF Γ EA.unit
  lift_wf   : ∀ Γ L, EA.WFLab Γ L → EA.WF Γ (EA.lift L)
  eqv_equiv : Equivalence EA.eqv
  eqv_wf    : ∀ ε₁ ε₂, EA.eqv ε₁ ε₂ → ∀ Γ, (EA.WF Γ ε₁ ↔ EA.WF Γ ε₂)
  -- second bullet: a partial monoid under ∼
  unit_r : ∀ ε, ∃ ε', EA.comp ε EA.unit = some ε' ∧ EA.eqv ε' ε
  unit_l : ∀ ε, ∃ ε', EA.comp EA.unit ε = some ε' ∧ EA.eqv ε' ε
  assoc  : ∀ ε₁ ε₂ ε₃,
    ((∃ x y, EA.comp ε₁ ε₂ = some x ∧ EA.comp x ε₃ = some y) ∨
     (∃ x y, EA.comp ε₂ ε₃ = some x ∧ EA.comp ε₁ x = some y)) →
    ∃ x y x' y', EA.comp ε₁ ε₂ = some x ∧ EA.comp x ε₃ = some y ∧
      EA.comp ε₂ ε₃ = some x' ∧ EA.comp ε₁ x' = some y' ∧ EA.eqv y y'
  -- third bullet: substitution respecting well-formedness is a homomorphism for ⊙, (−)↑, ∼
  subst_comp : ∀ α S ε₁ ε₂ ε, EA.SubstOK α S [ε₁, ε₂] → EA.comp ε₁ ε₂ = some ε →
    EA.comp (EA.subst α S ε₁) (EA.subst α S ε₂) = some (EA.subst α S ε)
  subst_lift : ∀ α S L, (∃ Γ₁ Γ₂, EA.WFLab (Γ₁ ++ α :: Γ₂) L ∧ EA.WF Γ₁ S) →
    EA.subst α S (EA.lift L) = EA.lift L
  subst_eqv : ∀ α S ε₁ ε₂, EA.SubstOK α S [ε₁, ε₂] → EA.eqv ε₁ ε₂ →
    EA.eqv (EA.subst α S ε₁) (EA.subst α S ε₂)

/-- `ε₁ < ε₂`: "`ε₁ ⊙ ε ∼ ε₂` for some `ε`". -/
def EffAlg.Sub (EA : EffAlg) (ε₁ ε₂ : EA.Eff) : Prop :=
  ∃ ε x, EA.comp ε₁ ε = some x ∧ EA.eqv x ε₂
```

`subst_lift` reads Def. 3.5's `(L)↑[S/α] = (L[S/α])↑` at labels with no variables
(`L[S/α] = L`). Def. 3.5 prints the third clause's conclusion as "ε1[S/α] ∼ ε[S/α]"; the
`ε₂` here is that clause's evident reading.

**The minimal open-row form, the restricted instance.** A closed first-match prefix and an
optional tail variable (Rémy). `⊙` is defined when the left row has no tail, or the right
row is empty, as for Yoshioka's simple rows; `∼` is equal tails and equal first-match lookup, so a
duplicate entry is shadowed as `Row.find` shadows it.

```lean
structure ORow where
  ops  : Row
  tail : Option RVar

/-- The open-row algebra at an effect context. -/
def orowAlg (Ξ : EffCtx) : EffAlg where
  Lab := {n : UInt32 // n ≠ 0 ∧ Ξ n ≠ [] ∧ (Ξ n).length ≤ 2 ^ 32}
  Eff := ORow
  Var := RVar
  WF Γ ε := (∀ ρ, ε.tail = some ρ → ρ ∈ Γ) ∧
    ∀ n i o, Row.find ε.ops n i = some o → n ≠ 0 ∧ (Ξ n)[i.toNat]? = some (o.q, o.A, o.B)
  WFLab _ _ := True
  comp ε₁ ε₂ := match ε₁.tail with
    | none => some ⟨ε₁.ops ++ ε₂.ops, ε₂.tail⟩
    | some _ => if ε₂.ops = [] ∧ ε₂.tail = none then some ε₁ else none
  unit := ⟨[], none⟩
  lift n := ⟨Row.ofEff n.1 (Ξ n.1) 0, none⟩
  eqv ε₁ ε₂ := ε₁.tail = ε₂.tail ∧ RowEq ε₁.ops ε₂.ops
  subst ρ S ε := if ε.tail = some ρ then ⟨ε.ops ++ S.ops, S.tail⟩ else ε

/-- The closed rows: the sub-algebra with no row variable. -/
def closedRowAlg (Ξ : EffCtx) : EffAlg where
  Lab := {n : UInt32 // n ≠ 0 ∧ Ξ n ≠ [] ∧ (Ξ n).length ≤ 2 ^ 32}
  Eff := Row
  Var := Empty
  WF _ S := ∀ n i o, Row.find S n i = some o → n ≠ 0 ∧ (Ξ n)[i.toNat]? = some (o.q, o.A, o.B)
  WFLab _ _ := True
  comp S S' := some (S ++ S')
  unit := []
  lift n := Row.ofEff n.1 (Ξ n.1) 0
  eqv := RowEq
  subst α _ _ := α.elim
```

Well-formedness reads a row through its first-match lookup, as `∼` does, so `∼` preserves it
(a shadowed entry is never looked up).

**The row form, and its link to the typing rules.** The typing rules (§1.2) read a row variable
by its closed instances, and their row operations are Core's closed-row ones: `[sub]` is `RowLe`
at every instance, `[handle]`'s body row is `Row.ofEff n E 0 ++ S`, and a row context's
instances are environment updates. An effect algebra says something about the kernel only if its
operations **are** those. So the end state takes the row form as a parameter (OQ-13's remaining
question: the kernel's row-variable form), with its reading as families of closed rows, and asks
the link:

```lean
/-- A row form: an effect algebra at each effect context, its labels' names, and its reading of
an effect, at an environment of its variables, as a closed row. -/
structure RowForm where
  alg  : EffCtx → EffAlg
  name : ∀ Ξ, (alg Ξ).Lab → UInt32
  den  : ∀ Ξ, (alg Ξ).Eff → ((alg Ξ).Var → Row) → Row

/-- **The link**: the algebra's `⊙`, `0`, `(n)↑`, `∼`, substitution and `<` are the closed-row
`++`, `[]`, `Row.ofEff`, `RowEq`, environment update and `RowLe` that the typing rules use; and
the algebra covers every name, every closed row and every row variable. -/
structure RowLink (RF : RowForm) : Prop where
  comp  : ∀ Ξ ε₁ ε₂ ε η, (RF.alg Ξ).comp ε₁ ε₂ = some ε →
            RowEq (RF.den Ξ ε η) (RF.den Ξ ε₁ η ++ RF.den Ξ ε₂ η)
  unit  : ∀ Ξ η, RF.den Ξ (RF.alg Ξ).unit η = []
  lift  : ∀ Ξ L η, RowEq (RF.den Ξ ((RF.alg Ξ).lift L) η) (Row.ofEff (RF.name Ξ L) (Ξ (RF.name Ξ L)) 0)
  eqv   : ∀ Ξ ε₁ ε₂ η, (RF.alg Ξ).eqv ε₁ ε₂ → RowEq (RF.den Ξ ε₁ η) (RF.den Ξ ε₂ η)
  subst : ∀ Ξ α S ε (η η' : (RF.alg Ξ).Var → Row), η' α = RF.den Ξ S η →
            (∀ β, β ≠ α → η' β = η β) → RowEq (RF.den Ξ ((RF.alg Ξ).subst α S ε) η) (RF.den Ξ ε η')
  sub   : ∀ Ξ ε₁ ε₂, (RF.alg Ξ).Sub ε₁ ε₂ → ∀ η, RowLe (RF.den Ξ ε₁ η) (RF.den Ξ ε₂ η)
  names : ∀ Ξ (n : UInt32), n ≠ 0 → Ξ n ≠ [] → (Ξ n).length ≤ 2 ^ 32 → ∃ L, RF.name Ξ L = n
  rows  : ∀ Ξ (S : Row), (closedRowAlg Ξ).WF [] S → ∃ ε, ∀ η, RowEq (RF.den Ξ ε η) S
  vars  : ∀ Ξ (α : (RF.alg Ξ).Var), ∃ ε, ∀ η, RF.den Ξ ε η = η α

/-- The minimal open-row form, the restricted instance. -/
def orowRF : RowForm where
  alg := orowAlg
  name _ n := n.1
  den _ ε η := ε.ops ++ (match ε.tail with | none => [] | some ρ => η ρ)
```

With the link, `[handle]`'s body row `Row.ofEff n E 0 ++ S` is the reading of `(n)↑ ⊙ S`, and
the algebra's `<` is admitted by `[sub]` (`RowLe` at every instance). `RowLink orowRF` is first
wave: append and lookup lemmas, and, at `subst`, that the update changes only the tail's row.
`names`, `rows` and `vars` keep T0's safety conditions from holding vacuously (an algebra with no
labels meets them).

The link ties the algebra to the closed-row operations the rules use. It does not say that every
row family an abstract `J` mentions is the reading of an effect: a typing system with row
variables in its syntax has that by construction, and the instance reading does not (§1.2). If the
kernel adopts another row-variable form (variables inside a row, presence variables), the end state
is taken at that `RowForm`; Yoshioka Thm 5.9 covers simple and scoped rows. §10 records the form as
OQ-13's remaining design question.

### D3. Handler and handling

- **Handler** (existing). The value `hndVal n hr hs` (`Paper/S3_Dynamics/Definitions.lean:352`):
  a return clause and a tuple of clauses. The term is `hndE H e`. The typing is `[handle]`
  (`effHandle`, `Core/Fundamental.lean:367`), with clause types `clausesTy`, `retTy` and `kTy`
  (`Core/EffRules.lean:976-994`). Clauses are `!U(…)`: deep clauses are unlimited.
- **Handling.** The handler is a model of its signature on the carrier `𝒞⟦F_S R⟧`: each clause
  interprets one operation. Handling is the map induced from the least fixed point. `ewp_handle`
  (`Core/EffRules.lean:615`) builds it by induction; that is initiality's existence half.
  Uniqueness is binary (T2).

### D4. Suspension: the continuation value, its frames, its type

- **Value** (existing). `kappa n H K` (`Paper/S3_Dynamics/Definitions.lean:438`) is the `&`-pair
  `λs. case s {resume: λy. hnd H K[y] | cancel: ccatch (hnd H K[raise (cancelVal (n :: K.hndNames)
  none)])}`. The `[op]` step (`Head.hop`) hands it to the clause.
- **Type** (existing). `kTy S R q B` is one of:
  - `U((B ⊸ F_S R) & ⊤)` at `lin`;
  - `U((B ⊸ F_S R) & F_S 1)` at `aff`;
  - its `!` at `unr`.
- **Frozen finalisers** (new).

  ```lean
  /-- The finalisers of `K`'s `[then]` frames (`ubind (N, D)`), innermost first.  In
  `.appR f K` the frame `f` is outside `K`. -/
  def Kont.fins : Kont → List Expr
    | .hole => []
    | .appR f K => K.fins ++ (match f with
        | .app (.prim .ubind) (.pair _ D) => [D]
        | _ => [])
    | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
    | .inj₂ K => K.fins

  /-- The cancel branch of `κ = kappa n H K` after its three administrative steps. -/
  def cancelOf (n : UInt32) (H : Val) (K : Kont) : Expr :=
    ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none)))))
  ```

### D5. Platform environment: a comodel

The platform answers, at the top, the operations no handler catches. It is a runner, also
called a comodel (Ahman–Bauer Def. 1; Plotkin–Power). It has state-access semantics only, as
OQ-19 decided: no signals and no finalisation. It never touches the program's memory. Allocation
stays a machine step, quantified over every allocator by `Steps` (SPEC §13); OQ-30 is not decided
here.

```lean
structure Platform where
  ops : Row
  St  : Type
  s₀  : St
  co  : St → UInt32 → UInt32 → Val → Option (Val × St)

/-- The protocol: data operations that resume once; every well-formed request answered;
answers at the operation's answer type. -/
structure Platform.Respects (P : Platform) : Prop where
  uniq  : P.ops.Uniq
  nz    : P.ops.NZ
  lin   : ∀ o ∈ P.ops, o.q = .lin ∧ o.abort = false
  data  : ∀ o ∈ P.ops, o.A.Data ∧ o.B.Data
  total : ∀ s o v, o ∈ P.ops → DataVal o.A v → ∃ w s', P.co s o.n o.i v = some (w, s')
  typed : ∀ s s' o v w, o ∈ P.ops → DataVal o.A v → P.co s o.n o.i v = some (w, s') →
            DataVal o.B w

def Platform.none : Platform := ⟨[], Unit, (), fun _ _ _ _ => none⟩
```

**Capabilities that need finalising** (stdin, stdout, files) are owned cells, as in today's I/O
model: `Ref Input` and `Ref Output`, made by the externs `mk_input`/`mk_output` and released by
`take_input`/`take_output` (`Core/Stdio.lean`), with their contracts as the named hypothesis
`ExternsMeet` (`Core/Stdio.lean:597`). `SoundnessContracts` (T1) puts the externs and the
platform together, at every row the platform answers, so a program that performs platform
operations and holds capability cells must release every one of them: `Final`'s empty memory is
the release obligation, and D9 is its exactly-once reading.

### D6. Runs, data, the outermost driver

```lean
structure Conf (P : Platform) where
  μ : Heap
  e : Expr
  s : P.St

/-- A step under a platform: a machine step (`Step1`: every allocator's choice), or the platform
answering an operation of its row that no handler of the program catches. -/
inductive PStep (P : Platform) : Conf P → Conf P → Prop
  | mach {μ e μ' e' s} : Step1 μ e μ' e' → PStep P ⟨μ, e, s⟩ ⟨μ', e', s⟩
  | plat {μ s s' K n i v w o} : K.HasHnd n = false → Row.find P.ops n i = some o →
      P.co s n i v = some (w, s') →
      PStep P ⟨μ, K.plug (performE (.val (opPayload n i v))), s⟩ ⟨μ, K.plug (.val w), s'⟩
abbrev PSteps (P : Platform) := Relation.ReflTransGen (PStep P)
def init (P : Platform) (e : Expr) : Conf P := ⟨Adequacy.emptyMem, e, P.s₀⟩

/-- First-order data at `k` bound variables: `1`, `0`, integers, `⊗`, `⊕`, and `μX. A` over
these.  No location, no code, no capability. -/
inductive VTy.DataB : Nat → VTy → Prop
  | unit (k) : VTy.DataB k .unit
  | zero (k) : VTy.DataB k .zero
  | int (k w) : VTy.DataB k (.int w)
  | tvar {k n} : n < k → VTy.DataB k (.tvar n)
  | tensor {k A B} : VTy.DataB k A → VTy.DataB k B → VTy.DataB k (.tensor A B)
  | sum {k A B} : VTy.DataB k A → VTy.DataB k B → VTy.DataB k (.sum A B)
  | mu {k A} : VTy.DataB (k + 1) A → VTy.DataB k (.mu A)
/-- A closed data type. -/
def VTy.Data (A : VTy) : Prop := VTy.DataB 0 A

/-- The values of a closed data type (`BytesV`'s shape, `Core/Stdio.lean`): the least fixed
point, with `μ` read at its unrolling. -/
inductive DataVal : VTy → Val → Prop
  | unit : DataVal .unit .unit
  | int {w v} : v.IsInt w → DataVal (.int w) v
  | pair {A B v₁ v₂} : DataVal A v₁ → DataVal B v₂ → DataVal (.tensor A B) (Val.pair v₁ v₂)
  | inj₁ {A B v} : DataVal A v → DataVal (.sum A B) (Val.inj₁ v)
  | inj₂ {A B v} : DataVal B v → DataVal (.sum A B) (Val.inj₂ v)
  | roll {A v} : DataVal (VTy.inst (.mu A) A) v → DataVal (.mu A) v

/-- Final: a value of the data answer type, with the memory empty. -/
def Final (P : Platform) (A : VTy) (c : Conf P) : Prop :=
  ∃ v, c.e = .val v ∧ DataVal A v ∧ c.μ = Adequacy.emptyMem
```

**The outermost driver.** SPEC §11 and §14: "the runtime drives a `main` that returns a loop
until it finishes; it never closes it."

```lean
inductive Phase | main | drive
/-- `next` of a loop thunk: its first observation (`forceE` at `ν` is the value itself). -/
def nextE (l : Val) : Expr := .app (.val l) (.val (Val.inj₁ .unit))

inductive RStep (P : Platform) : Conf P × Phase → Conf P × Phase → Prop
  | run   {c c' ph} : PStep P c c' → RStep P (c, ph) (c', ph)
  | start {μ s l}   : RStep P (⟨μ, .val l, s⟩, .main) (⟨μ, nextE l, s⟩, .drive)
  | again {μ s l}   : RStep P (⟨μ, .val (Val.inj₂ l), s⟩, .drive) (⟨μ, nextE l, s⟩, .drive)

def FinalDrive (P : Platform) (A : VTy) : Conf P × Phase → Prop
  | (c, .drive) => ∃ a, c.e = .val (Val.inj₁ a) ∧ DataVal A a ∧ c.μ = Adequacy.emptyMem
  | (_, .main)  => False
```

### D7. Effect safety: where a run may stop

```lean
/-- A stop at an operation of the row `S`: a `perform` that no handler of its name catches, or a
`raise` that no frame catches, of an operation `S` has, of the matching kind. -/
def StopsIn (S : Row) (e : Expr) : Prop :=
  (∃ K n i v o, e = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
      Row.find S n i = some o ∧ o.abort = false) ∨
  (∃ K n i v o, e = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
      Row.find S n i = some o ∧ o.abort = true)
```

A `StopsIn` term is irreducible (`stop_irreducible`, a machine lemma from `head_plug`/
`plug_decomp`, `Core/Steps.lean:312,579`).

### D8. Safety, termination, divergence

```lean
/-- Every-run safety: no run gets stuck; a run that cannot step is final. -/
def SafeRuns (P : Platform) (A : VTy) (e : Expr) : Prop :=
  ∀ c, PSteps P (init P e) c → Final P A c ∨ ∃ c', PStep P c c'

/-- Termination: every run continues to a final configuration, and no run is infinite. -/
def Terminates (P : Platform) (A : VTy) (e : Expr) : Prop :=
  (∀ c, PSteps P (init P e) c → ∃ c', PSteps P c c' ∧ Final P A c') ∧
  ¬ ∃ f : ℕ → Conf P, f 0 = init P e ∧ ∀ n, PStep P (f n) (f (n + 1))

/-- A driven loop: every finite prefix of the (possibly infinite) drive is safe. -/
def SafeDrive (P : Platform) (A : VTy) (e : Expr) : Prop :=
  ∀ rc, Relation.ReflTransGen (RStep P) (init P e, .main) rc →
    FinalDrive P A rc ∨ ∃ rc', RStep P rc rc'

/-- The answers whose programs terminate.  Divergence lives in `Loop` codata (decision 35), so
every `F_S A` at a data `A` is div-free; if divergence moved into rows, this predicate changes,
and the targets that read it with it. -/
def DivFree (_S : Row) (A : VTy) : Prop := A.Data
```

**`DivFree` is a claim about every construct typed at `F`.** T1 asks termination of every typed
program at a `DivFree` answer. That is right while every construct that can diverge is typed at a
`Loop` (decision 35) and the recursion drivers at `F` are bounded (`bounded_fix`, SPEC §20, total
at every host). Any construct that can diverge and is typed at an `F` type (a recursion driver
such as decision 59's `deep`, typed at `F` rather than `Loop`) must change `DivFree` to exclude
its types, or carry its divergence in a row that `DivFree` reads, so that termination is never
claimed for it. Divergence is an effect and totality is not a goal (decision 35); `DivFree` is the
place where that is kept true.

### D9. Finalisation exactly once

**Resources.** In this machine three facts hold: `alloc`/`tab` take a free location; `free` needs
an allocated one (`Head.free` asks `μ ℓ = some v`); a step that matches no rule is stuck. A run
whose allocator **reuses no location** names each cell by its location, and on such runs
"released exactly once" is an event-level property:

```lean
/-- A run, as the list of its configurations. -/
inductive PRun (P : Platform) : List (Conf P) → Prop
  | one (c : Conf P) : PRun P [c]
  | cons {c c' : Conf P} {cs : List (Conf P)} : PStep P c c' → PRun P (c' :: cs) →
      PRun P (c :: c' :: cs)

def Allocated {P} (cs : List (Conf P)) (k : Nat) (ℓ : Loc) : Prop :=
  ∃ c c', cs[k]? = some c ∧ cs[k + 1]? = some c' ∧ c.μ ℓ = none ∧ (c'.μ ℓ).isSome
def Released {P} (cs : List (Conf P)) (k : Nat) (ℓ : Loc) : Prop :=
  ∃ c c', cs[k]? = some c ∧ cs[k + 1]? = some c' ∧ (c.μ ℓ).isSome ∧ c'.μ ℓ = none

/-- The run never allocates a location it released earlier. -/
def NoReuse {P} (cs : List (Conf P)) : Prop :=
  ∀ j k ℓ, j < k → Released cs j ℓ → ¬ Allocated cs k ℓ

/-- Every location the run allocates is released exactly once, and none is released that the
run did not allocate. -/
def ReleasedOnce {P} (cs : List (Conf P)) : Prop :=
  (∀ ℓ k, Allocated cs k ℓ → ∃! j, Released cs j ℓ) ∧
  (∀ ℓ j, Released cs j ℓ → ∃ k, k < j ∧ Allocated cs k ℓ)

/-- **The machine lemma** (second wave): a safe, terminating program releases every cell exactly
once on every complete run that reuses no location. -/
def ReleasedOnceOfSound : Prop :=
  ∀ (P : Platform) (A : VTy) (e : Expr), SafeRuns P A e → Terminates P A e →
    ∀ cs, PRun P (init P e :: cs) → NoReuse (init P e :: cs) →
      (∀ c, (init P e :: cs).getLast? = some c → Final P A c) → ReleasedOnce (init P e :: cs)

/-- **Exactly-once release, a conjunct of done** (T1's "every owned resource and capability
finalised exactly once, including inside dropped continuations"): every complete run that reuses
no location, of every program T1 covers, externs given as values meeting their contracts
included, releases every cell it allocates exactly once. -/
def ReleasedOnceAll (J : TypingJ) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet Γ γ →
    ∀ cs, PRun P (init P (substAll γ e) :: cs) → NoReuse (init P (substAll γ e) :: cs) →
      (∀ c, (init P (substAll γ e) :: cs).getLast? = some c → Final P A c) →
      ReleasedOnce (init P (substAll γ e) :: cs)

/-- **Exactly-once release on runs that reuse locations** (beside done): each such complete run
has a no-reuse sibling, step for step, related to it at each step by a location renaming that
changes only where the run reallocates a released location; the sibling releases each cell
exactly once.  Its proof needs `BinderMachine` at block-affine permutations (OQ-43 (b)). -/
def ReleasedOnceReuse (J : TypingJ) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet Γ γ →
    ∀ cs, PRun P (init P (substAll γ e) :: cs) →
      (∀ c, (init P (substAll γ e) :: cs).getLast? = some c → Final P A c) →
      ∃ (cs' : List (Conf P)) (πs : ℕ → Equiv.Perm Loc),
        cs'.length = cs.length ∧ PRun P (init P (substAll γ e) :: cs') ∧
        NoReuse (init P (substAll γ e) :: cs') ∧ ReleasedOnce (init P (substAll γ e) :: cs') ∧
        ∀ k c c', cs[k]? = some c → cs'[k]? = some c' →
          c'.e = c.e.renameLoc (πs k) ∧ c'.μ = c.μ.renameLoc (πs k)
```

`ReleasedOnceAll J` follows from `SoundnessContracts J` and `ReleasedOnceOfSound`; it is a
conjunct of `Guarantees` so that exactly-once release is part of done in its own words, and not
only through `Final`'s empty memory. `ReleasedOnceReuse` is beside done (§1.0): it needs the
location half of the binder at the machine.

**Why the no-reuse runs carry it to every run.** On a run whose allocator reuses a freed
location, a stale pointer can release or read the new cell at that location without getting
stuck. Its **no-reuse sibling** is the run with the same steps, each reused location renamed
apart: `Alloc.replay` (`Core/Demonic.lean:205`) of the renamed choice list, related by location
renaming (TwoRun's `steps_rename`, in the block-affine form of D11). On the sibling the stale
release finds no cell and is stuck, which `SafeRuns` excludes, because `SafeRuns` quantifies over
every allocator through `Step1`. `Core/Stale.lean` shows the mechanism on `staleL`: the reusing
run is safe, and the run under `Alloc.atCount` is stuck. So `SafeRuns ∧ Terminates` carries the
exactly-once statement to every run, `Final`'s empty memory being the at-least-once half and the
stuck sibling the at-most-once half; `ReleasedOnceReuse` is that argument as a target. It includes
cells held only by continuations that were cancelled: if they were never released, the final
memory would not be empty. On a driven loop that never finishes, only the at-most-once half is
claimed, because divergence is an effect.

**Frames.** The cancel of a continuation runs the finalisers of its frozen `[then]` frames once
each, innermost first, and an unwind runs those it passes in the same order:

- each `ufinC`/`ufin` step consumes the frame it fires at;
- no handler can catch the cancel, because no handler is named `0`;
- `cfin` keeps a finaliser's error or suppresses it.

This is SPEC §19's machine. I3.b states it over complete runs (§5).

### D10. The invariant, arising, and what suspensions hold

- **Existing.** `TW W ps rs` (`Core/World.lean:110`) is the configurations the printed proofs'
  operations produce: the resources that arise (adjudications §12.72). `TI` is their invariant,
  and `TW.inv`/`TW.valid` prove it holds (`Core/Invariant.lean:1836,2702,1802`).
- **At W.** `M.held i` is what the suspended computations at index `i` hold: open 6.64 frames
  and tagged records. `Arises M` says every configuration W reaches is a tagged `TW` world over
  the visible frames and records together with the held ones (I2, §5). Then `TW.inv` and
  `TW.valid` apply to it. Where the held frames are kept is `held`'s content and OQ-9's question;
  `Arises` ties the count to it, so it cannot be met by an unrelated superset.

### D11. The freeze binder's actions

"Freeze is a binder over internal locations, lifetimes and instances; resume and placement
instantiate it" (user, 2026-10-04). Each part has its own action.

**Locations.** A permutation `π : Equiv.Perm Loc` acts on everything that names a location:

- **on terms, contexts, heaps:** `Expr.renameLoc π`, `Kont.renameLoc π`, `Heap.renameLoc π`, local
  copies of `TwoRun/Rename.lean`'s `Expr.rename`, `Kont.rename`, `Heap.rename`;
- **on resources:** `ResU.mapLoc π` (new). It renames keys and the locations inside cells: values,
  witnesses, and stored predicates by conjugation, by the stratum recursion Restrat's `relRU` uses;
- **on `FrameRec`/`SRec`:** fieldwise (`FrameRec.renameLoc`), and on indices by
  `Idx.locAct a π (ls, σ) := (ls.map (SRec.renameLoc π), a.loc π σ)`;
- **on predicates, entries and tables:** by conjugation,
  `(π • Φ) i e ρ := Φ (i.locAct a π⁻¹) (e.renameLoc π⁻¹) (ρ.mapLoc π⁻¹)`, and the same on each
  entry's `PA`/`PB` (`OpEntI.locAct`, `OpTabI.locAct`).

Array steps compute `ℓ + j` (`tab`, `idx`, `split`, `drop`), so a permutation commutes with them
only if it moves each array's block as a whole. The action is therefore taken at permutations
that are **affine on the blocks** a configuration's arrays name:

```lean
/-- A set of ranges `(ℓ, n)`, each the block `[ℓ, ℓ + n)`. -/
abbrev Ranges := Loc × Nat → Prop

/-- `π` moves each range of `rs` as a block. -/
def BlockAffine (π : Equiv.Perm Loc) (rs : Ranges) : Prop :=
  ∀ p, rs p → ∀ j, j < p.2 → π (p.1 + j) = π p.1 + j

/-- The ranges of the array values `Val.arr ℓ n` occurring in a term (under binders too). -/
def Expr.arrRanges : Expr → Ranges
  | .pair (.loc ℓ) (.prim (.lit (.i32 n))), q => q = (ℓ, n.toNat)
  | .pair a b, q | .seq a b, q | .letpair a b, q | .app a b, q => a.arrRanges q ∨ b.arrRanges q
  | .inj₁ a, q | .inj₂ a, q | .lam a, q => a.arrRanges q
  | .case a b c, q => a.arrRanges q ∨ b.arrRanges q ∨ c.arrRanges q
  | _, _ => False
/-- In a heap: in a stored value. -/
def Heap.arrRanges (μ : Heap) : Ranges := fun q => ∃ m v, μ m = some v ∧ v.1.arrRanges q
/-- In a context: in a term or value of one of its frames. -/
def Kont.arrRanges : Kont → Ranges
  | .hole, _ => False
  | .pairL K e, q | .letpair K e, q | .seq K e, q => K.arrRanges q ∨ e.arrRanges q
  | .pairR v K, q | .appL K v, q => K.arrRanges q ∨ v.1.arrRanges q
  | .case K e₁ e₂, q => K.arrRanges q ∨ e₁.arrRanges q ∨ e₂.arrRanges q
  | .appR f K, q => f.arrRanges q ∨ K.arrRanges q
  | .inj₁ K, q | .inj₂ K, q => K.arrRanges q
/-- In a resource: in a cell's value or, recursively, in its witness (`CellU.erase`,
`CellU.wit`, as `SubRec` reads them, `Core/FrameRecords.lean:118`). -/
inductive ResU.arrRanges : WRes → Ranges
  | val {ρ : WRes} {m : Loc} {ψ : CellU Loc Val} {q : Loc × Nat} :
      ρ.get m = some ψ → ψ.erase.1.arrRanges q → ResU.arrRanges ρ q
  | wit {ρ : WRes} {m : Loc} {ψ : CellU Loc Val} {q : Loc × Nat} :
      ρ.get m = some ψ → ResU.arrRanges ψ.wit q → ResU.arrRanges ρ q

/-- A run every configuration of which names arrays only within the ranges `rs`. -/
def RangesIn (rs : Ranges) (μ : Heap) (e : Expr) : Prop :=
  ∀ q, (e.arrRanges q ∨ μ.arrRanges q) → ∃ p, rs p ∧ p.1 ≤ q.1 ∧ q.1 + q.2 ≤ p.1 + p.2
inductive StepsIn (rs : Ranges) : Heap → Expr → Heap → Expr → Prop
  | refl (μ e) : RangesIn rs μ e → StepsIn rs μ e μ e
  | more {μ μ₁ μ' e e₁ e'} : RangesIn rs μ e → Step1 μ e μ₁ e₁ → StepsIn rs μ₁ e₁ μ' e' →
      StepsIn rs μ e μ' e'
```

Every run is a `StepsIn` at the ranges it names (`steps_in_ranges`), since `tab`'s array value
appears in the term at the step that allocates it (`tabFill`'s tail,
`Support/Dynamics/Arrays.lean:38`).

**Lifetimes.** A re-stratification `θ : Restrat.Emb c` is a strictly monotone map on
`Life = ℕᵒᵈ`, the identity at and above the cut `c`. The binder is instantiated only beneath the
resumer's own lifetimes, below its cut `c`; that, not an absence of other order-respecting maps,
is why the renamings are `Restrat.Emb c`. It acts:

- on resources by `θ.relRU`;
- on substitutions by `LSub.mapN θ.toNat`;
- on records and indices fieldwise (`Idx.lifeAct a θ`);
- on predicates, entries and tables by direct image (`θ` is injective, not invertible):
  `(θ ▹ Φ) i e ρ := ∃ i₀ ρ₀, i = i₀.lifeAct a θ ∧ ρ = θ.relRU ρ₀ ∧ Φ i₀ e ρ₀`.

**Instances.** Names are static per site (OQ-14 (a)), so the instance half is vacuous today. If
generative instances are adopted, a name permutation fixing `0` acts on `hnd` frames and
operation payloads, as the location half does.

**The lend stack.** W's own action on σ is a group action of location permutations and a monoid
action of re-stratifications, fixing `nil`:

```lean
structure StkAct (M : SemWorld) where
  loc  : Equiv.Perm Loc → M.Stk → M.Stk
  life : ∀ {c : Life}, Restrat.Emb c → M.Stk → M.Stk
  loc_one  : ∀ σ, loc 1 σ = σ
  loc_mul  : ∀ π π' σ, loc (π * π') σ = loc π (loc π' σ)
  loc_nil  : ∀ π, loc π M.nil = M.nil
  life_id  : ∀ c σ, life (Restrat.Emb.id c) σ = σ
  life_comp : ∀ c (θ θ' : Restrat.Emb c) σ, life (θ.comp θ') σ = life θ (life θ' σ)
  life_nil : ∀ c (θ : Restrat.Emb c), life θ M.nil = M.nil
```

`Restrat.Emb.id` and `Restrat.Emb.comp` are new (the identity and composition of strictly
monotone maps that fix everything at and above `c`).

### D12. Observations and contextual approximation (binary targets only)

```lean
def Obs (P : Platform) (A : VTy) (e : Expr) : Set Val :=
  {v | ∃ c, PSteps P (init P e) c ∧ Final P A c ∧ c.e = .val v}

/-- The thunk `λ_. e` of a computation at an `F` type. -/
def thunkF (e : Expr) : Val := ⟨.lam (e.shift 1 0), .lam⟩

/-- `t₁ ≼ t₂` at `U C`: every well-typed closing context at a data answer observes no more of
`t₁` than of `t₂`.  `t₁`, `t₂` are closed thunks of `C`. -/
def CtxApprox (J : TypingJ) (P : Platform) (C : CTy) (t₁ t₂ : Val) : Prop :=
  ∀ (f : Expr) (S : Row) (A : VTy), A.Data → RowLe S P.ops →
    J.at LifeCtx.empty [⟨.thunk C, true⟩] f (.comp (CTy.effOf S A)) →
    Obs P A (f.subst 0 t₁) ⊆ Obs P A (f.subst 0 t₂)
def CtxEquiv (J : TypingJ) (P : Platform) (C : CTy) (t₁ t₂ : Val) : Prop :=
  CtxApprox J P C t₁ t₂ ∧ CtxApprox J P C t₂ t₁
```

### D13. Answering implementations (for I4)

An answering effect is implemented by a borrow, following HandlersAsBorrows (README §2) and
`Core/Handlers.lean`:

- the handler's state cell is lent as `Mut 'h S`;
- each operation is a `withswap` on the borrowed state;
- the clause resumes once, in tail position, with no continuation reified.

```lean
structure AnsImpl where
  S  : VTy
  E  : List (VTy × VTy)              -- operations A_j ↠^lin B_j
  co : List Val                      -- co_j : !U(S ⊗ A_j ⊸ F(S ⊗ B_j)), closed

/-- The operation call on the borrowed state:
`λp. let (m, a) = p in withswap m (λs. co (s, a))`, answering `(m, b)`. -/
def ansCall (co : Val) : Val :=
  ⟨.lam (.letpair (.var 0)
     (app2 withswap (.var 1) (.val (.lam (.app (.val co) (.pair (.var 0) (.var 1))))))), .lam⟩

/-- `with h(s₀) { body }`:
`c ← alloc s₀; f ← (Λ. λm. body); w ← withborU d; (c, r) ← w c f; (free c, r)`, the finaliser `d` releasing
the source on an unwind (`withborUE`, `Core/EffBorrow.lean:205`).  `body` is typed in
`m :: Γ`; inside the callback it sits under `m`, the `Λ`'s dead slot and the cell, so its
variables of `Γ` are shifted past the latter two. -/
def ansRun (d s₀ body : Expr) : Expr :=     -- A-normal form, §Corrections C3
  bindE (.app alloc' s₀)
    (bindE (.val (.lam (.val (.lam (body.shift 2 1)))))
      (bindE (withborUE d)
        (.app (.val (.lam (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))
```

**The control form** (decision 59: "a handler whose operations resume has a state … passed to
each clause and at each resume"). It is the state-passing handler at the answer
`U(S ⊸ F_Σ(S ⊗ R))`, applied to the initial state:

```lean
/-- The clause of `co`: `λ(a, κ). λs. let (s', b) = co (s, a) in κ.resume b to f. f s'`. -/
def ctlClause (co : Val) : Val :=
  ⟨.lam (.letpair (.var 0) (.lam
    (.letpair (.app (.val co) (.pair (.var 0) (.var 2)))
      (bindE (.app (.app (.var 3) (.val (Val.inj₁ .unit))) (.var 0)) (.app (.var 0) (.var 2)))))),
   .lam⟩

/-- The answer clause: `λr. λs. (s, r)`. -/
def ctlRet : Val := ⟨.lam (.lam (.pair (.var 0) (.var 1))), .lam⟩

/-- A right-nested tuple of clauses. -/
def clausesV : List Val → Val
  | [] => .unit
  | c :: cs => Val.pair c (clausesV cs)

/-- `(handle_n e with ctlRet, ctlClause co_j …) s₀`, `e` closed. -/
def ctlForm (n : UInt32) (impl : AnsImpl) (s₀ e : Expr) : Expr :=
  bindE (bindE (.val (clausesV (impl.co.map ctlClause))) (bindE (.val ctlRet) (hndTerm n 0 1 e)))
    (bindE s₀ (.app (.var 1) (.var 0)))
```

**Capability passing on the spine.** HandlersAsBorrows' translation (`tr`, `Translate.lean`)
threads the borrowed state through the body. It is defined here at the bodies whose operations of
`n` are performed on the spine: each `perform (n, j) a` is the bound computation of a `let`, and
everything else the body runs mentions no operation of `n` (`Expr.OpFree n`, syntactic: no
`perform`, `raise` or `hnd` with the name literal `n`). It covers straight-line bodies with
branches; a body that hands the effect to a callback needs the full translation, which changes the
callback's type. Outside the class `capPass` is `none`; a translation of every body is
HandlersAsBorrows' `tr` lifted to Core, which is OQ-1's design question.

```lean
/-- `n` is not the name literal of any `perform`, `raise` or `hnd` in the term. -/
def Expr.OpFree (n : UInt32) : Expr → Prop
  | .app (.prim p) (.pair (.prim (.lit (.i32 m))) r) =>
      ((p = .perform ∨ p = .raise ∨ p = .hnd) → m ≠ n) ∧ r.OpFree n
  | .pair a b | .seq a b | .letpair a b | .app a b => a.OpFree n ∧ b.OpFree n
  | .inj₁ a | .inj₂ a | .lam a => a.OpFree n
  | .case a b c => a.OpFree n ∧ b.OpFree n ∧ c.OpFree n
  | _ => True

/-- `(j, a)` when the term is `perform (n, (j, a))` with the literal name `n`. -/
def Expr.performOf (n : UInt32) : Expr → Option (UInt32 × Expr)
  | .app (.prim .perform) (.pair (.prim (.lit (.i32 n'))) (.pair (.prim (.lit (.i32 j))) a)) =>
      if n' = n then some (j, a) else none
  | _ => none

open Classical in
/-- `k` is the borrowed state's index.  A `let` of `perform (n, j) a` becomes
`let (m', b) = ansCall co_j (m, a) in …`, the rest reading `m'` (its other variables shifted past
`m'`); an `n`-free tail forgets `m` first.  Well-founded on `Expr.size`, which `shift` keeps. -/
noncomputable def capPass (n : UInt32) (cos : List Val) : Nat → Expr → Option Expr
  | k, .app (.lam e') M =>
      match M.performOf n with
      | some (j, a) =>
          if a.OpFree n then
            (cos[j.toNat]?).bind fun co => (capPass n cos 1 (e'.shift 1 1)).map fun body =>
              .letpair (.app (.val (ansCall co)) (.pair (.var k) a)) body
          else none
      | none => if M.OpFree n then (capPass n cos (k + 1) e').map fun b => .app (.lam b) M
                else none
  | k, .seq v e' => if v.OpFree n then (capPass n cos k e').map (.seq v) else none
  | k, .letpair v e' =>
      if v.OpFree n then (capPass n cos (k + 2) e').map (.letpair v) else none
  | k, .case v e₁ e₂ =>
      if v.OpFree n then
        (capPass n cos (k + 1) e₁).bind fun b₁ => (capPass n cos (k + 1) e₂).map (.case v b₁)
      else none
  | k, e => if e.OpFree n then some (.seq (.app forget (.var k)) e) else none
```

The borrow form of a closed body `e` is `ansRun d s₀ body` with
`capPass n impl.co 0 (e.shift 1 0) = some body`. I4 (§5) relates the two forms.

### D14. The acceptance terms

The survey's programs that tier 2 must accept (§8), as closed Core terms. Each is typed at the
stated answer by tier 2's spanning rules and rejected by tier 1 (`Row.Unwind`, and semantically
R-T1). The builder writes the de Bruijn form shown and checks each one's interpreter run.

```lean
/-- `Foo : 1 ↠^lin 1`, the operation `0` of the name `5`. -/
def fooSig : OpSig := ⟨5, 0, .lin, .unit, .unit⟩
def fooE : Expr := performE (opArgE 5 0 (.val .unit))
/-- `Choose : 1 ↠^lin Flag`, the operation `0` of the name `6`. -/
def chooseSig : OpSig := ⟨6, 0, .lin, .unit, Flag⟩
def chooseE : Expr := performE (opArgE 6 0 (.val .unit))
/-- `Susp : 1 ↠^aff 1` is `suspSig`, the name `4` (`Core/EffPrograms.lean:882`). -/
def suspE : Expr := performE (opArgE 4 0 (.val .unit))

/-- A handler of the name `n` with the identity answer clause and the one clause `cl`. -/
def handleWith (n : UInt32) (cl : Expr) (e : Expr) : Expr :=
  bindE (.pair cl (.val .unit)) (bindE (.val (.lam (.var 0))) (hndTerm n 0 1 e))
/-- The clause that resumes with the argument (`Backend/Kernel.lean`'s `resumeCl`). -/
def resumeArg : Expr := .val (.lam (.letpair (.var 0) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.var 1))))
/-- The clause that resumes with `inj₁ ()`. -/
def resumeLeft : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val (.inj₁ .unit))))))
/-- The clause that cancels the continuation and answers `inj₂ ()`. -/
def cancelAns : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1)
    (bindE (.app (.var 0) (.val (.inj₂ .unit))) (.seq (.var 0) (.inj₂ unit'))))))
/-- The clause that stores the continuation in a cell, takes it back, and resumes it at `()`. -/
def storeResume : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1)
    (bindE (.app alloc' (.var 0)) (bindE (.app free' (.var 0))
      (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit)))))))

/-- `dupFlag : !U(Flag ⊸ F(Flag ⊗ Flag))`: the flag and a copy. -/
def dupFlag : Expr :=
  .val (.lam (.case (.var 0) (.seq (.var 0) (.pair (.inj₁ unit') (.inj₁ unit')))
                             (.seq (.var 0) (.pair (.inj₂ unit') (.inj₂ unit')))))
/-- Read the flag through `m` (index `i`): `let (m', b) = withswap m dupFlag in forget m'; b`. -/
def readThrough (i : Nat) : Expr :=
  .letpair (app2 withswap (.var i) dupFlag) (.seq (.app forget (.var 1)) (.var 0))
/-- Write `c` (index `j`) through `m` (index `i`), answering the old flag. -/
def writeThrough (i j : Nat) : Expr :=
  .letpair (app2 withswap (.var i) (.val (.lam (.pair (.var (j + 1)) (.var 0)))))
    (.seq (.app forget (.var 1)) (.var 0))

/-- A callback `Λ. λm. body`. -/
def cb (body : Expr) : Expr := .val (.lam (.val (.lam body)))
/-- Lend a fresh cell holding `init` to `f` with `withborU dFlag`, then free the cell and answer
`f`'s result. -/
def lendCell (init : Expr) (f : Expr) : Expr :=     -- A-normal form, §Corrections C3
  bindE (.app alloc' init)
    (bindE f
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0) (.seq (dropB (.app free' (.var 1))) (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

/-- **AT02** (Yarrow's region example, one-shot): `m` held across `Foo`, then read. -/
def at02 : Expr := handleWith 5 resumeArg
  (lendCell (.inj₁ unit') (cb (bindE fooE (.seq (.var 0) (readThrough 1)))))
/-- **AT04** (`v.push(do choose())`, one-shot): `Choose`'s answer written through `m`. -/
def at04 : Expr := handleWith 6 resumeLeft          -- A-normal form, §Corrections C3
  (bindE (.app alloc' (.inj₂ unit'))
    (bindE (cb (bindE chooseE (writeThrough 1 0)))
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0)
            (bindE (.app free' (.var 1)) (.pair (.var 0) (.var 1))))))
          (.app (.app (.var 0) (.var 2)) (.var 1))))))
/-- **AT12** (`thread::scope` with the continuation dropped, single-threaded): the lend spans an
affine `Susp`; the handler cancels the continuation, and the lend's finaliser frees the cell
during the cancel. -/
def at12 : Expr := handleWith 4 cancelAns
  (lendCell (.inj₁ unit') (cb (bindE suspE (.seq (.var 0) (readThrough 1)))))
/-- **AT17** (a lend across a perform in a movable first-class continuation): the handler moves
the continuation into a cell and back, then resumes it. -/
def at17 : Expr := handleWith 5 storeResume
  (lendCell (.inj₁ unit') (cb (bindE fooE (.seq (.var 0) (readThrough 1)))))
```

| term | answer | observation (interpreter) |
|---|---|---|
| `at02` | `Flag` | `inj₁ ()`, memory empty |
| `at04` | `Flag ⊗ Flag` | `(inj₁ (), inj₂ ())`, memory empty |
| `at12` | `Flag` | `inj₂ ()`, memory empty (the cell freed by `dFlag` during the cancel) |
| `at17` | `Flag` | `inj₁ ()`, memory empty |

`storeCancel` (`Core/EffPrograms.lean:905`, a handler stores `κ`, takes it back and cancels it) is
the tier-1 member of the same family, typed by `d_storeCancel`.

---

## 3. The four top-level theorems

### T1. Soundness (unary) — notebook P1

**World:** [prog]. The proof route goes through [W] (§4).

**(a) Statement.** Take every well-typed program, every allocator, and every platform that
respects its protocol.

- Every run is safe. It is never stuck: no use after free, no double release, no unhandled
  operation.
- A program at a div-free answer terminates. Every run ends at a value of its type with the
  memory empty, so every owned cell and capability is released exactly once (D9), including
  those held inside cancelled continuations.
- A program that returns a loop is driven by the runtime, possibly forever. Every finite prefix
  of the drive is safe, and a drive that finishes ends as above.
- The same holds when the program also holds capabilities given as externs meeting their
  contracts, while it performs platform operations (`SoundnessContracts`).

Termination is claimed only where the answer is div-free (D8). Tier 1 and tier 2 are this
theorem at two typing systems. Exactly-once release on every complete run is the conjunct
`ReleasedOnceAll` (D9), beside these.

**Scope: main's row.** `SoundRetAt` asks `RowLe S P.ops`, and every platform operation is linear
and resumes (`Platform.Respects.lin`). So main's row may hold only platform operations: an
abortive operation, an error, must be handled before the top. This is the user's "no unhandled
operation" read at the top: a program whose error escapes `main` is outside T1, and P2 (`EffSafe`)
says it stops only at that operation. A `Final` alternative for an uncaught abortive stop with the
memory empty (the exit-with-error reading) is not adopted; it is OQ-51's option (b), adequacy
observed at a row, which 05b classes as constrained toward (a), every program closed by handlers.

**(b) Definitions.** D5 `Platform`, `ExternsMeet`; D6 `PStep`/`RStep`/`Final`/`VTy.Data`; D8;
D9.

**(c) Lean.**

```lean
/-- Programs at a div-free answer: safe and terminating, every run ending with the memory empty. -/
def SoundRetAt (J : TypingJ) (P : Platform) : Prop :=
  ∀ (S : Row) (A : VTy) (e : Expr), DivFree S A → RowLe S P.ops →
    J.closed e (CTy.effOf S A) → SafeRuns P A e ∧ Terminates P A e

/-- Programs that return a loop: every finite prefix of the drive is safe. -/
def SoundDriveAt (J : TypingJ) (P : Platform) : Prop :=
  ∀ (S : Row) (A B : VTy) (e : Expr), A.Data → RowLe S P.ops →
    J.closed e (CTy.effOf S (.thunk (CTy.loopEff S A B))) → SafeDrive P A e

def SoundnessAt (J : TypingJ) (P : Platform) : Prop := SoundRetAt J P ∧ SoundDriveAt J P

/-- **T1.** -/
def Soundness (J : TypingJ) : Prop := ∀ P : Platform, P.Respects → SoundnessAt J P

/-- T1 with capabilities as externs meeting their contracts (today's I/O presentation,
`Core/Stdio.lean:597`), together with platform operations, at every row the platform answers. -/
def SoundnessContracts (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet Γ γ → SafeRuns P A (substAll γ e) ∧ Terminates P A (substAll γ e)
```

`ExternsMeet` reads the contracts at Core's relation. The externs' types are `!U(…)` thunks of
first-order computations with no row, so they are row-abortive types (`VTy.AbortRows`, §4.2), and
by `ConservativeWB` a contract Core proves holds in W at every index reachable from σ = []. So the
hypothesis needs no world.

**(d) Literature.**

- [CONF] Theorem 3.2: "If ⊨ wp (e) {⌜P̂⌝} then (∅, e) →∗ (∅, v) and P̂(v) for some v." Corollary
  3.3: "If ⊨ e : 1 then (∅, e) →∗ (∅, ())." These give the empty memory at the end. [CONF] says
  of them: "adequacy of the weakest precondition—that it really does characterize executions
  that are safe, terminating, and reclaim memory".
- Affect (van Rooij & Krebbers, POPL 2025) §3.2: "safe e := ∀ e′ σ′. e / ∅ →∗ e′ / σ′ =⇒ e′ ∈ Val
  ∨ (∃ e″ σ″. e′ / σ′ → e″ / σ″)", and "⊢ e : ⟨⟩ : τ ⊣ =⇒ safe e". "safety implies that no
  effects are left unhandled". This is the every-run form.
- Timany–Guéneau–Birkedal, POPL 2024, Thm 3.1: a program with a triple "is safe, i.e., it does
  not crash, and whenever it terminates to a value v, v satisfies the postcondition".
- Congard–Munch-Maccagnoni–Douence, ESOP 2026, §3: "⟨t ∣ ⋆ ∣ l⟩ ⇝∗ ⟨v ∣ ⋆ ∣ l′⟩ ⇐⇒ ∃σ, l′ = σ(l)".
  They list what it gives: "all allocated resources are released by the end of the program, only
  previously-allocated resources are released, no resource has been released twice". This is
  D9's `ReleasedOnce`.
- Ahman–Bauer, ESOP 2020, Def. 1: "A runner R for a signature Σ is given by a carrier set |R|
  together with, for each op ∈ Σ, a co-operation op_R : A_op → (|R| ⇒ B_op × |R|)". This is the
  platform.
- Zhang–Myers, POPL 2019, Thm 2: "If ∅ | ∅ | ∅ | ∅ ⊢ t : [T]∅ and t −→∗ t′, then either there
  exists v such that t′ = v or there exists t″ such that t′ −→ t″".

**(e) Existing Lean, and what to prove now.** All of it is at [Core σ=[]].

- `adequacyD`, `adequacyD_safe`, `adequacyD_val` (`Core/Demonic.lean:312,325,334`) and
  `adequacyD_obs` (`Core/EffPrograms.lean:41`): every run of a closed `F A` program, `A`
  persistent, continues to a value at the empty memory.
- `total_every_run`, `total_no_infinite_run` (`Core/Totality.lean:64,223`).
- `externs_every_run` (`Core/Stdio.lean:622`): `SoundnessContracts`'s shape at `run_io`, at no row
  and `Platform.none`.
- `externs_loop_every_run` (`:768`): driven loops, one bounded drive `driveE n` at a time.

To prove now:

- **`SoundRetAt tier1 Platform.none`.** From `adequacyD_obs` and the totality theorems, with
  `vC_data : A.Data → (vC true A ls δ v ρ ↔ ρ = PMap.empty ∧ DataVal A v)`. PROVED AT A
  RESTRICTION (`P = Platform.none`, the ret conjunct).
- **`SoundDriveAt tier1 Platform.none`.** From bounded drives (adequacy at `F(A ⊕ B)`), with the
  machine lemma that a finite prefix of the drive is a prefix of `driveE n`'s run for large `n`;
  or directly from the `ν` clause. Second wave.
- **`SoundRetAt tier1 P` for a platform with operations**: `theorem32D`'s argument across
  platform answers, by the resume conjunct of `contShare` at data answers. Second wave.
- **`SoundnessContracts tier1`**: `externs_every_run`'s proof at a general `F_S A` under every
  platform. Second wave.
- **`Soundness J`** for the end state's `J`: OPEN, at W.

**(f) Non-vacuity.**

- `Platform.none` respects its protocol.
- So does the byte-I/O comodel: `ops = [read : 1 ↠^lin (U8 ⊕ 1), write : U8 ↠^lin 1]`, with
  `St` = input bytes × output bytes.
- The typing hypothesis is met by every acceptance program in `Core/EffPrograms.lean`, closed
  derivations at data answers such as `Flag = 1 ⊕ 1`, and by D14's terms at tier 2.
- The loop clause is met by `tickProg n` (`Loop_{Log} 0 1`).
- `SoundnessContracts`' hypotheses are met by `stdModel` (`Core/Stdio.lean`, `stdModel_meets`).

**(g)** In the first pass.

### T2. Laws (binary) — notebook P11's binary half, P7's binary half

**World:** [prog], binary (contextual equivalence); the proof route goes through [W₂].

**(a) Statement.** The handler equations hold as contextual equivalences over the kernel: return,
operation, forwarding, the tail-resumptive (direct-call) law, algebraicity at linear and affine
operations, the capture laws β and η, hiding, fusion, and Staton's ν/op law at linear and affine
operations.

**(b) Definitions.** D12 `CtxEquiv`, `thunkF`. The forwarding handler `fwdH n n' E` re-performs
each of `n`'s operations as `n'` and resumes with the answer. `tailClause c` is
`λ(a, k). c a to b. k.resume b`:

```lean
def tailClause (c : Val) : Val :=
  ⟨.lam (.letpair (.var 0) (bindE (.app (.val c) (.var 1))
     (.app (.app (.var 1) (.val (Val.inj₁ .unit))) (.var 0)))), .lam⟩
```

**(c) Lean.**

```lean
def LawRet (J : TypingJ) (P : Platform) : Prop :=
  ∀ n hr hs (v : Val) S R, J.closed (hndE (hndVal n hr hs) (.val v)) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R) (thunkF (hndE (hndVal n hr hs) (.val v)))
      (thunkF (.app (.val hr) (.val v)))
def LawOp (J : TypingJ) (P : Platform) : Prop :=
  ∀ n i hr hs c (v : Val) (K : Kont) S R, K.HasHnd n = false → clauseAt hs.1 i.toNat = some c →
    J.closed (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R)
      (thunkF (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))))
      (thunkF (.app (.val c) (.pair (.val v) (kappa n (hndVal n hr hs) K))))
def LawFwd (J : TypingJ) (P : Platform) : Prop :=
  ∀ n m i hr hs (v : Val) (K : Kont) S R, m ≠ n → K.HasHnd m = false →
    J.closed (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload m i v))))) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R)
      (thunkF (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload m i v))))))
      (thunkF (bindE (performE (.val (opPayload m i v)))
        (hndE (hndVal n hr hs) ((K.shift 1 0).plug (.var 0)))))
def LawTail (J : TypingJ) (P : Platform) : Prop :=
  ∀ n i hr hs c (v : Val) (K : Kont) S R, K.HasHnd n = false →
    clauseAt hs.1 i.toNat = some (tailClause c) →
    J.closed (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R)
      (thunkF (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))))
      (thunkF (hndE (hndVal n hr hs) (K.plug (.app (.val c) (.val v)))))
/-- Algebraicity: an operation commutes with the `let` it is sequenced in, at `lin`/`aff`. -/
def LawAlg (J : TypingJ) (P : Platform) : Prop :=
  ∀ n i (v : Val) (o : OpSig) M N S R, Row.find S n i = some o → o.abort = false → o.q ≠ .unr →
    J.closed (bindE (bindE (performE (.val (opPayload n i v))) M) N) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R) (thunkF (bindE (bindE (performE (.val (opPayload n i v))) M) N))
      (thunkF (bindE (performE (.val (opPayload n i v))) (bindE M (N.shift 1 1))))
/-- β for capture: resuming `κ` at `w` is the frozen computation at `w` under its handler. -/
def CapBeta (J : TypingJ) (P : Platform) : Prop :=
  ∀ n H K (w : Val) S R, J.closed (hndE H (K.plug (.val w))) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R)
      (thunkF (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)))
      (thunkF (hndE H (K.plug (.val w))))
/-- η for capture, up to renaming the name (`[handle]` forbids the handled name in the result
row, so `fwdH n n` is not typed; OQ-27's typing check). -/
def CapEta (J : TypingJ) (P : Platform) : Prop :=
  ∀ n n' E e S R, n ≠ n' → J.closed (hndE (fwdH n n' E) e) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R) (thunkF (hndE (fwdH n n' E) e)) (thunkF (e.renameOp n n'))

/-- The forwarding clause of operation `j`, re-performed as `n'`:
`λ(a, k). perform (n', j) a to b. k.resume b`. -/
def fwdClause (n' : UInt32) (j : Nat) : Val :=
  ⟨.lam (.letpair (.var 0) (bindE (performE (opArgE n' (UInt32.ofNat j) (.var 1)))
     (.app (.app (.var 1) (.val (Val.inj₁ .unit))) (.var 0)))), .lam⟩
/-- The forwarding handler of `n`'s operations `E`, to `n'`. -/
def fwdH (n n' : UInt32) (E : List (Qual × VTy × VTy)) : Val :=
  hndVal n ⟨.lam (.var 0), .lam⟩ (clausesV ((List.range E.length).map (fwdClause n')))

/-- **A simulation between two answering implementations** of one signature (D13): related
states and one argument run, by each implementation's operation, to one answer and related next
states.  A syntactic hypothesis: runs of the machine, no binary relation. -/
def AnsSim (impl₁ impl₂ : AnsImpl) (Rel : Val → Val → Prop) : Prop :=
  impl₁.E = impl₂.E ∧ List.Forall₂ (fun (c₁ c₂ : Val) =>
    ∀ s₁ s₂ a, Rel s₁ s₂ → ∀ μ μ₁ t₁ b,
      Steps μ (.app (.val c₁) (.val (Val.pair s₁ a))) μ₁ (.val (Val.pair t₁ b)) →
      ∃ μ₂ t₂, Steps μ (.app (.val c₂) (.val (Val.pair s₂ a))) μ₂ (.val (Val.pair t₂ b)) ∧
        Rel t₁ t₂) impl₁.co impl₂.co

/-- The control form, its final state observed by `o`: `ctlForm … to (s, r). o s to w. (w, r)`. -/
def ctlObs (n : UInt32) (impl : AnsImpl) (s₀ e : Expr) (o : Val) : Expr :=
  bindE (ctlForm n impl s₀ e)
    (.letpair (.var 0) (bindE (.app (.val o) (.var 1)) (.pair (.var 0) (.var 1))))

/-- **Hiding** (the binary content of 6.66; I5's `AntiFrameW` is the unary half): two answering
handlers of one name whose states are related by a simulation, started at related states and
observed by observers that agree on related states, are contextually equivalent. -/
def Hiding (J : TypingJ) (P : Platform) : Prop :=
  ∀ (impl₁ impl₂ : AnsImpl) (Rel : Val → Val → Prop) (n : UInt32) (s₁ s₂ : Val) (e : Expr)
    (o₁ o₂ : Val) (S : Row) (R O : VTy),
    AnsSim impl₁ impl₂ Rel → AnsSim impl₂ impl₁ (flip Rel) → Rel s₁ s₂ →
    (∀ t₁ t₂ μ w, Rel t₁ t₂ →
      ((∃ μ', Steps μ (.app (.val o₁) (.val t₁)) μ' (.val w)) ↔
       (∃ μ', Steps μ (.app (.val o₂) (.val t₂)) μ' (.val w)))) →
    J.closed (ctlObs n impl₁ (.val s₁) e o₁) (CTy.effOf S (.tensor O R)) →
    J.closed (ctlObs n impl₂ (.val s₂) e o₂) (CTy.effOf S (.tensor O R)) →
    CtxEquiv J P (CTy.effOf S (.tensor O R))
      (thunkF (ctlObs n impl₁ (.val s₁) e o₁)) (thunkF (ctlObs n impl₂ (.val s₂) e o₂))

/-- **Fusion**, at the composite-handler construction `fuse` (OQ-49: the composite handler as a
kernel term).  `fuse` is a parameter, so the law is stated before the construction is chosen. -/
def LawFusion (J : TypingJ) (P : Platform) (fuse : Val → Val → Val) : Prop :=
  ∀ H₁ H₂ e S R, J.closed (hndE H₁ (hndE H₂ e)) (CTy.effOf S R) →
    J.closed (hndE (fuse H₁ H₂) e) (CTy.effOf S R) →
    CtxEquiv J P (CTy.effOf S R) (thunkF (hndE H₁ (hndE H₂ e))) (thunkF (hndE (fuse H₁ H₂) e))

/-- **Staton's ν/op law** needs generative instances (OQ-14 (b)).  Under static names there is
no `ν`, and the law is `True`; it is restated if OQ-14 (b) is adopted. -/
def LawNuOp (_J : TypingJ) (_P : Platform) : Prop := True

/-- **T2.** -/
def Laws (J : TypingJ) (fuse : Val → Val → Val) : Prop :=
  ∀ P, P.Respects → LawRet J P ∧ LawOp J P ∧ LawFwd J P ∧ LawTail J P ∧ LawAlg J P ∧
    CapBeta J P ∧ CapEta J P ∧ Hiding J P ∧ LawFusion J P fuse ∧ LawNuOp J P
```

`Expr.renameOp n n'` is a syntactic function, by structural recursion: it replaces the name
literal `n` by `n'` in every `perform`/`raise` payload and `hnd` value of the term. `Hiding` is
stated at answering handlers (D13), where the state is explicit; a handler's state in general is
whatever its clauses close over, and a simulation on that is binary (OQ-4).

**(d) Literature.**

- Plotkin–Pretnar, LMCS 2013, §1.1: "h(M) … is the unique homomorphism (a map preserving
  operations) from A+exc to M that extends the map in1".
- Their equations: "return V handled with {raise_e () ↦ N_e} to x : A. N(x) = N(V)" and
  "raise_e′ () handled with … = N_e′".
- Def. 4.5: "A handler … is correct at c if the op_H(c) are all total and the set U⟦C⟧ together
  with the op_H(c) forms a model of T".

**(e) Existing Lean.**

- Every algebraic law, in the sibling calculus EffModelRel. [SIB]; there is no bridge to Core.
- Run facts for the withdrawn sum schema: `Core/Handlers.lean`'s `op_tail`, `op_answer`,
  `handle_fold`, `abort_passes`, `return_resumes`, `loop_abort`. [Core runs]
- TwoRun's determinism up to renaming: `head_rename` for non-array steps. It does not build on
  main.

There is no binary relation on Core, and nothing is to be proved now. OQ-47 (whether reduction in
every context is contained in `≡`) is the first lemma such a relation needs.

**(f) Non-vacuity.** `LawRet` and `LawOp` hold of every handled program, because each is one head
step (`Head.hret`, `Head.hop`) in a deterministic machine.

**(g)** Out of the first pass (user, 2026-10-02: "optional and don't get pursued unless they
become necessary for safety"). Nothing is driven from it. The unary halves that FL needs are in
I5 and P11.

### T3. Abstraction (binary) — notebook P12

**World:** [prog], binary; the proof device is [W₂].

**(a) Statement.** Abstraction is a corollary of a binary fundamental lemma, as Soundness is of
the unary one. It has three parts:

- **(tunnelling)** effect-polymorphic code cannot handle the effects of the code it is handed:
  a client cannot tell whether an effect-polymorphic `f` is given a pure callback or one that
  performs a fresh effect handled outside `f`;
- **(representation independence)** two handlers whose states are related by a simulation give
  contextually equivalent programs;
- **(encapsulation)** effects handled internally are invisible to every context.

**(b) Definitions.** D12. A binary world `M₂ : SemWorld₂`, named only: a relation on pairs of
terms over pairs of resource worlds. `Expr.HndFree n e`: no `hnd (n, …)` occurs in `e`
(syntactic).

**(c) Lean.**

```lean
/-- `f`'s type at the row `S`: `U(U(A ⊸ F_S B) ⊸ F_S R)`. -/
def hofTy (A B R : VTy) (S : Row) : VTy :=
  .thunk (.arr (.thunk (.arr A (CTy.effOf S B))) (CTy.effOf S R))

/-- **Tunnelling** (Zhang–Myers, Example 1).  `f` is typed once, polymorphic in its callback's row
`ρ`; the name `n` is fresh for `f` (site freshness, decision 57 R3).  Handing `f` the pure
`λa. c a` at `ρ := []` is equivalent to handing it `λa. perform (n, 0) a` at `ρ := {n}` and
handling `n` outside by a clause that answers with `c`: even an `f` that handles effects of its
own cannot intercept `n`. -/
def Tunnel (J : TypingJ) (P : Platform) : Prop :=
  ∀ (f c : Val) (ρ : RVar) (k : RowCon) (A B R : VTy) (n : UInt32),
    let op : OpSig := ⟨n, 0, .lin, A, B⟩
    n ≠ 0 → k.cls.Admits [] → k.cls.Admits [op] → k.adm op →
    J [(ρ, k)] LifeCtx.empty (fun _ => []) (.val f) (fun η => .val (hofTy A B R (η ρ))) →
    J.at LifeCtx.empty [] (.val c) (.val (.bang (.thunk (.arr A (.ret B))))) →
    (f.1).HndFree n →
    CtxEquiv J P (.ret R)
      (thunkF (.app (.val f) (.val ⟨.lam (.app (.val c) (.var 0)), .lam⟩)))
      (thunkF (hndE (hndVal n ⟨.lam (.var 0), .lam⟩ (Val.pair (tailClause c) .unit))
        (.app (.val f) (.val ⟨.lam (performE (opArgE n 0 (.var 0))), .lam⟩))))

/-- **Representation independence**: T2's `Hiding`, at answering handlers, whose operations are
the only access to their states. -/
abbrev RepInd (J : TypingJ) (P : Platform) : Prop := Hiding J P

/-- **Encapsulation**: two closed computations at a data answer, every effect of each handled
inside it, that every platform observes alike, are contextually equivalent. -/
def Encap (J : TypingJ) (P : Platform) : Prop :=
  ∀ e₁ e₂ A, A.Data → J.closed e₁ (.ret A) → J.closed e₂ (.ret A) →
    (∀ P', P'.Respects → Obs P' A e₁ = Obs P' A e₂) →
    CtxEquiv J P (.ret A) (thunkF e₁) (thunkF e₂)

/-- **T3.** -/
def Abstraction (J : TypingJ) : Prop := ∀ P, P.Respects → Tunnel J P ∧ RepInd J P ∧ Encap J P
```

**The proof device, named-only.** T3 is a corollary of a binary fundamental lemma, as T1 is of
the unary one. Its statement needs a binary world `M₂ : SemWorld₂` (a relation on pairs of terms
over pairs of resource worlds) and its judgment `SemW₂`, which this design does not define (OQ-4:
a binary relation over Core's world is optional). Named-only, excluded from the elaboration check:

- `FL₂ M₂ J`: every judgment of `J` relates its term to itself in `SemW₂ M₂`
  (Zhang–Myers Thm 1's shape);
- `Adequate₂ M₂ J`: two closed thunks related in `SemW₂ M₂` at `U C` are `CtxApprox J P C`
  (their Thm 3's shape);
- `AbstractionOfFL₂`: `FL₂ M₂ J → Adequate₂ M₂ J → Abstraction J`.

`Encap` is the survey's B1 corollary ("two implementations that differ only in encapsulated
internal effects are contextually equivalent").

**(d) Literature.** Zhang–Myers, POPL 2019:

- abstract: "it is impossible for higher-order, effect-polymorphic code to accidentally handle
  effects raised by functions passed in";
- §6, Example 1: for `f` "with an effect-polymorphic type T = ∀α . (N → [N]α) → [N]α", the terms
  "t1 = f [∅] (λx : N. x + x)" and the handled "try { f(g) } with twice(x) { resume (x + x) }" are
  contextually equivalent; "this equivalence should apply to all possible (well-typed)
  implementations of f, so even if the implementation handles F internally, the clients are unable
  to make different observations";
- Thm 1 (Parametricity, a.k.a. Fundamental Property): "∆ | P | Γ | Ξ ⊢ t : [T]e ⇒ ∆ | P | Γ | Ξ ⊢
  t ≼log t : [T]e";
- Thm 3 (Soundness): "t1 ≼log t2 … ⇒ t1 ≼ctx t2";
- "Type safety … falls out as an easy corollary of Adequacy and Parametricity."

`Tunnel` is Example 1 at our kernel, with `c` in place of `x + x`. Zhang–Myers obtain it from
tunnelling semantics; in our kernel, handlers are found by static site names, so the role of
tunnelling is played by site freshness (`HndFree`, decision 57 R3) and the row typing of
`[handle]` (`hnS`).

**(e) Existing Lean.** None in Core. EffModelRel has a binary relation with `fundamental`/
`soundness` [SIB]. Site freshness is checked by the elaborator (decision 57 R3).

**(f) Non-vacuity.** `Tunnel`'s hypotheses are met by every HOF typed generically in its
callback's row whose own handlers use other names, with `k = ⟨.any, fun _ => True⟩`.

**(g)** Out of the first pass (OQ-4: binary is optional). It is stated at full strength, over
row-polymorphic `f`.

### T4. Lowering and zero cost (cross-language) — notebook P13

**World:** [prog] and the backend's IRs.

**(a) Statement.** Two statements:

- **(LoweringCorrect)** the erased lowering preserves behaviour: a closed well-typed program that
  runs to a value lowers to a program whose run prints what the source's run prints;
- **(ZeroCost)** handling adds no cost of its own: in each lowering class the lowered program
  allocates and makes dispatched calls no more than the class's reference encoding, the code a C
  or Rust programmer writes by hand:
  - an answering operation: a direct call of its clause on the passed state (I4's borrow form);
  - an abortive operation: an early return through a sum, a branch per call;
  - a control operation: a hand-written state machine.

**(b) Definitions.** The kernel lowering `Backend.closTypesOfExpr` (`Backend/Driver.lean:237`:
convert, capture, unwind, collapse) and `Flat.lower`. The flat interpreter's counters
`FState.allocs` and `FState.indirect` (`Backend/Flat/Interp.lean:31-34`): the objects a run
allocates and its dispatched calls.

**(c) Lean: named-only.** Both statements need definitions this design does not give: a
fuel-parametric interpreter of the lowering's stages, a run of the flat stage that reports its
counts, and each class's reference encoding. They are recorded named-only and excluded from the
elaboration check until the backend exposes them; their shapes are:

- `LoweringCorrect J` (Ma et al.'s Cor. 1 shape, at the flat stage): for every closed `e`
  with `J.closed e (.ret A)` at a data `A` that runs to a value from the empty memory, there is a
  fuel beyond which `stageRun "flat" fuel e = stageRun "source" fuel e`.
- `ZeroCost J`: for every lowering class `c`, every closed `e` of the class (`c.Of e`) with
  reference encoding `e'` (`c.ref e = some e'`), and every fuel at which both run to the end, the
  flat counts of `e` are at most those of `e'`, objects allocated and dispatched calls each.

The missing definitions:

- `stageRun stage fuel e`: a fuel-parametric copy of `Backend.interpStageExpr`
  (`Backend/Driver.lean:246`);
- `flatCounts fuel e`: runs `Flat.lower p true T` by `callFn` and reads `(allocs, indirect)`
  from the final `FState`;
- `LowClass.Of` and `LowClass.ref`, over `inductive LowClass | answering | abortive | control`:
  - `answering`: every clause a `tailClause`; its reference encoding replaces every
    `perform (n, i) a` by `c_i a` for the handler's `tailClause c_i`, the answer clause applied to
    the result;
  - `abortive`: every operation abortive, which is a fact about types, not syntax, so `Of` needs
    the handler's row; its reference encoding returns `inj₂ (i, v)` through each enclosing `let`
    by a `case`, the handler's `case` dispatching to its clause;
  - `control`: no reference encoding until OQ-23 is answered.

The source's reference interpreter must agree with `Steps` on terminating runs
(`sourceRun_sound`), an obligation of `LoweringCorrect`'s proof, not of its statement.

**(d) Literature.** Ma–Ge–Jung–Zhang, OOPSLA 2025:

- Thm 1 (Simulation): "Given a well-typed SL configuration M and a TL configuration M such that
  M ∼ M, if M ⟶ M′, then there exists a TL configuration M′ such that M ⟶∗ M′ and M′ ∼ M′".
- Cor. 1 (Semantics Preservation): "if a closed, well-typed SL program terminates with a value,
  then its translation in TL also terminates and produces the expected result".

**(e) Existing Lean.**

- The lowering compiles and runs (`bcc kernel`, `Backend/Kernel.lean`).
- The counts are in `corpus/counts.expected` and `corpus/kernel-counts.expected`, checked by
  `bcc-counts` against both the flat interpreter and `wasmtime`.
- There is no theorem.

**(f) Non-vacuity.** The kernel programs `bcc kernel` compiles meet the hypotheses; `loopTail`
(tail-resumptive) and `failOutside` (abortive) are instances of the two stated classes.

**(g)** Out of the first pass. Whether lowering correctness is a theorem, and the cost model of
the control class, are OQ-23, which needs the user. The answering class rests on I4 and `LawTail`.

---

## 4. The proof device: the fundamental lemma at W

### 4.1 FL and adequacy

**World:** [W], at the end state's `M`.

**(a) Statement.**

- **FL:** every judgment of the typing system holds in W's relation, at every admissible instance.
- **Adequacy:** a closed computation in W's relation is safe and terminating under every platform
  (or safely driven).
- So Soundness is a corollary of FL. Adequacy follows from the laws of §4.2, so FL is the only
  hard theorem.

**(b) Definitions.** §1.3, D5–D8.

**(c) Lean.**

```lean
def FL (M : SemWorld) (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, J Θ Δ Γ e j → SemW M Θ Δ Γ e j

def AdequateRetAt (M : SemWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A : VTy) (e : Expr), DivFree S A → RowLe S P.ops →
    M.comp (CTy.effOf S A) ([], M.nil) LSub.empty e PMap.empty → SafeRuns P A e ∧ Terminates P A e
def AdequateDriveAt (M : SemWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A B : VTy) (e : Expr), A.Data → RowLe S P.ops →
    M.comp (CTy.effOf S (.thunk (CTy.loopEff S A B))) ([], M.nil) LSub.empty e PMap.empty →
    SafeDrive P A e
def AdequateAt (M : SemWorld) (P : Platform) : Prop := AdequateRetAt M P ∧ AdequateDriveAt M P
def Adequate (M : SemWorld) : Prop := ∀ P, P.Respects → AdequateAt M P

/-- The generic composition lemmas, as targets; each is proved once, for every `M` and `J`. -/
def SoundnessOfFL : Prop := ∀ M J, FL M J → Adequate M → Soundness J
def SoundnessContractsOfFL : Prop :=        -- corrected, §Corrections C2
  ∀ M J, FL M J → ExtPre M → Conservative M → Adequate M → SoundnessContracts J
def SoundnessContractsOfFLWB : Prop :=      -- the route as first designed, at row-abortive externs
  ∀ M J, FL M J → ExtPre M → ConservativeWB M → Adequate M → SoundnessContractsAR J
def EffSafeOfFL : Prop := ∀ M J, FL M J → WLaws M → EffSafe J
def AdequateOfLaws : Prop := ∀ M, WLaws M → ShareResume M → Adequate M
```

**(d) Literature.**

- [TR] 6.151: "If ∆; Γ ⊢ e ∶ T then ∆; Γ ⊧ e ∶ T."
- [CONF] 415:17–18: "The Fundamental Property is just one part of the overall proof of semantic
  type soundness … we must show adequacy of the weakest precondition".
- Zhang–Myers (T3 above): type safety "falls out as an easy corollary of Adequacy and
  Parametricity".

**(e) Existing Lean, and what to prove now.**

- `fundamentalC` (`Core/Fundamental.lean:434`) is `FL coreW tier1`, through the transports, at
  every instance. PROVED AT σ=[].
- `theorem32D` (`Core/Demonic.lean:292`) is the core of `AdequateRetAt coreW Platform.none`.
- `SoundnessOfFL`, `SoundnessContractsOfFL`, `EffSafeOfFL` are generic composition.
- `AdequateOfLaws` is `wpTS_demonic`/`theorem32D`'s replay-and-reclaim argument over `wpGW`. It
  never inspects `Fam` beyond the empty world, and it chains runs across platform answers by
  `ShareResume` at the same index (`ExtPre`'s reflexivity) at resource-free answers (`DataVals`).
  Platform operations are linear, so the rows it reads are unr-free. Generic. Prove the
  `Platform.none`, non-loop part first.
- `FL M J` at the end state: OPEN.

**(f) Non-vacuity.** `CDerives` has closed derivations at data answers (T1 (f)), and `coreW`
satisfies the laws.

**(g)** In the first pass, as the proof device.

### 4.2 The laws every W satisfies

These are conjuncts of `Guarantees` about the end state's `M`, [W]. Each holds of `coreW`, mostly
by unfolding. Together they bound the relation from above at **every** index and every type
former: data values are exactly data (`DataVals`), a computation of `F_Σ A` at an unr-free row is
exactly W's runs (`EffInterp`), every other former is bounded by its eliminations and its shape
(`RelLaws`; at `Imm` and `Mut` by Core's own clauses, with W's relation for the payload), and
every run from every configuration W reaches is safe (`AdequateEvery`). With `LifetimeSound` (P9,
at every index) no conjunct of the end state can be met by an over-approximating relation.

At an index where no configuration arises (`M.Fam` empty there), the relation is unconstrained,
and nothing reads it: every quantifier over configurations in `wpGW` ranges over `M.Fam`, and
every index a run reaches has a configuration, the run's own end. At a row holding a resuming
`unr` operation the relation is unconstrained too, and only FL's structural cases pass values of
such types along (§0). So the bounds bind exactly where the relation is used.

```lean
mutual
/-- Every effect layer anywhere in the type is abortive: the operations a callback of this type
can perform are in `{fn, abort}` (answering effects are borrows, not rows; I4). -/
def VTy.AbortRows : VTy → Prop
  | .tensor A B | .sum A B => A.AbortRows ∧ B.AbortRows
  | .thunk C => C.AbortRows
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .mu A | .fam A => A.AbortRows
  | .unit | .zero | .unk | .tvar _ | .int _ | .opq _ => True
def CTy.AbortRows : CTy → Prop
  | .ret A => A.AbortRows
  | .arr A C => A.AbortRows ∧ C.AbortRows
  | .amp C D => C.AbortRows ∧ D.AbortRows
  | .top => True
  | .all _ _ C | .nu C => C.AbortRows
  | .eff _ _ q A B C => (B.isZero && q != .lin) = true ∧ A.AbortRows ∧ B.AbortRows ∧ C.AbortRows
end

/-- **The nil slice, structurally**: at σ = [] nothing is held, the configurations, the order
and the stop are Core's, and a stored payload is read at σ = []. -/
def SliceShape (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔
     (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)) ∧
  (∀ b, M.payStk b M.nil = M.nil)

/-- **Mono**: Kripke monotonicity of the value relation, in both modes. -/
def Mono (M : SemWorld) : Prop :=
  ∀ b A i i' δ v ρ, M.Ext i i' ρ → M.val b A i δ v ρ → M.val b A i' δ v ρ

/-- The Kripke order is a preorder. -/
def ExtPre (M : SemWorld) : Prop :=
  (∀ i ρ, M.Ext i i ρ) ∧ (∀ i i' i'' ρ, M.Ext i i' ρ → M.Ext i' i'' ρ → M.Ext i i'' ρ)

/-- **EffInterp**: an unr-free row is read through its protocol ("opTable is the
interpretation"). -/
def EffInterp (M : SemWorld) : Prop :=
  ∀ S R i δ e ρ, S.NU → (M.comp (CTy.effOf S R) i δ e ρ ↔
    ewpW M i e (opTabW M (rowTabW M S δ)) (fun j v => M.val true R j δ v) ρ)

def FamEmpty (M : SemWorld) : Prop := M.Fam PMap.empty [] ([], M.nil)

def DataVals (M : SemWorld) : Prop :=
  ∀ b A i δ v ρ, A.Data → (M.val b A i δ v ρ ↔ ρ = PMap.empty ∧ DataVal A v)

/-- The share is monotone in what it owes, at non-`unr` entries, so `opTabW` is monotone at
unr-free tables and `ewpW` unfolds (`opTable_mono`, `Core/EffWp.lean:951`). -/
def ShareMono (M : SemWorld) : Prop :=
  ∀ T en n i K (Φ Φ' : Idx M.Stk → Expr → WProp) ρ, en.q ≠ .unr → (∀ i e ρ, Φ i e ρ → Φ' i e ρ) →
    M.share T en n i K Φ ρ → M.share T en n i K Φ' ρ

/-- The eliminations, at the same index.  None has a `M.Ext` quantifier, so each holds under
either option of OQ-8: with the future-world quantifier at `U` (Core's), by `ExtPre`'s
reflexivity; at the binder clauses, by definition. -/
def RelElim (M : SemWorld) : Prop :=
  (∀ C i δ v ρ, M.val true (.thunk C) i δ v ρ → M.comp C i δ (forceE C (.val v)) ρ) ∧
  (∀ A C i δ e ρ, M.comp (.arr A C) i δ e ρ →
     ∀ v, (M.val true A i δ v ─⋆ M.comp C i δ (.app e (.val v))) ρ) ∧
  (∀ C D i δ e ρ, M.comp (.amp C D) i δ e ρ →
     M.comp C i δ (.app e (.val (Val.inj₁ .unit))) ρ ∧ M.comp D i δ (.app e (.val (Val.inj₂ .unit))) ρ) ∧
  (∀ x b C i δ e ρ, M.comp (.all x b C) i δ e ρ → ∀ α, LtLife δ b α →
     M.comp C i (δ.extend x α) (.app e (.val .unit)) ρ) ∧
  (∀ C i δ e ρ, C.NuOk → M.comp (.nu C) i δ e ρ → M.comp C.unroll i δ e ρ) ∧
  (∀ b A i δ v ρ, M.val b (.mu A) i δ v ρ → M.val b (VTy.inst (.mu A) A) i δ v ρ)

/-- **The shapes of values**, at the same index: `vCE`'s clauses (`Core/Relation.lean:119-150`),
with W's relation in place of `vCE`'s recursive calls.  At `Imm` and `Mut` these are Core's
`ptoImmS`/`ptoMutS` clauses at W's index (`ptoImmSW`/`ptoMutSW`), with the coherence `CohE` and
the payload in W's relation: the observable view at `Imm`, the program's relation at `Mut`. -/
def RelShape (M : SemWorld) : Prop :=
  (∀ b i δ v ρ, M.val b .unit i δ v ρ → v = .unit ∧ ρ = PMap.empty) ∧
  (∀ b i δ v ρ, ¬ M.val b .zero i δ v ρ) ∧
  (∀ b A B i δ v ρ, M.val b (.tensor A B) i δ v ρ →
     ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ (M.val b A i δ v₁ ⋆ M.val b B i δ v₂) ρ) ∧
  (∀ b A B i δ v ρ, M.val b (.sum A B) i δ v ρ →
     (∃ w, v = Val.inj₁ w ∧ M.val b A i δ w ρ) ∨ (∃ w, v = Val.inj₂ w ∧ M.val b B i δ w ρ)) ∧
  (∀ b A i δ v ρ, M.val b (.ref A) i δ v ρ →
     ∃ ℓ v', v = Val.loc ℓ ∧ (ptoOwn ℓ v' ⋆ M.val b A i δ v') ρ) ∧
  (∀ b A i δ v ρ, M.val b (.bang A) i δ v ρ → ρ = PMap.empty ∧ M.val true A i δ v ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.box a A) i δ v ρ → atLife δ a (fun α => box α (M.val b A i δ v)) ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.imm a A) i δ v ρ →
     atLife δ a (fun α => ex fun ℓ => ⌜v = Val.loc ℓ ∧ CohE (rsOf i.1) ℓ A δ⌝ ⋆
       ptoImmSW M ℓ α i (fun i₀ => M.val false A i₀ δ)) ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.mut a A) i δ v ρ →
     atLife δ a (fun α => ex fun ℓ => ⌜v = Val.loc ℓ⌝ ⋆
       ptoMutSW M ℓ α i (fun i₀ => M.val true A i₀ δ)) ρ) ∧
  (∀ b L i δ v ρ, M.val b (.fam L) i δ v ρ → ∃ ℓ c, v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31 ∧
     sepRange (fun m => M.val b L i δ (Val.loc m)) ℓ c.toNat ρ) ∧
  (∀ b i δ v ρ, M.val b .unk i δ v ρ → ρ = PMap.empty) ∧
  (∀ b w i δ v ρ, M.val b (.int w) i δ v ρ → v.IsInt w ∧ ρ = PMap.empty) ∧
  (∀ b k i δ v ρ, M.val b (.opq k) i δ v ρ → k.Holds v ∧ ρ = PMap.empty) ∧
  (∀ b n i δ v ρ, ¬ M.val b (.tvar n) i δ v ρ)

def RelLaws (M : SemWorld) : Prop := RelElim M ∧ RelShape M

/-- **Adequacy from every index**: from every configuration W reaches, every run of a
computation in W's relation at an unr-free row continues to a value or to a stop of the row. -/
def AdequateEvery (M : SemWorld) : Prop :=
  ∀ (i : Idx M.Stk) (fρ ρf ρ : WRes) (ps : List FrameRec) (μ : Heap) (S : Row) (A : VTy)
    (δ : LSub) (e : Expr), S.NU →
    M.Fam fρ ps i → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → ResU.Lower fρ μ →
    M.comp (CTy.effOf S A) i δ e ρ →
    ∀ μ₁ e₁, Steps μ e μ₁ e₁ → ∃ μ₂ e₂, Steps μ₁ e₁ μ₂ e₂ ∧ (IsVal e₂ ∨ StopsIn S e₂)

def WLaws (M : SemWorld) : Prop :=
  SliceShape M ∧ Mono M ∧ ExtPre M ∧ EffInterp M ∧ FamEmpty M ∧ DataVals M ∧ ShareMono M ∧
  RelLaws M ∧ AdequateEvery M
```

`FamEmpty` follows from `SliceShape` (`TW.empty`); it is kept as the name `AdequateOfLaws`
reads. `AdequateEvery` follows from `EffInterp` and `ewpW`'s shape by `wpTS_demonic`'s replay at
`wpGW`; it is stated so that the bound is explicit. `RelShape` at `Imm`/`Mut` leaves OQ-46 open
only in `payStk`, the stack the payload is read at; the record half of the payload's index is
`ptoMutS`'s own `ls₀`.

**Status at `coreW`.**

- `SliceShape`: by `rfl`.
- `Mono`: `vC_local` (`Core/RelationFacts.lean:265`), both modes.
- `ExtPre`: `Ext.refl`, `Ext.trans` (`Core/Wp.lean:142,138`).
- `EffInterp`: `cC_effOf`.
- `FamEmpty`: `TW.empty`.
- `DataVals`: `vC_data`, new and small.
- `ShareMono`: `contShare`'s monotonicity, inside `opTable_mono`.
- `RelLaws`: Core's clauses (`Core/Relation.lean:119-204`) by unfolding, through
  `ptoImmSW_core`/`ptoMutSW_core` at `Imm`/`Mut`, with `Ext.refl` at `U`; `cC_nu_iff`
  (`Core/NuRel.lean:155`) at `ν`; `vC_unfold` at `μ`.
- `AdequateEvery`: `wpG_demonic` (new: `wpTS_demonic` at `wpG`).

All are PROVED AT σ=[] once written.

**At the end state they are OPEN, and each is a real requirement.**

- `SliceShape` and `ConservativeWB` (§6 P14) are this design's reading of the sign-off's "vC/cC
  are the σ = [] instance": the nil slice is Core's in its structure, and Core's relation
  **embeds** into W at σ = [] (at row-abortive types in done, at every type beside done). It is
  not an equivalence. An equivalence `M.val b A (ls, M.nil) ↔ vCE none b A ls` at a type that a
  tier-2 value can inhabit would put that value in today's `cC`, whose `wpG` keeps R-T1 at every
  stop (`Core/EffDefs.lean:40`) and whose `↭` (`UpdV`) cannot end a run with a borrow cell it
  created (LoopBorrow's `not_upd_of_new_mut`). Under OQ-9 (a) a run from σ = [] can end with a
  lend held. That is so at abortive-row types too: a handler whose clause answers a thunk that
  resumes `κ` (`λ_. κ.resume () to t. force t`, at the answer `U(F_∅ Flag)`, a type with no row)
  returns a value holding the suspended lend of an `at02`-like body. I have not built that program
  in Lean; the design avoids the equivalence rather than rest on the argument. LoopBorrow found the
  same thing for loops: a lend spanning runs "needs a model change: a borrow that `↭` lets outlive
  the run that opens it" (`refoldKripke_false`, `refold_fails_at_consumer_frame`, a list that
  arises). §10 records the question for the user.
- `Mono` is what GhostEnd's `gRL*` lacks (`docs/effects-state/06` §2.2).

**`Mono` and OQ-8.** `Mono` is Kripke monotonicity, which is what makes W a Kripke world (the
sign-off's "one Kripke world"), and I1's stored suspensions and `ConservativeWB` read it. Under the
placement of OQ-8 that puts the future-world quantifier at `U`, `contShare` and `KapRel` (Core's),
it holds as `vC_local` does: the `U` clause quantifies over futures and `Ext` is transitive. Under
the placement at the binder clauses (`∀`, `⊸`, as GhostEnd's `vRLk` does) the `U` clause has no
quantifier, and `Mono` at `U(F_Σ A)` needs index-monotonicity of the effectful wp:

```lean
/-- What `Mono` needs at `U` when the future-world quantifier sits at the binder clauses. -/
def EwpMono (M : SemWorld) : Prop :=
  ∀ i i' e Tb Q ρ, TableI.Mono Tb → M.Ext i i' ρ → ewpW M i e Tb Q ρ → ewpW M i' e Tb Q ρ
```

Nothing proves `EwpMono` at a binder-clause candidate; GhostEnd's `gRL*` lack monotonicity. So
`Mono` constrains OQ-8: it excludes every placement under which W's relation is not monotone along
`M.Ext`, and at the binder-clause placement it asks `EwpMono`. §10 records this.

### 4.3 The one proof method

"One proof method: the fundamental lemma; 1 and 3 corollaries of it":

- T1 is `SoundnessOfFL`;
- T3 is `AbstractionOfFL₂` (named-only, §3).

No target is proved by a second route, such as syntactic progress and preservation (OQ-52 is moot
by D21).

### 4.4 No step-indexing: the audit, part of done

W's relation is defined by recursion on types and stratification by lifetime (`Life = ℕᵒᵈ`), with
least and greatest fixed points for data and codata written in `Prop` (`∀ P, … → P …` and
`∃ R, …`, as `ewpTS` and `cC`'s `ν` clause are), and no natural-number step index (decision 7).

This is a property of a **definition**, not of the laws: a W whose `Stk` carries a step index and
whose relation recurses on it could meet every law of §4.2 at σ ≠ []. `SliceShape` pins only the
nil slice. So done names its `W` (§1.0), and `audit_W` checks its definition:

- **What it scans.** A `run_meta` in `Targets/Audit.lean`, modelled on Restrat's
  (`Restrat/Audit.lean:121`), walks the constants that `W`'s fields use, transitively
  (`Expr.getUsedConstants`), stopping at Core's and Paper's definitions that Restrat's audit and
  this one already cover.
- **What it reports.** Every constant in that closure that is defined by recursion on a `Nat` (or
  `Fin`, or any type with a `Nat`-valued measure) other than a syntax size (`VTy`, `CTy`, `Expr`,
  de Bruijn indices), and every use of `Nat.iterate`, `Nat.rec` or `WellFounded.fix` at a `WProp`
  transformer: the shapes a step index takes.
- **How it passes.** The reported list is pinned (as Restrat pins its list): every entry is a
  syntax recursion the audit's docstring justifies, and the build fails if the list changes.

The audit runs on `coreW` in the first wave, which checks the audit itself on a relation known to
be step-free; it runs on `W` when `W` is built. `Status.lean` records done as PROVED only with the
audit passing.

---

## 5. The interaction interface

### I1. A suspension is a value of the resource world — notebook P3

**World:** [W]. Program-level corollary `I1Prog` (§1.0).

**(a) Statement.** At a stop at a resuming operation of the handled computation's unr-free row,
take the share the stop owes its continuation. Closed by the handler that catches the stop, it is
a value of the continuation's type `kTy`. So a suspension can be passed, stored with `Ref`, and
resumed later at any future world (`Mono`), and it is dropped only by its cancel branch.

**(b) Definitions.** D4 (`kappa`, `kTy`), §1.3 (`share`, `ewpW`, `opTabW`, `rowTabW`, `entW`).

**(c) Lean.**

```lean
/-- **I1.** -/
def I1 (M : SemWorld) : Prop :=
  ∀ (S : Row) (n : UInt32) (E : List (Qual × VTy × VTy)) (R : VTy) (δ : LSub) (hr hs : Val)
    (j : UInt32) (o : OpSig) (K : Kont) (i : Idx M.Stk) (ρ : WRes),
    n ≠ 0 → (∀ o' ∈ S, o'.n ≠ n) → (Row.ofEff n E 0 ++ S).NU →
    Row.find (Row.ofEff n E 0) n j = some o → o.abort = false →
    M.share (rowTabW M (Row.ofEff n E 0 ++ S) δ) (entW M δ o) n i K
      (fun i' t => ewpW M i' (hndE (hndVal n hr hs) t) (opTabW M (rowTabW M S δ))
        (fun i'' v => M.val true R i'' δ v)) ρ →
    M.val true (kTy S R o.q o.B) i δ ⟨kappa n (hndVal n hr hs) K, .lam⟩ ρ
```

Together with `Mono` (§4.2), I1 says the suspension is a value at every future world. Storing it
is `Ref (kTy …)`, whose shape is `ptoOwn ⋆ M.val true (kTy …)` (`RelShape`). The bound on a
stored suspension is P9.

**Program level.** `I1Prog` (§1.0): `storeCancel` (tier 1) and `at17` (tier 2, D14) store a
suspension, move it, and cancel or resume it; under the end state each is typed (`ExtendsNU`,
`AcceptsTier2`) and every run of it is safe and ends at the empty memory (`Soundness`).

**(d) Literature.**

- System C (TR version) Lemma 7: "Given a well-typed effect call ∅ ⊢ H_l[cap_l(v_i)] : τ | C ∪ {l}
  with effect signature l : τ_i → τ_0 ∈ Ξ, it follows that y : τ_0 ⊢ H_l[return y] : τ | C ∪ {l}".
  This is Lemma 4.6 in the published numbering the survey cites.
- Tang et al., POPL 2024, Thm 3.4.2: "if Δ; Γ ⊢ E[(do ℓ V)^E] : C … then there exists Δ ⊢ Γ = Γ1 +
  Γ2 such that … Δ; Γ1, y : B ⊢ E[(return y)^E] : C".
- The survey's A1: "Σ must type continuation values and the loans they hold".

Ours is the semantic form. The context split is the separating conjunction `PA ⋆ share` at the
stop, and the continuation's typing is its membership in `M.val true (kTy …)`.

**(e) Existing Lean, and what to prove now.**

- `ewp_handle`'s `[op]` case (`Core/EffRules.lean:615`) builds `KapRel` from `contShare` with the
  induction hypothesis, by `ewp_kappa_resume`, `ewp_kappa_cancel` and `ewp_ccatch`.
- `vC_kTy_of_kapRel` (`:1053`) turns `KapRel` into `vC (kTy …)`.

Extracting that case gives `I1 coreW`. PROVED AT σ=[]. Storage at σ=[] is shown by `storeCancel`.
`ewp_gen` (L14.3, branch `lift-stage1`, Core σ=[]) is evidence for the boxed form. I1 at the end
state is OPEN.

**(f) Non-vacuity.** Stops at resuming operations occur in `nLogOutside` (a native affine `log`),
in `prog`/`progC` (`Core/EffExamples.lean`), and in D14's terms.

**(g)** In the first pass.

### I2. Capture and resume preserve the invariant, including lends that span the suspension — notebook P4

**World:** [W]. The spanning typing rules and the binder's machine half are [prog].

**(a) Statement.** A preservation statement at the two constructs, including lends that span the
suspension. It does not mention termination. I2 is stated at a class `c` of rows a lend may span:
`.abortive` is tier 1, `.any` (every unr-free row) is the end state.

- **(capture)** Every configuration a run ends in arises, once the frames held by suspended
  computations are counted: at a return, at an abortive stop, and at a stop that captures a
  continuation. `TW.inv` and `TW.valid` hold of it. The visible frames and records at the run's
  end are those at its entry; whatever the run leaves open is held. Since every `ewpW` run ends in
  `M.Fam`, this is "every wp run ends in a TW world plus TW.inv", extended to W.
- **(resume)** The continuation a stop owes is resumed at every future index (`M.Ext`) at every
  answer the operation's answer relation admits, and its run starts from every configuration that
  arises there (`wpGW` quantifies over `M.Fam`).
- **(the lend frames across a stop)** [TR] 6.64 (Imm Frame) and 6.65 (Mut Frame) hold at W over
  `ewpW` at tables whose entries are of class `c`: the lend is quantified once, at the callback's
  start (`И`), and a callback that stops at a resuming operation is owed its continuation with the
  lend at the lifetime it began at. At abortive tables they are Core's `ewpTS_*_frameU`, with the
  lend ended at the stop as at a return.
- **(the spanning borrows)** The six unwinding borrow constants, lending to a callback at a row of
  class `c` that `Adm` admits, are sound at W (`SpanBorrows M O Adm c`), the cancel path of an
  affine operation included.

The tier question is a question about preservation at a construct: do the borrow constants,
lending to a callback at a row whose operations resume, preserve it? That is I2's last two
conjuncts. FL's spanning cases are `SpanBorrows`, and tier 2's typing holds the rules by
`Tier2Pinned`; `SpanBorrows` is in I2 itself, so that I2 states the spanning lends and not only
the conditions FL consumes. The stop condition's role follows from the preservation: it restores
the visible discipline, and what is held is `held`'s content (OQ-9), not a choice made at the
stop.

**(b) Definitions.** D10 (`held`, `Arises`); the six unwinding borrow constants' types
(`withbor1UTy` … `sliceBorrowIUTy`, `Core/EffBorrow.lean:177-198,525,625-630`) and `withborUE`.
New:

```lean
/-- OQ-56's question: which operations a borrow callback's row may hold, given the context and
the lend's variable. -/
abbrev OpAdm := LifeCtx → LifeVar → OpSig → Prop

/-- OQ-56 (a), R-CLOSEDOP (`Row.Unwind`'s conditions, `Core/EffBorrow.lean:133`): the
operation's types are free of `'x` and outlive every lifetime. -/
def admClosedOp : OpAdm := fun _ x o =>
  ¬ VFree x o.A ∧ ¬ VFree x o.B ∧ (∀ Δ a, VOutlives Δ a o.A) ∧ (∀ Δ a, VOutlives Δ a o.B)

/-- **The lower bound on `Adm`**: it admits at least what today's unwinding constants admit.
Without it, `Adm := fun _ _ _ => False` would make every spanning rule the pure constant and the
end state hold with no spanning rule at all. -/
def AdmExtends (Adm : OpAdm) : Prop := ∀ Δ x o, admClosedOp Δ x o → Adm Δ x o

/-- A row a lend may span: every operation named, no resuming operation unrestricted, and every
operation admitted. -/
def RowSpan (Adm : OpAdm) (Δ : LifeCtx) (x : LifeVar) (S : Row) : Prop :=
  ∀ o ∈ S, o.n ≠ 0 ∧ (o.abort = true ∨ o.q ≠ .unr) ∧ Adm Δ x o

/-- The entries of a table of class `c` with no abortive entry: resuming, unr-free, and linear at
`.resumeOnce`; at `.abortive` there is no such entry, so the table is empty. -/
def OpTabI.Resuming {I} (c : RowClass) (T : OpTabI I) : Prop :=
  ∀ n j en, T n j = some en → en.abort = false ∧ en.q ≠ .unr ∧ c ≠ .abortive ∧
    (c = .resumeOnce → en.q = .lin)
```

`RowSpan admClosedOp Δ x S ∧ RowClass.abortive.Admits S ↔ S.Unwind x`
(`rowSpan_abortive_iff_unwind`: an abortive operation's answer is `0`, free of `'x` and
outliving every lifetime).

**(c) Lean.**

```lean
/-- **I2, capture**: every configuration W reaches is a tagged `TW` world over the visible and
the held frames and records. -/
def Arises (M : SemWorld) : Prop :=
  ∀ fρ ps i, M.Fam fρ ps i →
    ∃ ps₀ ls₀, (∀ p, p ∈ ps₀ ↔ p ∈ ps ∨ p ∈ (M.held i).1) ∧
      (∀ x, x ∈ ls₀ ↔ x ∈ i.1 ∨ x ∈ (M.held i).2) ∧
      TW fρ ps₀ (rsOf ls₀) ∧ Tagged fρ ps₀ ls₀

/-- **I2, the stop's role**: at every end of a run the visible frames and records are those at
its entry. -/
def StopVisible (M : SemWorld) : Prop :=
  ∀ ps i ps' i' t, M.Stop (ps, i) (ps', i') t →
    (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ i'.1 ↔ x ∈ i.1)

/-- **I2, resume**: `contShare`'s resume conjunct at W, at non-`unr` entries. -/
def ShareResume (M : SemWorld) : Prop :=
  ∀ T en n i K Φ ρ, M.share T en n i K Φ ρ → en.q ≠ .unr → ∀ i', M.Ext i i' ρ →
    ∀ w : Val, (en.PB i' w ─⋆ Φ i' (K.plug (.val w))) ρ
```

`ShareResume` is stated at every `M.Ext`-future index, transcribing `contShare`. That is a
property both options of OQ-8 have, not a placement: with the quantifier at the share it is the
definition; with it at the binder clauses it follows from the same-index conjunct and the share's
Kripke monotonicity, which I1 and `Mono` require of a stored suspension.

**The lend frames at W.** Two shapes, transcribed from the Core lemmas they generalise:

- at an **abortive** table, the lend ends at the stop as at a return, and the callback's premise
  boxes the whole post, stops included (`ewpTS_I_frameU`, `ewpTS_M_frameU`,
  `Core/EffWp.lean:828,842`);
- at a **resuming** table of class `c`, the lend is quantified once, at the callback's start, and
  a stop of the callback owes its continuation the lend at the lifetime it began at: GhostEnd's
  `O151AsStated` (`Open.lean:76`, 6.65 "as `docs/effects-tr/15-mut-cell.md` prints it") and its
  `Imm` analogue (`wpG_I_frameX`'s premise over `ewpW`). GhostEnd proves, at Core's `ewpTS`, the
  re-lendable variants `ewpTS_M_frameR` (`GhostEnd/Relend.lean:117`) and `ewpTS_I_frameR`
  (`ImmLend.lean:175`), whose premise is a callback re-lent at a fresh lifetime at each
  resumption (the ghost end, OQ-9 (b)'s shape). The end state asks the stated shape, the printed
  rule with `wp` allowed to stop and the `И` taken once: under OQ-9 (a) it is the lend carried
  open; under (b) whether the re-lendable variant gives it is open (`O151AsStated`, "I have not
  derived the stated form from the variant"). If (b) cannot give it, these conjuncts decide OQ-9
  for (a); §10 records this.

A table that mixes abortive and resuming entries is the unwinding constants' business, with their
finaliser (`SpanBorrows`); the plain frames are stated at the two pure shapes.

```lean
def TableI.Abortive {I} (Tb : TableI I) : Prop :=
  ∀ i t (Φ Φ' : I → Expr → WProp) ρ, Tb i t Φ ρ → Tb i t Φ' ρ
/-- A value in `Q`, or a stop owing nothing (`ewpPost`, `Core/EffWp.lean:807`). -/
def ewpPostW {I} (Tb : TableI I) (Q : I → Val → WProp) : I → Expr → WProp :=
  fun i t ρ => valPostI Q i t ρ ∨ Tb i t (fun _ _ _ => False) ρ

/-- **6.65 at W at an abortive table** (`ewpTS_M_frameU` at W). -/
def MutFrameUW (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (β : Life), Tb.Abortive →
    (∀ i w σ, M.val true A i δ w σ → σ.InStratum β) →
    ∀ (v : Val) (e : Expr) (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp),
      Entails
        (ptoOwn l v ⋆ M.val true A i δ v ⋆
          fresh (fun α => ptoMutSW M l α i (fun i₀ => M.val true A i₀ δ) ─⋆
            wpGW M i e (fun i'' t =>
              box α (all fun w => ptoOwn l w ─⋆ (M.val true A i'' δ w ─⋆ ewpPostW Tb Q i'' t)))))
        (ewpW M i e Tb Q)

/-- **6.64 at W at an abortive table** (`ewpTS_I_frameU` at W). -/
def ImmFrameUW (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (v : Val) (e : Expr)
    (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp), Tb.Abortive → AdmWf A δ →
    (∀ i₁ i₂ t ρ, M.Ext i₁ i₂ ρ → ewpPostW Tb Q i₁ t ρ → ewpPostW Tb Q i₂ t ρ) →
    Entails
      (ptoOwn l v ⋆ M.val true A i δ v ⋆
        fresh (fun α ρ => ∀ ls', AddAt i.1 ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = A ∧ r.δ = δ) →
          (ptoImmSW M l α (ls', i.2) (fun i₀ => M.val true A i₀ δ) ─⋆
            wpGW M (ls', i.2) e (fun i'' t =>
              box α (ptoOwn l v ─⋆ (M.val true A i'' δ v ─⋆ ewpPostW Tb Q i'' t)))) ρ))
      (ewpW M i e Tb Q)

/-- **6.65 at W at a resuming table of class `c`, the lend quantified at the callback's start**
(`O151AsStated` at W). -/
def MutFrameW (M : SemWorld) (c : RowClass) : Prop :=
  ∀ (T : OpTabI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (β : Life), T.Resuming c →
    (∀ i w σ, M.val true A i δ w σ → σ.InStratum β) →
    ∀ (v : Val) (e : Expr) (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp),
      Entails
        (ptoOwn l v ⋆ M.val true A i δ v ⋆
          fresh (fun α => ptoMutSW M l α i (fun i₀ => M.val true A i₀ δ) ─⋆
            ewpW M i e (opTabW M T) (fun i'' v' =>
              box α (all fun w => ptoOwn l w ─⋆ (M.val true A i'' δ w ─⋆ Q i'' v')))))
        (ewpW M i e (opTabW M T) Q)

/-- **6.64 at W at a resuming table of class `c`, the lend quantified at the callback's start.**
`hQ` and the table's stops carried along `M.Ext` are 6.64's `hQ` (`opTable_extR` at a resuming
table, `GhostEnd/Frames.lean:32`). -/
def ImmFrameW (M : SemWorld) (c : RowClass) : Prop :=
  ∀ (T : OpTabI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (v : Val) (e : Expr)
    (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp), T.Resuming c → AdmWf A δ →
    (∀ i₁ i₂ w ρ, M.Ext i₁ i₂ ρ → Q i₁ w ρ → Q i₂ w ρ) →
    (∀ i₁ i₂ t Φ ρ, M.Ext i₁ i₂ ρ → opTabW M T i₁ t Φ ρ → opTabW M T i₂ t Φ ρ) →
    Entails
      (ptoOwn l v ⋆ M.val true A i δ v ⋆
        fresh (fun α ρ => ∀ ls', AddAt i.1 ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = A ∧ r.δ = δ) →
          (ptoImmSW M l α (ls', i.2) (fun i₀ => M.val true A i₀ δ) ─⋆
            ewpW M (ls', i.2) e (opTabW M T) (fun i'' v' =>
              box α (ptoOwn l v ─⋆ (M.val true A i'' δ v ─⋆ Q i'' v')))) ρ))
      (ewpW M i e (opTabW M T) Q)

/-- The lend frames at W, at class `c`.  At `.abortive` the resuming tables are empty, and the
resuming conjuncts are 6.64 and 6.65 at a table with no stop. -/
def FramesW (M : SemWorld) (c : RowClass) : Prop :=
  ImmFrameUW M ∧ MutFrameUW M ∧ ImmFrameW M c ∧ MutFrameW M c
```

**The spanning rules (tier 2's pin) and their FL cases.** The typing rule is `CDerives.withbor2U`
(`Core/Fundamental.lean:264`) with `S.Unwind x` replaced by `RowSpan Adm Δ x S`, at row families,
and its outlives side condition read at `J.out`:

```lean
def SpanRule2 (J : TypingJ) (Adm : OpAdm) : Prop :=
  ∀ Θ Δ (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (S : RowEnv → Row) (d : Expr) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η) ∧ (∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) ∧
      ¬ VFree x (A η) ∧ ¬ VFree x (B η) ∧ RowSpan Adm Δ x (S η)) →
    Δ.find? x = none → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.ref (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (withbor2UTy x Δ.meetOfDom (A η) (B η) (S η)))

/-- Its semantic case at W, at the outlives judgment `O`: the premises in W's relation give the
conclusion. -/
def SpanWithbor2 (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → (∃ b, Δ.Defines b ∧ O.le Δ b A) →
    ¬ VFree x A → ¬ VFree x B → RowSpan Adm Δ x S → c.Admits S → closedAt 0 d = true →
    SemW₀ M Δ Γ d (.val (.lolli (.ref A) .unit)) →
    SemW₀ M Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))
```

The other five are the same transcription of their `CDerives` constructors
(`Core/Fundamental.lean:258-293`), each with `hS : S.Unwind x` replaced by `RowSpan Adm Δ x S`
(and, in the semantic form, `c.Admits S`), and every outlives side condition read at `J.out`
(at `O` in the semantic form):

| constant | source | lend | finaliser premise | other premises |
|---|---|---|---|---|
| `withbor1U` | `Ref A` | `Imm 'x A` | `d : Ref A ⊸ 1` | `VScoped Δ A` |
| `withbor2U` | `Ref A` | `Mut 'x A` | `d : Ref A ⊸ 1` | `∃ b, Δ.Defines b ∧ J.out.le Δ b A` (Core's `VOutlivesLe`) |
| `withbor3U` | `Mut @a A` | `Mut 'x A` | `d : Mut @a A ⊸ 1` | — |
| `withloadU` | `Imm @a A` | `Imm̲ 'x A` (the reborrow, `VTy.immReborrow`); the answer is `B` alone | none (its own term, `withload`) | — |
| `sliceBorrowMU` | `Array A` | `[Mut 'x A]` | `d : Array A ⊸ 1` | both side conditions |
| `sliceBorrowIU` | `Array A` | `[Imm 'x A]` | `d : Array A ⊸ 1` | `VScoped Δ A`, both side conditions |

```lean
def SpanRules (J : TypingJ) (Adm : OpAdm) : Prop :=
  SpanRule1 J Adm ∧ SpanRule2 J Adm ∧ SpanRule3 J Adm ∧ SpanRuleLoad J Adm ∧
  SpanRuleSliceM J Adm ∧ SpanRuleSliceI J Adm
def SpanBorrows (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  SpanWithbor1 M O Adm c ∧ SpanWithbor2 M O Adm c ∧ SpanWithbor3 M O Adm c ∧
  SpanWithload M O Adm c ∧ SpanSliceM M O Adm c ∧ SpanSliceI M O Adm c

/-- **Tier 2's pin**: the typing system holds the spanning rules at every row a lend may span,
the affine (cancellable) operations included. -/
def Tier2Pinned (J : TypingJ) (Adm : OpAdm) : Prop := SpanRules J Adm

/-- The tier-2 acceptance programs (D14). -/
def AcceptsTier2 (J : TypingJ) : Prop :=
  J.closed at02 (.ret Flag) ∧ J.closed at04 (.ret (.tensor Flag Flag)) ∧
  J.closed at12 (.ret Flag) ∧ J.closed at17 (.ret Flag)

/-- **I2**, at the outlives judgment `O`, the admissibility `Adm` and the class `c` of rows a lend
may span: capture, the stop's role, resume, the lend frames, and the spanning borrows. -/
def I2 (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  Arises M ∧ StopVisible M ∧ ShareResume M ∧ FramesW M c ∧ SpanBorrows M O Adm c
```

In `Guarantees`, I2 is `I2 M J.out Adm c`. `FL M J ∧ Tier2Pinned J Adm` also gives
`SpanBorrows M J.out Adm .any` (each rule's FL case); `SpanBorrows` is a conjunct of I2 so that
the spanning lends are part of I2's own statement. At `S = []` the rules are the pure constants,
which the sign-off's "one borrow per printed constant, over any well-formed row" turns into
instances. A wider `Adm` makes `SpanRules`, `SpanBorrows` and `EndStateAt` stronger
(`spanRules_mono`); `AdmExtends` bounds it below (§1.0).

**Program level.** `I2Prog` (§1.0): `ExtendsNU J ∧ Tier2Pinned J Adm ∧ Soundness J` makes every
program that lends across a resuming operation through the spanning rules typed, safe and
leak-free, AT02, AT04 and AT12 among them.

**(d) Literature.**

- [TR] 6.65 (p. 24): "ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Mut α P̂ –⋆ wp(e){[α] ∀v′. ℓ ↦ v′ –⋆ P̂(v′) –⋆ Q̂}) ⊧
  wp(e){Q̂}". 6.64 and 6.66 have the same shape. `MutFrameW` and `ImmFrameW` are this rule with
  `wp` allowed to stop and resume, the `И` still taken once; the spanning rules are what the
  borrow constants built on it become.
- System C Thm 5 (Preservation): "If ∅ ⊢ s : τ | ∅ and s ⟼ s′ then ∅ ⊢ s′ : τ | ∅". Ours is the
  semantic form: the post-world of every run is in the family, and the family arises.

**(e) Existing Lean, and what to prove now.**

- `Arises coreW`: `Fam` is `TW ∧ Tagged` and nothing is held (`ps₀ = ps`, `ls₀ = ls`); by
  unfolding. Its held part is vacuous at σ = [], so it is recorded with I2 below, at a
  restriction.
- `StopVisible coreW`: `Stop` is R-T1; by `rfl`.
- `ShareResume coreW`: `contShare`'s resume conjunct; by unfolding.
- `FramesW coreW .abortive`: `ImmFrameUW`/`MutFrameUW` are `ewpTS_I_frameU`/`ewpTS_M_frameU`
  through the transports; `ImmFrameW`/`MutFrameW` at `.abortive` quantify over empty tables, and
  are `wpG_I_frameX`/`wpG_M_frameX` at a table with no stop (`ewp_bot`). PROVED AT A RESTRICTION
  once written.
- `SpanBorrows coreW OutJ.core admClosedOp .abortive` is the six compatibility lemmas
  `withbor1U_compatX` … `sliceBorrowIU_compatX` (`Core/EffBorrow.lean:446,275,356,548,645,726`).
  PROVED AT A RESTRICTION (abortive rows, R-CLOSEDOP).
- So `I2 coreW OutJ.core admClosedOp .abortive` is **PROVED AT A RESTRICTION** (abortive rows),
  not PROVED: at σ = [] nothing is held, and no lend spans a stop.
- At resuming rows, at σ=[]:
  - the instances `withbor_spans_yields_cC`, `imm_spans_yield` and `nested_spans_yield` (GhostEnd,
    by ghost-end) are PROVED; `withbor_spans_yields_cC` is AT02's lend through the pure
    `withbor`, in Core's `cC`;
  - the re-lendable frames `ewpTS_M_frameR`, `ewpTS_I_frameR` are PROVED; the stated shapes,
    `O151AsStated` (`MutFrameW coreW .resumeOnce`'s content, through the transports) and its
    `Imm` analogue, are OPEN;
  - WorldW batch 1 has resource-level hand-on and exit lemmas [probe].

I2 at the end state is OPEN. It is the next track by the register's rule.

**(f) Non-vacuity.**

- `RowSpan admClosedOp` and `.resumeOnce` are met by a linear `yield : I32 ↠^lin 1` and by
  `fooSig`; `.any` also by the affine `suspSig`.
- `OpTabI.Resuming .resumeOnce` is met by the table of `[fooSig]`, and `.any` by that of
  `[suspSig]`.
- The premises of `SpanWithbor2` are met by `withbor_spans_yields_cC`'s program; `AcceptsTier2`
  is met by any `J` with `ExtendsNU` and the spanning rules at `admClosedOp`.

**(g)** In the first pass.

**The freeze binder (I2.c): a target beside done.** "Freeze is a binder over internal locations,
lifetimes and instances; resume and placement instantiate it" (user, 2026-10-04). The notebook
lists what it unifies as "hypotheses to check", and the brief asks that I2 be stated so that the
reading is **available**, without presupposing the hard proof. So the binder is its own target at
the same `M`, not a conjunct of done (§1.0's `EndStateBinder` adds it): I2 is compatible with it
(its fields are the ones the binder acts on) and does not depend on it, and a W that meets every
guarantee and fails the binder still meets done.

Its two halves have different strengths:

- **locations** are a symmetry: a block-affine permutation is invertible, so its clauses are `↔`;
- **lifetimes** are instantiation: a re-stratification `θ : Restrat.Emb c` is injective and not
  surjective, so its clauses are forward implications, the bound lifetimes moved to their images
  beneath the resumer's own. Reflection along a non-surjective `θ` is not what instantiation needs.

```lean
/-- **The binder, location half, machine**: a run whose arrays lie in blocks `π` moves as
blocks renames to a run. -/
def BinderMachine : Prop :=
  ∀ (π : Equiv.Perm Loc) (rs : Ranges) μ e μ' e', BlockAffine π rs → StepsIn rs μ e μ' e' →
    StepsIn (fun q => ∃ p, rs p ∧ q = (π p.1, p.2)) (μ.renameLoc π) (e.renameLoc π)
      (μ'.renameLoc π) (e'.renameLoc π)

/-- **The binder at W, locations**: equivariance under a block-affine permutation of a
configuration that arises.  `r₁ ⊔ r₂` is the union of two `Ranges`. -/
def FreezeBinderLoc (M : SemWorld) (a : StkAct M) : Prop :=
  (∀ π fρ ps i, BlockAffine π fρ.arrRanges →
     (M.Fam fρ ps i ↔ M.Fam (fρ.mapLoc π) (ps.map (·.renameLoc π)) (i.locAct a π))) ∧
  (∀ π i, M.held (i.locAct a π) = (M.held i).renameLoc π) ∧
  (∀ π i i' ρ, M.Ext i i' ρ ↔ M.Ext (i.locAct a π) (i'.locAct a π) (ρ.mapLoc π)) ∧
  (∀ π ps i ps' i' t, M.Stop (ps, i) (ps', i') t ↔
     M.Stop (ps.map (·.renameLoc π), i.locAct a π) (ps'.map (·.renameLoc π), i'.locAct a π)
       (t.renameLoc π)) ∧
  (∀ π fρ ps i ρ ρf b A δ v, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (fρ.arrRanges ⊔ v.1.arrRanges) →
     (M.val b A i δ v ρ ↔ M.val b A (i.locAct a π) δ (v.renameLoc π) (ρ.mapLoc π))) ∧
  (∀ π fρ ps i ρ ρf C δ e, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (fρ.arrRanges ⊔ e.arrRanges) →
     (M.comp C i δ e ρ ↔ M.comp C (i.locAct a π) δ (e.renameLoc π) (ρ.mapLoc π))) ∧
  (∀ π fρ ps i ρ ρf T en n K Φ, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (fρ.arrRanges ⊔ K.arrRanges) →
     (M.share T en n i K Φ ρ ↔
       M.share (T.locAct a π) (en.locAct a π) n (i.locAct a π) (K.renameLoc π) (π • Φ)
         (ρ.mapLoc π)))

/-- **The binder at W, lifetimes**: instantiation along a re-stratification below a cut, of a
configuration that arises.  Every clause is forward. -/
def FreezeBinderLife (M : SemWorld) (a : StkAct M) : Prop :=
  (∀ c (θ : Restrat.Emb c) fρ ps i, M.Fam fρ ps i →
     M.Fam (θ.relRU fρ) (ps.map (·.restrat θ)) (i.lifeAct a θ)) ∧
  (∀ c (θ : Restrat.Emb c) i, M.held (i.lifeAct a θ) = (M.held i).restrat θ) ∧
  (∀ c (θ : Restrat.Emb c) i i' ρ, M.Ext i i' ρ → M.Ext (i.lifeAct a θ) (i'.lifeAct a θ) (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) ps i ps' i' t, M.Stop (ps, i) (ps', i') t →
     M.Stop (ps.map (·.restrat θ), i.lifeAct a θ) (ps'.map (·.restrat θ), i'.lifeAct a θ) t) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf b A δ v, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.val b A i δ v ρ → M.val b A (i.lifeAct a θ) (LSub.mapN θ.toNat δ) v (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf C δ e, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.comp C i δ e ρ → M.comp C (i.lifeAct a θ) (LSub.mapN θ.toNat δ) e (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf T en n K Φ, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.share T en n i K Φ ρ →
     M.share (T.imgLife a θ) (en.imgLife a θ) n (i.lifeAct a θ) K (θ ▹ Φ) (θ.relRU ρ))

/-- **The freeze binder at W.** -/
def FreezeBinder (M : SemWorld) (a : StkAct M) : Prop := FreezeBinderLoc M a ∧ FreezeBinderLife M a
```

Today:

- `BinderMachine` at `rs = []` is TwoRun's `steps_rename` (`TwoRun/Rename.lean:419`) over
  `StepsR`, which does not build; with `split` added to the array steps it is the port. At
  block-affine `π` it is OQ-43 (b), new. PROVED AT A RESTRICTION once ported (no array values).
- The location half at types with no `fam` reachable and configurations with no arrays is the
  restricted instance (`FreezeBinderNoArr`).
- **The lifetime half is OPEN pending an arising check**, because it carries a known risk:
  - Restrat's `not_vDenNatural` (`Restrat/Open.lean:30`) refutes naturality of
    `𝒱⟦Mut 'a (Imm 'b 1)⟧` at the paper layer, over all resources, not only those that arise; the
    direction that fails is the forward one, the one `FreezeBinderLife`'s `val` clause states
    (`𝒱⟦T⟧_δ(ℓ)(ρ₀)` holds, `𝒱⟦T⟧_{e∘δ}(ℓ)(e·ρ₀)` fails);
  - whether its witness arises was never checked;
  - Restrat's README names two repairs: not moving cells above the cut, or freeze then re-lend
    (D14.4). The re-lend repair ghost-ends every internal `mut` cell into an `own` cell before the
    move and builds the cell afresh at resume; it does **not** make `vC` natural. Under it, the
    `val`/`comp` clauses would be dropped and the lifetime half would rest on the frozen state
    alone (`Fam`, `held`, `Stop`, `share`). Which form the lifetime half takes is the binder
    track's open question.
- The first step of the binder's track is that arising check, as an elaborating `def` at `coreW`.

`FreezeBinder` is OPEN at every world, and is not a conjunct of done.

### I3. Drop finalises exactly once — notebook P5

**World:** I3.a is [W]; I3.b and I3.c are [prog].

**(a) Statement.** "The preservation conjunct for drop." Three parts, none a termination claim.

- **(I3.a)** The cancel conjunct of the share at W: a stop owing a continuation of an affine
  operation owes, at every future index, the cancel run of its frozen context to the cancel's end,
  at the table of a cancel run. That run ends in `M.Fam` with nothing owned left behind, so by
  `Arises` it ends in a configuration that arises, with the visible frames those at its entry
  (`StopVisible`), and every finaliser it passed has run (I3.b). Its **closing clause**,
  option-neutral: the cancel leaves nothing newly held, every frame and record held at its end
  having been held at its start. Under OQ-9 (b) nothing is ever held, and the clause is trivial.
- **(I3.a, the lends it holds: named-only)** "and ends every lend it holds" (the notebook's I3)
  needs the frames the continuation froze, as distinct from frames held at the same index by other
  suspended computations. That is the closing obligation's accounting, OQ-57. It is not available
  from an index alone: a resumed run keeps the frames it holds held (`StopVisible` forbids it to
  close a visible frame open at its entry), so the frames a continuation holds are not those held
  at its stop less those held at its last segment's entry. `CancelCloses` is named-only (§1.0's
  table, beside done) until OQ-57 gives the accounting. Its program-level form is in done:
  `CancelOrder` (I3.b) fires the lender's `[then]` finaliser during the cancel, and T1's `Final`
  and `ReleasedOnceAll` release the lender's memory exactly once.
- **(I3.b)** Over runs, a complete cancel of a continuation fires the finalisers of its frozen
  `[then]` frames once each, innermost first, and a complete unwind fires those it passes in the
  same order. Only complete runs are constrained, so whether a finaliser may stop at a resuming
  operation (OQ-7) stays open.
- **(I3.c)** No typed program can intercept a cancel (decision C4).

**(b) Definitions.** D4 `Kont.fins`, `cancelOf`; D9; `cancelTabW` (§1.3).

**(c) Lean.**

```lean
/-- **I3.a**: `contShare`'s cancel conjunct (`cancelOwed`, `Core/EffDefs.lean:138`) at W, at
affine entries, with the closing clause: the cancel's end holds nothing its start did not. -/
def ShareCancel (M : SemWorld) : Prop :=
  ∀ T en n i K Φ ρ, M.share T en n i K Φ ρ → en.q ≠ .lin → en.q ≠ .unr → ∀ i', M.Ext i i' ρ →
    ∀ N : List UInt32, n ∈ N → (∀ m ∈ K.hndNames, m ∈ N) →
      ewpW M i' (K.plug (raiseE (.val (cancelVal N none))))
        (cancelTabW T N (fun i'' => (∀ f ∈ (M.held i'').1, f ∈ (M.held i').1) ∧
                                    (∀ x ∈ (M.held i'').2, x ∈ (M.held i').2)))
        (fun _ _ _ => False) ρ

/-- **I3** at W. -/
def I3 (M : SemWorld) : Prop := ShareCancel M

def cancelAnswer : Option Val → Expr
  | none => .val .unit
  | some E => raiseE (.val E)

/-- A cancel run that fires the finalisers `fs`, innermost first: one `ufinC` per finaliser, its
`D ()` run under `cfin` to `cfret`/`cferr`, and at the end `ccatch` answering. -/
inductive CancelRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | caught {μ : Heap} {K : Kont} {Ns : List UInt32} {err : Option Val}
      (hK : K.Catches 0 = false) :
      CancelRun μ (ccatchE (K.plug (raiseE (.val (cancelVal Ns err))))) [] μ (cancelAnswer err)
  | fin {μ μ₁ μ₂ : Heap} {K₀ K : Kont} {Nv Dv : Val} {Ns : List UInt32} {err err' : Option Val}
      {fs : List Expr} {r : Expr} (hK : K.Catches 0 = false)
      (hD : Steps μ (cfinE (cancelVal Ns err) (.app (.val Dv) (.val .unit))) μ₁
              (raiseE (.val (cancelVal Ns err'))))
      (hr : CancelRun μ₁ (ccatchE (K₀.plug (raiseE (.val (cancelVal Ns err'))))) fs μ₂ r) :
      CancelRun μ
        (ccatchE (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (cancelVal Ns err)))))))
        (Dv.1 :: fs) μ₂ r

/-- An unwind that fires the finalisers `fs`, innermost first: one `ufin` per finaliser, its
`D (); raise p` run until a raise is pending under a context `Kd` that catches nothing of it,
ending at a raise that the remaining frames do not catch.  If `D` returns, `Kd` is the hole and
the raise is `p`.  If `D` raises its own abortive operation, the raise is that one, and `Kd` holds
the `seq` frame (`_; raise p`, which catches nothing) and `D`'s own frames at the raise; no rule
reduces a raise under a `seq`, so the unwind goes on from `K₀ ∘ Kd`, where the next `[then]`
frame of `K₀` catches it. -/
inductive UnwindRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | out {μ : Heap} {K : Kont} {m j : UInt32} {w : Val} (hK : K.Catches m = false) :
      UnwindRun μ (K.plug (raiseE (.val (opPayload m j w)))) [] μ
        (K.plug (raiseE (.val (opPayload m j w))))
  | fin {μ μ₁ μ₂ : Heap} {K₀ K Kd : Kont} {Nv Dv : Val} {n i m j : UInt32} {v w : Val}
      {fs : List Expr} {r : Expr} (hn : n ≠ 0) (hK : K.Catches n = false)
      (hD : Steps μ (.seq (.app (.val Dv) (.val .unit)) (raiseE (.val (opPayload n i v)))) μ₁
              (Kd.plug (raiseE (.val (opPayload m j w)))))
      (hKd : Kd.Catches m = false)
      (hr : UnwindRun μ₁ ((K₀.comp Kd).plug (raiseE (.val (opPayload m j w)))) fs μ₂ r) :
      UnwindRun μ (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (opPayload n i v))))))
        (Dv.1 :: fs) μ₂ r

/-- `K` has no `ccatch` and no `cfin` frame. -/
def Kont.NoCtl : Kont → Prop
  | .hole => True
  | .appR f K => (f ≠ .prim .ccatch ∧ ∀ s, f ≠ .app (.prim .cfin) s) ∧ K.NoCtl
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCtl

/-- **I3.b, cancel**: in a typed program, every complete run of a continuation's cancel fires the
frozen finalisers once each, innermost first.  (The three administrative steps from
`κ (inj₂ ())` to `cancelOf n H K` are pure; the canceller's context `K₀` takes no part until
`ccatch` answers.) -/
def CancelOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ : Kont) n H K, K.NoCtl →
    Steps Adequacy.emptyMem e μ₁ (K₀.plug (.app (kappa n H K) (.val (Val.inj₂ .unit)))) →
    ∀ μ₃ r, Steps μ₁ (cancelOf n H K) μ₃ r → (r = .val .unit ∨ ∃ E, r = raiseE (.val E)) →
      CancelRun μ₁ (cancelOf n H K) K.fins μ₃ r

/-- **I3.b, unwind**: every complete unwind through frames with no handler fires their
finalisers once each, innermost first. -/
def UnwindOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ K : Kont) n i v, K.hndNames = [] → K.NoCtl → n ≠ 0 →
    Steps Adequacy.emptyMem e μ₁ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) →
    ∀ μ₂ (K' : Kont) m j w, K'.Catches m = false →
      Steps μ₁ (K.plug (raiseE (.val (opPayload n i v)))) μ₂ (K'.plug (raiseE (.val (opPayload m j w)))) →
      UnwindRun μ₁ (K.plug (raiseE (.val (opPayload n i v)))) K.fins μ₂
        (K'.plug (raiseE (.val (opPayload m j w))))

def FinaliserOrder (J : TypingJ) : Prop := CancelOrder J ∧ UnwindOrder J

/-- **I3.c**: typed terms contain no `ccatch`, no `cfin`, and no handler named `0`. -/
def NoInterception (J : TypingJ) : Prop :=
  ∀ Θ Δ Γ e j, J Θ Δ Γ e j → ¬ e.HasPrim .ccatch ∧ ¬ e.HasPrim .cfin ∧ e.HndNamesNZ
```

`Expr.HasPrim p e` says `.prim p` occurs in `e`; `Expr.HndNamesNZ e` says every occurrence of
`.prim .hnd` is the function of `.app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) _)` with
`m ≠ 0`. Both are syntactic, by structural recursion.

**`UnwindRun` checked on two frames whose inner finaliser raises.** Take
`ubind (N₁, D₁) (ubind (N₂, D₂) (raise p))`, `D₂ = λ_. raise p′` (a typed finaliser may raise an
abortive operation, `effThen`'s `hD`) and `D₁ = λ_. ()`. The machine runs `ufin` at the inner
frame, then `D₂ ()` to `(raise p′; raise p)`, which is a raise under a `seq` frame and is not
reduced there, then `ufin` at the outer frame on `p′`, then `D₁ (); raise p′` to `raise p′`. The
revised `fin` derives this run with `Kd = (_; raise p)` at the first step and `Kd = hole` at the
second, firing `[D₂, D₁]`, which is `Kont.fins` of the two frames, innermost first. A rule whose
`hD` ends at a bare raise derives no run here: `(raise p′; raise p)` has no step. Without an outer
frame, the run stops at `(raise p′; raise p)`, and `fin` then `out` at `K = (_; raise p)` derive
it. `Kd` is asked only `Kd.Catches m = false`, which already excludes a `[then]` frame and a handler of
`m`. It may hold handler frames of other names: a typed finaliser may install a handler and raise
through it (`effThen`'s `hD` types `D` at `F_{S.abortOnly} 1`, and `[handle]` forwards the raise),
so asking `Kd` for no handler frame would leave such runs out and make `UnwindOrder` false of
them. This was checked in Lean against Core's machine, in a scratch file outside the library
(`UnwindRun`, `Kont.fins` and both runs as above: `two_frame` derives the `UnwindRun`,
`two_frame_steps` is the machine run, axioms `[propext, Classical.choice, Quot.sound]`); the
builder re-proves it in `Targets/Restricted` as the first instance of `UnwindOrder`.

Under OQ-7 (b), today's kernel, a frozen context never holds a `cfin` frame: a finaliser performs abortive operations
only (`effThen`'s `hD`), so no continuation is captured inside a cancel. Under OQ-7 (a) it can be
(OQ-41), and the order statement for such a context is OQ-41's.

A finaliser's observable effects are on memory and through the errors it raises; T1's `Final`
and `SafeRuns` cover the first, and `CancelRun`/`UnwindRun`'s raise states the second.

**(d) Literature.**

- Voigt–Schuster–Brachthäuser, OOPSLA 2025, Thm 3.6 (Resource Safety): "If ActiveOpen(M) and
  InactiveClosed(M) and M → M′, then ActiveOpen(M′) and InactiveClosed(M′)". Its caveat: "These
  invariants are not statically checked, but rather represent a set of best practices". Ours are
  typed, and stated as preservation (I3.a) as theirs is.
- Ahman–Bauer Thm 7 (Finalisation): "A well-typed run factors through finalisation".
- Affect's future work: "a linear (instead of affine) version of Affect with a 'discontinue'
  operation for unused continuations". Our core is that version.
- The survey's A6 states it for a linear core: "Every continuation that captures a must-use value
  is resumed or explicitly discontinued exactly once, and every owned value is dropped exactly
  once". I3 and D9 take its second half (resources); its first half, the continuation's use, is
  P8.b, deferred to OQ-50 (§6, §7).

**(e) Existing Lean, and what to prove now.**

- `ShareCancel coreW`: `contShare`'s cancel conjunct is `cancelOwed`, through `cancelTabW_core`;
  the closing clause holds because nothing is held at `coreW`. Recorded **PROVED AT A
  RESTRICTION** (nothing held: σ = []), not PROVED: the clause's content is vacuous there.
- `CancelCloses` at the end state: named-only, OPEN under OQ-57.
- At affine resuming rows, GhostEnd's `withborR_compat` (`Drop.lean:108`: 6.65 unwinding with
  affine resumption) and `spans_two_affine_yields` (`:318`, the cancel path) are σ=[] instances of
  `SpanBorrows` at `.any`.
- Also relevant: `ewp_kappa_cancel`, `ewp_ccatch`, `ewp_frame_then` (`Core/EffRules.lean:369`,
  finalisers at a cancel), `cancel_then`, `cancel_frame`.
- Both cancel outcomes are machine-checked: `prog_run` and `prog₃_run`
  (`Core/EffCancel.lean:103,113`).
- To prove now:
  - `NoInterception tier1`, by induction on `CDerives` (no constant contains `ccatch`/`cfin`;
    `effHandle` asks `n ≠ 0`). PROVED-able.
  - `FinaliserOrder tier1`: machine lemmas, by induction on `K`'s catching frames with
    determinism (`AStep1.deterministic`); the two-frame run above is its first instance. Second
    wave.

**(f) Non-vacuity.**

- `takeProg n` (`take n` cancels a producer holding a cell, and the producer's finaliser frees it),
  `storeCancel` and `at12` reach the cancel application.
- `failOutside` and `reborrowRaise` reach an unwind through finaliser frames.
- `RowClass.any` is met by an affine `yield`.

**(g)** In the first pass.

### I4. Answering effects are borrows — notebook P6

**World:** I4.a and I4.b are [prog] (typing); I4.c is binary.

**(a) Statement.** An answering (tail-resumptive) effect lends its state to the body as a
capability, `Mut 'h S` at a fresh lifetime `'h`, for the body's extent. Performing an operation is
a `withswap` call on the borrowed capability. So these properties of answering effects are the
borrow calculus's own:

- their safety (6.151);
- their extent (6.60);
- their exclusivity: a `Mut` borrow has no copy rule.

It has four parts:

- **(I4.a)** The borrow form of every typed answering body is typed by the borrow rules, at the
  rows it may span.
- **(I4.b)** The survey's A5 rules (a)–(c) hold, stated as the rejections AT05 and AT06 (§8).
- **(I4.c, typing)** Where the control form (a `hnd` with answering clauses, state passed at each
  resume, decision 59) is typed, its borrow form is typed at the same answer. Unary: no binary
  relation.
- **(I4.c, equivalence)** The two forms are contextually equivalent. Binary.

**(b) Definitions.** D13 (`AnsImpl`, `ansCall`, `ansRun`, `ctlForm`, `capPass`).

**(c) Lean.**

```lean
def ImplTyped (J : TypingJ) (impl : AnsImpl) : Prop :=
  List.Forall₂ (fun (ab : VTy × VTy) c => J.at LifeCtx.empty [] (.val c)
    (.val (.bang (.thunk (.arr (.tensor impl.S ab.1) (.ret (.tensor impl.S ab.2))))))) impl.E impl.co

/-- **I4.a.** -/
def I4a (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (impl : AnsImpl) (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (S : Row) (d s₀ body : Expr) (B : VTy),
    ImplTyped J impl → Ctx.DeadP Γ → Δ.find? x = none →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →        -- §Corrections C4
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) →                 -- §Corrections C4
    ¬ VFree x impl.S → ¬ VFree x B →
    (∃ b, Δ.Defines b ∧ J.out.le Δ b impl.S) → RowSpan Adm Δ x S → c.Admits S →
    closedAt 0 d = true →
    J.at Δ Γ s₀ (.val impl.S) → J.at Δ Γ d (.val (.lolli (.ref impl.S) .unit)) →
    J.at (Δ.extend x Δ.meetOfDom) (⟨.mut (.var x) impl.S, true⟩ :: Γ) body
      (.comp (CTy.effOf S (.box (.var x) B))) →
    J.at Δ Γ (ansRun d s₀ body) (.comp (CTy.effOf S (.tensor impl.S B)))

/-- **I4.c, typing half**: a typed control form of a closed body on the spine has a typed borrow
form, at the same answer, its row one a lend may span.  `R` is data, so the callback's answer
`['x] R` is the borrow rules'. -/
def I4Typing (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (impl : AnsImpl) (n : UInt32) (d s₀ e body : Expr) (S : Row) (R : VTy) (x : LifeVar),
    capPass n impl.co 0 (e.shift 1 0) = some body → R.Data → ImplTyped J impl →
    ¬ VFree x impl.S → (∃ b, LifeCtx.empty.Defines b ∧ J.out.le LifeCtx.empty b impl.S) →
    RowSpan Adm LifeCtx.empty x S → c.Admits S → closedAt 0 d = true →
    J.closed (ctlForm n impl s₀ e) (CTy.effOf S (.tensor impl.S R)) →
    J.at LifeCtx.empty [] d (.val (.lolli (.ref impl.S) .unit)) →
    J.closed (ansRun d s₀ body) (CTy.effOf S (.tensor impl.S R))

/-- **I4.c, equivalence** (binary): the control form and the borrow form are contextually
equivalent. -/
def I4c (J : TypingJ) : Prop :=
  ∀ P, P.Respects → ∀ (impl : AnsImpl) (n : UInt32) (d s₀ e body : Expr) (S : Row) (R : VTy),
    capPass n impl.co 0 (e.shift 1 0) = some body →
    J.closed (ctlForm n impl s₀ e) (CTy.effOf S (.tensor impl.S R)) →
    J.closed (ansRun d s₀ body) (CTy.effOf S (.tensor impl.S R)) →
    CtxEquiv J P (CTy.effOf S (.tensor impl.S R)) (thunkF (ctlForm n impl s₀ e))
      (thunkF (ansRun d s₀ body))
```

Both forms answer `S ⊗ R`: the control form's answer clause pairs the final state with the
result, and the borrow form frees the cell and returns its content beside the result.

**(d) Literature.**

- HandlersAsBorrows (ours, PAPER): "`handle` becomes `withbor` form (2), lending the handler's
  state as `Mut 'x S`; … an operation becomes `withswap` on the borrowed state", and "Effect
  safety therefore becomes no use of a borrow after its lifetime".
- System C §4.4: "Effect safety means that applications of a capability with label l only occur
  in a context that contains a delimiter at l".
- The survey's A5 synthesis: "handle lends cap: &'h mut H … cap.op(args) reborrows cap for the
  call … Rules (a) and (b) are then the ordinary reborrow rules for a call whose return happens to
  be delayed".

**(e) Existing Lean, and what to prove now.**

- [PAPER] `translate_typed`, `effect_safety`, `handle_is_shift`, `twoBlocks_refused`
  (`experiments/HandlersAsBorrows`).
- The surface elaborates answering effects to exactly this form (`Core/Handlers.lean`, SPEC §18):
  run facts only.
- `I4a tier1 admClosedOp .abortive` is a derived rule from `withbor2U`, `alloc`, `free` and
  `withswap`. PROVED AT A RESTRICTION once written.
- `I4a` at `.resumeOnce` needs tier 2: a capability held across another effect's resuming
  operation is a spanning lend. OPEN.
- `I4Typing tier1 admClosedOp .abortive`: by inversion of the control form's derivation down the
  spine (`[handle]`, `[let]`, `[perform]` at `n`), each `perform` re-typed as `ansCall` on the
  threaded `Mut 'x S` by `withswap`; the inversion lemmas are D21's cost. OPEN, beside done.
- `I4c` is OQ-1. Binary, out.

**(f) Non-vacuity.** `logInBorrow` (`Core/EffPrograms.lean:578`) and the corpus answering
handlers (`effects-*`) are instances of I4.a. For `I4Typing`, a body `let b = perform (n, 0) () in
b` at `E = [(1, 1)]` has `capPass = some (let (m′, b) = ansCall co (m, ()) in forget m′; b)`.

**(g)** I4.a is in the first pass. In the first pass, "answering effects are borrows" rests on
I4.a and on elaboration: the surface elaborates answering effects to the borrow form
(`Core/Handlers.lean`, SPEC §18), so the kernel's answering effects are borrows by construction.
What relates a `hnd` with answering clauses to the borrow form is `I4Typing` (unary) and `I4c`
(binary), both beside done: `I4Typing`'s proof needs inversion lemmas (D21's cost), and I4.c is
binary. I4.b is stated and outside the first pass: its rejections need inversion lemmas too, and
each is proved only when a track needs it. Whether answering effects become rows with a
reborrow-holding clause is OQ-1's design question, not decided here.

### I5. The capture laws β, η, hiding — notebook P7

**World:** [W].

**(a) Statement.** These are the unary halves FL uses.

- **(β)** Resuming a continuation at `w` runs the frozen computation at `w` under the reinstalled
  handler.
- **(hiding)** [TR] 6.66 at W, at every protocol table: a computation that unfolds a `Mut` cell
  to its owned content runs with the content, and at each stop it re-establishes the cell's
  invariant and gives the content back for the view; the continuation is owed the view, and
  unfolds it again when resumed. So the code that receives control at a stop observes the cell
  only through its invariant.
- **(frame)** A frame (the rest of a `let`) is carried through every stop and resume of an
  effectful computation, and is left behind holding nothing owned at a cancel or an abort.

η and the binary forms are in T2.

**(b) Definitions.** D4, §1.3.

**(c) Lean.**

```lean
/-- **I5.β.** -/
def I5beta (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) (n : UInt32) (H : Val) (K : Kont) (w : Val) i Q ρ,
    TableI.Mono Tb → ewpW M i (hndE H (K.plug (.val w))) Tb Q ρ →
    ewpW M i (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)) Tb Q ρ

/-- The view `ℓ ↦ M_α 𝒱⟦T⟧δ` at W. -/
def mutView (M : SemWorld) (ℓ : Loc) (α : Life) (T : VTy) (δ : LSub) (i : Idx M.Stk) : WProp :=
  ptoMutSW M ℓ α i (fun i₀ => M.val true T i₀ δ)

/-- One unfolding of the anti-framed computation (GhostEnd's `antiF`, `Frames.lean:59`, at W):
from the content handed out, run to an answer or a stop, handing the content back for the view;
a stop owes the view and the computation again. -/
def antiFW (M : SemWorld) (Tb : TableI (Idx M.Stk)) (ℓ : Loc) (α : Life) (T : VTy) (δ : LSub)
    (Q : Idx M.Stk → Val → WProp) (X : Idx M.Stk → Expr → WProp) :
    Idx M.Stk → Expr → WProp := fun i e =>
  all fun v => ptoOwn ℓ v ─⋆ (M.val true T i δ v ─⋆
    wpGW M i e (fun i'' t => ex fun w => ptoOwn ℓ w ⋆ M.val true T i'' δ w ⋆
      (mutView M ℓ α T δ i'' ─⋆ fun ρ => valPostI Q i'' t ρ ∨
        Tb i'' t (fun i' e' => mutView M ℓ α T δ i' ⋆ X i' e') ρ)))

/-- The anti-framed computation: the least fixed point of `antiFW`. -/
def AntiRelendW (M : SemWorld) (Tb : TableI (Idx M.Stk)) (ℓ : Loc) (α : Life) (T : VTy)
    (δ : LSub) (Q : Idx M.Stk → Val → WProp) (i : Idx M.Stk) (e : Expr) : WProp :=
  fun ρ => ∀ X : Idx M.Stk → Expr → WProp,
    (∀ i e ρ, antiFW M Tb ℓ α T δ Q X i e ρ → X i e ρ) → X i e ρ

/-- **I5.hiding**: [TR] 6.66 at W (`ewpTS_M_antiFrameR`, `GhostEnd/Frames.lean:89`, at W), the
view at a lifetime `α`, as there. -/
def AntiFrameW (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) ℓ α T δ Q i e, TableI.Mono Tb →
    Entails (mutView M ℓ α T δ i ⋆ AntiRelendW M Tb ℓ α T δ Q i e) (ewpW M i e Tb Q)

/-- **I5.frame**: `ewp_frame_plain` (`Core/EffRules.lean:193`) at W, at tables with no `unr`
entry.  Its stability premise is `hFs` transcribed: Stop-related indices whose visible records
agree give `Fr i ⊨ Fr i'`.  `hU` (an `unr` entry's frame is empty) is vacuous at such tables. -/
def FrameW (M : SemWorld) : Prop :=
  ∀ (T : OpTabI (Idx M.Stk)) (K : Kont), (∀ n, K.HasHnd n = false) → (∀ n, K.Catches n = false) →
    K.hndNames = [] → (∀ n j en, T n j = some en → en.q ≠ .unr) →
    ∀ (Fr : Idx M.Stk → WProp),
    (∀ ps i ps' i' t, M.Stop (ps, i) (ps', i') t → (∀ x, x ∈ i'.1 ↔ x ∈ i.1) →
       Entails (Fr i) (Fr i')) →
    (∀ i i' ρ, M.Ext i i' ρ → Fr i ρ → Fr i' ρ) →
    (∀ n j en, T n j = some en → (en.q ≠ .lin ∨ en.abort = true) → ∀ i ρ, Fr i ρ → NoOwn ρ) →
    ∀ (Q₁ Q : Idx M.Stk → Val → WProp),
      (∀ i v, Entails (Q₁ i v ⋆ Fr i) (ewpW M i (K.plug (.val v)) (opTabW M T) Q)) →
      ∀ i e ρ, ewpW M i e (opTabW M T) Q₁ ρ → ∀ ρ₂ ρ', Fr i ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpW M i (K.plug e) (opTabW M T) Q ρ'

def I5 (M : SemWorld) : Prop := I5beta M ∧ AntiFrameW M ∧ FrameW M
```

At `coreW`, `Stop` is R-T1, so a Stop-related pair with agreeing records is any pair of lists
with the same members (take `ps = ps' = []`), and `FrameW`'s premise is `hFs` exactly. If a W
needs the premise only at stops whose end arises, that weakening is named separately
(`FrameWArising`) and justified when it is needed; it is not the transcription.

**(d) Literature.**

- Plotkin–Pretnar (T2 above): handling is "the unique homomorphism". β at a captured operation is
  the homomorphism equation at `op`.
- [TR] 6.66 (p. 25), checked against the PDF: "ℓ ↦ Mut α P̂ ⋆ (∀ v. ℓ ↦ v –⋆ P̂ (v) –⋆ wp (e) {∃ v.
  ℓ ↦ v ⋆ P̂ (v) ⋆ (ℓ ↦ Mut α P̂ –⋆ Q̂)}) ⊧ wp (e) {Q̂}". `AntiFrameW` is this rule with `wp`'s run
  allowed to stop: at each stop the postcondition's fold is applied, and at each resumption the
  precondition's unfold. It is `[variant: P̂ ≔ 𝒱⟦T⟧δ]`, as `wpG_M_antiFrameX` is.
- "Hiding is the relational content of 6.66" (the notebook); its binary form is T2's `Hiding`.

**(e) Existing Lean, and what to prove now.**

- `ewp_kappa_resume` (`Core/EffRules.lean:493`) is `I5beta coreW`. Since `wpGW`'s shape is fixed,
  `I5beta M` is provable for every `M` from a generic `ewpW_step`. PROVED (generic) once written.
- `ewpTS_M_antiFrameR` (`GhostEnd/Frames.lean:89`) is `AntiFrameW coreW`, at every table, through
  the transports (`ptoMutSW_core`): the GhostEnd experiment proves it at Core's `ewpTS`. PROVED AT
  σ=[] once the transport is written.
- `FrameW coreW` is `ewp_frame_plain` through the transports: its premise at `coreW` is `hFs`, and
  `hU` is vacuous at tables with no `unr` entry. To be proved before it is recorded; recorded
  PROVED AT σ=[] then.
- EffModelRel has β, η and hiding as equations [SIB].

`AntiFrameW` and `FrameW` at the end state are OPEN: the first is 6.66 at W's `wpGW`, and the
second asks the frame to be stable across the stops W's runs reach, which is where spanning lends
bite.

**(f) Non-vacuity.** `[let]` around a performing computation (`let_compatC`) and every handler
resumption use β and the frame; `withswap_compatX` and `withbor3U_compatX` use 6.66.

**(g)** The unary halves are in the first pass. η and the binary forms are out (T2).

---

## 6. The other properties

### P1 — see T1. P12 — see T3. P13 — see T4.

### P2. Effect safety (with T0)

**World:** [prog]. T0 is about the row form and its link to the typing rules.

**(a) Statement.** A program typed at `F_Σ A`, `Σ` unr-free, only ever stops at a value or at an
operation of `Σ`, of the right kind, and is never stuck elsewhere. At `Σ = []` it never stops at
an operation: no unhandled operation, no undelimited capability. (A closed program can be typed
at a row with a resuming `unr` operation, by `[raise]` or by unrolling a loop; W is unconstrained
there, and such programs are covered at tier 1.)

**T0.** The row form the typing rules use, with row variables, is an effect algebra in Yoshioka et
al.'s sense (Def. 3.5) and meets their safety conditions (Def. 5.1):

- subeffecting cannot hide a performed operation;
- handling one name never erases another's operations.

T0 is stated at the end state's row form `RF`, a parameter (OQ-13's remaining question), together
with `RowLink RF` (D2): the algebra's operations are the closed-row operations `[sub]`, `[handle]`
and row instantiation use. Without the link, T0 would be true or false of an algebra no typing
rule reads. `EffSafe` itself is proved semantically (FL and `AdequateEvery`), not from T0; T0 is
the check that the representation has no subeffecting or handling that could lose an operation.

**(b) Definitions.** D1, D2 (`RowForm`, `RowLink`, `orowRF`), D7.

**(c) Lean.**

```lean
/-- **P2**, at unr-free rows (a row with a resuming `unr` operation is covered at tier 1, by
Core's adequacy). -/
def EffSafe (J : TypingJ) : Prop :=
  ∀ e (S : Row) A, S.NU → J.closed e (CTy.effOf S A) → ∀ μ' e', Steps Adequacy.emptyMem e μ' e' →
    IsVal e' ∨ (∃ μ'' e'', Step1 μ' e' μ'' e'') ∨ StopsIn S e'

/-- Yoshioka–Sekiyama–Igarashi Def. 5.1. -/
structure EffAlg.Safe (EA : EffAlg) : Prop where
  c1 : ∀ L, ¬ EA.Sub (EA.lift L) EA.unit
  c2 : ∀ L L' ε ε' x, EA.Sub (EA.lift L) ε → EA.comp (EA.lift L') ε' = some x → EA.eqv x ε →
         L ≠ L' → EA.Sub (EA.lift L) ε'

/-- **T0**: the row form's algebra is an effect algebra (Def. 3.5) that meets the safety
conditions (Def. 5.1), at every effect context.  In `EndStateAt` beside `RowLink RF`. -/
def RowAlgSafe (RF : RowForm) : Prop := ∀ Ξ : EffCtx, (RF.alg Ξ).Laws ∧ (RF.alg Ξ).Safe
```

Def. 7.1 (needed only with `lift`/masking) and Def. 7.6 (needed only if dispatch ignores effect
type arguments) do not apply: there is no masking, and our dispatch is by `(n, i)`, with no type
arguments. They become targets if either is added.

**(d) Literature.** Yoshioka–Sekiyama–Igarashi, ICFP 2024 (arXiv 2404.16381), checked against the
PDF:

- Def. 3.5: "Typelike substitution respecting well-formedness is a homomorphism for ⊙, (−)↑, and
  ∼, that is, … (ε1 ⊙ ε2)[S/α] = ε1[S/α] ⊙ ε2[S/α]; … (L)↑[S/α] = (L[S/α])↑; and … ε1 ∼ ε2 =⇒
  ε1[S/α] ∼ ε2[S/α]", and "∼ is an equivalence relation on Eff(Σ) and preserves well-formedness";
  ⟨Eff(Σ), ⊙, 0⟩ "is a partial monoid under ∼".
- Def. 5.1: "(1) For any L, (L)↑ < 0 does not hold. (2) If (L)↑ < ε and (L′)↑ ⊙ ε′ ∼ ε and L ≠
  L′, then (L)↑ < ε′."
- Lemma 5.4: "If ∅ ⊢ e : A | ε and e −→∗ e′ ↛, then … e′ = v … or e′ = E[op_l S T v] … such that
  0−free(l S, E)".
- Thm 5.8: "If ∅ ⊢ e : A | 0 and e −→∗ e′ ↛, then e′ = v for some v."
- System C, Def 8 / Cor 9: "Starting from an empty context reducing a well-typed program ∅ ⊢ s : τ
  | ∅ never results in an undelimited label."
- Tang et al., POPL 2024, Thm 3.2: "If ⊢ M : A ! E, then either there exists N such that M ⤳ N or
  M is in a normal form with respect to E", the normal form being "E[(do ℓ V)^E] for ℓ ∈ E and ℓ
  ∉ bl(E)".

**(e) Existing Lean, and what to prove now.** At `Σ = []`, `adequacyD` with `ewp_bot`
(`Core/EffWp.lean:772`) [Core σ=[]]; it has no name. For `EffSafe tier1` at every row, two new
pieces are needed, both first-wave:

- `wpG_demonic`: `wpTS_demonic`'s replay argument at `wpG` (also `AdequateEvery coreW`);
- `stop_irreducible` (D7).

`(closedRowAlg Ξ).Laws ∧ (closedRowAlg Ξ).Safe` is PROVED-able now: the laws by list and
lookup lemmas (the substitution clauses are vacuous at `Var := Empty`); safety (1) by lookup at
`(n, 0)`, (2) taking the witness `ε′`, since `(n)↑` only has the name `n`. PROVED AT A
RESTRICTION (closed rows). `RowAlgSafe orowRF` adds the substitution lemmas on `ORow` (append,
and `RowEq` under append), and `RowLink orowRF` the reading's lemmas (D2); first wave. At the end
state, `RowAlgSafe RF ∧ RowLink RF` is at the row form OQ-13 settles; `orowRF` is the restricted
instance.

**(f) Non-vacuity.**

- `raiseU : F_{Fail} B` (`Core/EffPrograms.lean`) is closed and stops at once.
- `logOutside` is typed at `F_∅`.
- Every program's effect context has non-empty signatures at the names it uses.

**(g)** In the first pass.

### P8. Continuation linearity

**World:** [prog].

**(a) Statement.** A continuation is used as its qualifier says:

- a linear one is resumed exactly once;
- an affine one is resumed or cancelled exactly once.

A `lin` or `aff` continuation is never dropped silently: `kTy` at `lin`/`aff` is a thunk, and no
`forget` constant has a thunk type. An `unr` continuation can be forgotten (`forgetBang`), but it
holds no resource (`contShare`'s `unr` conjunct), and the end state's typing pin has no resuming
`unr` operation (§0). There are two halves:

- **(P8.a, the resource half, OQ-50 (c))**: on every complete run, every cell a captured
  continuation holds is released exactly once. This is **not a separate property**: it is T1's
  `ReleasedOnceAll` (D9) read at the runs that capture a continuation, and `Final`'s empty memory
  at their end. `Status.lean` records it as a corollary of T1.
- **(P8.b, the use count)**: each continuation a step creates (`hop`) is used (applied to
  `inj₁ ()` or `inj₂ ()`) as its qualifier says. This is the continuation-linearity property
  proper, and it is beside done.

**(b) Definitions.** D4, D6, D9.

**(c) Lean.** P8.a has no definition of its own (above). **P8.b is not stated in Lean here.** The machine does not observe a continuation's use: `κ` is a
λ-value, and two copies of it are indistinguishable from one. Stating P8.b needs that
observation, and how to make it is OQ-50, the user's choice:

- OQ-50 (a), with Tang et al.'s Thm 3.6 shape: an instrumented machine in which each `hop` step
  tags the `κ` it creates and each use step consumes the tag, every step conserving tags,
  `ℒ(M) ∪ S = ℒ(N) ∪ T`; P8.b is that a linear tag is consumed exactly once, by a resume, and an
  affine tag at most once, on every terminating run; its proof is syntactic subject reduction;
- OQ-50 (b), the TR's one-shot-cell machine: `κ` is a heap cell freed by its use, and P8.b is D9
  at that cell.

Until OQ-50 is answered, `ContUse` is a placeholder name, not a target.

**(d) Literature.**

- Tang et al., Thm 3.6 (Reduction Safety): "For any closed, well-typed and linear safe
  computation M in F◦eff, if M ⤳^S_T N, then N is linear safe and ℒ(M) ∪ S = ℒ(N) ∪ T."
- Tang et al., Thm 3.4.3: "Deep handlers are unlimited". Ours are: clauses are `!U(…)`.
- Affect: "A call to an already resumed one-shot continuation is a stuck expression".

**(e) Existing Lean.** At [Core σ=[]]: the qualifiers, `contShare`, `KapRel`, and the
`[let]`/`[then]` premises (`S.Weak → Γ₂.Drops`, `S.Unr → Persistent Γ₂`). P8.a holds wherever
`ReleasedOnceAll` does (second wave at tier 1). P8.b is not stated (OQ-50).

**(f) Non-vacuity.** `prog` (linear, resumed once) and `progC` (affine, cancelled) in
`Core/EffExamples.lean`.

**(g)** P8.a is in the first pass as part of T1. P8.b waits on OQ-50, beside done.

### P9. Lifetime soundness

**World:** [W].

**(a) Statement.** A value of a type that outlives `@a` holds only resources that outlive `@aδ`,
at every type of the calculus, suspension types included, at every index (6.60 at W). So:

- no capability is used outside its handler's extent;
- no continuation is resumed after a lifetime it holds a loan from has ended.

P9 and P10 are stated at W, as BoLo states them: 6.60, and validity. At the program level T1
covers only their use-after-free consequence. In this machine a use through a borrow after its
lend ends, and before the owner frees the cell, is not stuck (the machine sees locations, not
lifetimes), so lifetime soundness and exclusivity have no program-level form here, and survey
A4 (b) is stated at W only. P2 covers an operation performed past its handler (it is
unhandled).

**(b) Definitions.** The outlives judgments are the typing system's own, `J.out : OutJ` (§1.2),
and every rule transcription reads them, so `LifetimeSound M J.out` certifies exactly the outlives
rules `J` uses. `OutExtends J.out` (a conjunct of `Guarantees`) says they extend Core's
`VOutlives`/`VOutlivesLe` (`Core/Types.lean:1755,1761`), which have no rule at `U C`; whether tier
2 adds one, or a `[gen]` rule, is OQ-28. At `J.out = OutJ.core`, P9 says nothing at a thunk type,
and then no rule of `J` relies on an outlives fact at a thunk type either.

**(c) Lean.**

```lean
/-- **P9**: 6.60 at W, at both of the typing system's outlives judgments, both modes, every
index. -/
def LifetimeSound (M : SemWorld) (O : OutJ) : Prop :=
  (∀ Δ δ a α T b i v ρ, Δ.Models δ → a.interp δ = some α → O.lt Δ a T →
     M.val b T i δ v ρ → BoLo.Outlives ρ α) ∧
  (∀ Δ δ a α T b i v ρ, Δ.Models δ → a.interp δ = some α → O.le Δ a T →
     M.val b T i δ v ρ → OutlivesLe ρ α)
```

The expressive half, that a stored suspension can be typed with a bound, is AT07 and AT08 (§8).

**(d) Literature.**

- [TR] 6.60 (p. 21): "If ∆ ⊢ T ⊐ @a and δ ∈ ⟦∆⟧, and ρ ∈ 𝒱⟦T⟧δ then @ρ ⊐ @aδ".
- The survey's A4: "(a) no handler capability is invoked outside its handler's extent; (b) no
  continuation is resumed after a lifetime it holds a loan from has ended".

**(e) Existing Lean.**

- `vC_outlives` and `vC_outlivesLe` (`Core/RelationFacts.lean:479,575`), both modes, are
  `LifetimeSound coreW OutJ.core`. PROVED AT σ=[].
- `Row.Unwind.out` and `ewp_box_end` place operation arguments in the frame's stratum.

At an extended judgment and at the end state: OPEN.

**(f) Non-vacuity.** `VOutlives` derives at every data type and at `Imm`/`Mut` with a longer
lifetime.

**(g)** In the first pass.

### P10. Exclusivity across the handler

**World:** [W].

**(a) Statement.** Every configuration W reaches satisfies the aliasing invariant, counting the
loans held by suspended frames (`held`), by running clauses and by values in transit, all parts of
the full resource `fρ`.

**(b) Definitions.** D10.

**(c) Lean.**

```lean
/-- **P10.**  A consequence of `Arises` by `TW.valid` and `TW.inv` (`exclusive_of_arises`). -/
def Exclusive (M : SemWorld) : Prop :=
  ∀ fρ ps i, M.Fam fρ ps i → ResU.Valid fρ ∧
    ∃ ps₀ ls₀, (∀ p, p ∈ ps₀ ↔ p ∈ ps ∨ p ∈ (M.held i).1) ∧
      (∀ x, x ∈ ls₀ ↔ x ∈ i.1 ∨ x ∈ (M.held i).2) ∧ TI fρ ps₀ (rsOf ls₀)
```

It counts the same frames and records as `Arises`. `Tagged` is not repeated: it is a conjunct
of `Arises`, and `TI` is what `TW.inv` gives of the `TW` world `Arises` names.

The program-level rules this invariant enforces are the A5 rules (a)–(c): AT05, AT06 (§8).

**(d) Literature.**

- [CONF] 415:21: "Conceptually, in a valid resource, every pair of aliases map to the same object
  and each has an immutable ancestor."
- The survey's T5 (synthesis): "(i) exclusivity counting suspended and in-transit loans".

**(e) Existing Lean.** `TW.valid` and `TW.inv` give `Exclusive coreW`. PROVED. WorldW's
`entryRecorded_mut` is evidence at the probe world. At the end state: OPEN, by way of `Arises`.

**(f) Non-vacuity.** Every `TW` world.

**(g)** In the first pass.

### P11. Handler correctness

**World:** [W].

**(a) Statement.** A handler means what its clauses say. These unary parts are in the pass:

- the `[handle]` rule is sound at W: the handler is a model of its signature, and handling is the
  induced map (initiality's existence half);
- reduction is semantic identity, unary: return, operation and unwind are head steps, and `ewpW`
  neither gains nor loses programs along a pure head step.

**(b) Definitions.** D3.

**(c) Lean.**

```lean
/-- `handle_compatC` (`Core/EffRules.lean:1092`) at W, at unr-free rows. -/
def HandleCompat (M : SemWorld) : Prop :=
  ∀ Δ Γ Γ₁ Γ₂ Γr Γc e S (E : List (Qual × VTy × VTy)) (n : UInt32) A R ir ic,
    (Row.ofEff n E 0 ++ S).NU →
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.SplitP Γ₁ Γr Γc → Ctx.SoloP Γr ir (retTy S A R) →
    Ctx.SoloP Γc ic (clausesTy S R E) → n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    SemW₀ M Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A)) →
    SemW₀ M Δ Γ (hndTerm n ir ic e) (.comp (CTy.effOf S R))

/-- Reduction is semantic identity (unary): a pure, non-allocating head step neither adds nor
removes programs from `ewpW` at a protocol table (whose stops are irreducible, D7). -/
def RedLaws (M : SemWorld) : Prop :=
  ∀ (K : Kont) a a' i (T : OpTabI (Idx M.Stk)) Q ρ, (∀ μ, Head μ a μ a') → a.allocs = false →
    (ewpW M i (K.plug a) (opTabW M T) Q ρ ↔ ewpW M i (K.plug a') (opTabW M T) Q ρ)

def P11 (M : SemWorld) : Prop := HandleCompat M ∧ RedLaws M
```

`HandleCompat M` is FL's `[handle]` case at unr-free rows, so `FL M J ∧ Tier1SubNU J` gives it; it
is named for the register.

**(d) Literature.**

- Plotkin–Pretnar Def. 4.2: "A model M of the effect theory T is a set |M| … together with an
  operation op_M : ⟦α⟧ × |M|^⟦β⟧ → |M| for each operation symbol".
- Prop. 4.3: "The functor U : Mod_T → Set has a left adjoint F", the free model.
- Def. 4.5 (correct handlers), quoted at T2.

**(e) Existing Lean.**

- `handle_compatC` is `HandleCompat coreW`. PROVED AT σ=[].
- `ewp_step` and `wpG_head` give `RedLaws`' backward direction.
- The forward direction is determinism (`AStep1.deterministic`, `Core/Demonic.lean:117`) with the
  replay. PROVED-able generically, given `ShareMono`.

At the end state: OPEN.

**(f) Non-vacuity.** Every handled program in `Core/EffPrograms.lean`.

**(g)** The unary parts are in the first pass. The equational laws are T2 (out).

### P14. Well-bracketing conservativity

**World:** P14.a is [Core σ=[]]; P14.b relates [Core σ=[]] to [W].

**(a) Statement.** The notebook's P14: "Proofs that assume well-bracketed control (every call
returns before its caller resumes) still hold where the operations a callback can perform
preserve well-bracketing." Three parts.

- **(P14.a)** Tier 1 is well-bracketed by construction: no frame or record a run opens is open at
  any of its stops (R-T1).
- **(P14.b, T7's shape, in done)** A value today's Core proves valid, at a type whose callbacks
  can perform only operations in `{fn, abort}`, stays valid in W at every index reachable from its
  σ = [] index. In this kernel `fn` operations are answering effects, which are borrows and not
  rows (I4), so the class is the row-abortive types (`VTy.AbortRows`, §4.2). Library proofs
  carried out in Core at those types survive tier 2 at the level of the relation.
- **(P14.b′, every type, beside done)** The same at every type: A7 in full. The survey's §6 calls
  it open (item 3), and a Core proof at a type with a resuming callback may use R-T1 (`WBCore`)
  about that callback.
- **(P14.c)** What tier 2 gives up is a proof principle, not a valid value: R-T1 itself, which
  W's runs from σ = [] need not meet once something is held at a stop. It is stated only as a
  machine-checked obstruction when one is built; an example would be a Core proof that uses
  `WBCore` on a run that W lets stop with a lend held. This design claims none.

**Against today's relation.** Both P14.b forms read `vCE none`, Core's relation as this branch
imports it. If OQ-58 (b), or a change of `wpG`'s stop condition, redefines Core's relation, a
conservativity stated against the redefined relation would be true by definition and would not
cover proofs done against today's Core, which is what A7 and Dreyer–Neis–Birkedal are about. So
`Targets/Audit.lean` pins Core's relation: a `run_meta` compares the definitions of `vCE`, `cC`,
`wpTS`, `wpG`, `ewpTS`, `opTable` and `contShare` with recorded hashes, and fails the build if
any changes. A redefinition then keeps today's relation under a new name (`vC₀`, a copy, not
deleted), and both P14.b forms are restated against `vC₀`; a redefined Core cannot meet them by
definition.

**(b) Definitions.** §1.3, §4.2 (`VTy.AbortRows`).

**(c) Lean.**

```lean
/-- **P14.a.**  wpG's conjunct (`Core/EffDefs.lean:40`). -/
def WBCore : Prop :=
  ∀ ls e (Q : List SRec → Expr → WProp) ρ, wpG ls e Q ρ →
    wpG ls e (fun ls' t ρ' => Q ls' t ρ' ∧ ∀ x, x ∈ ls' ↔ x ∈ ls) ρ

/-- **P14.b, T7's shape**: today's Core relation embeds into W at row-abortive types, at every
index reachable from σ = [], in both modes.  A conjunct of done. -/
def ConservativeWB (M : SemWorld) : Prop :=
  ∀ b A ls δ v ρ, A.AbortRows → vCE none b A ls δ v ρ →
    ∀ i', M.Ext (ls, M.nil) i' ρ → M.val b A i' δ v ρ

/-- **P14.b′, every type**: A7 in full.  Beside done. -/
def Conservative (M : SemWorld) : Prop :=
  ∀ b A ls δ v ρ, vCE none b A ls δ v ρ → ∀ i', M.Ext (ls, M.nil) i' ρ → M.val b A i' δ v ρ
```

The quantifier is guarded: only indices reachable from the value's own σ = [] index along W's
Kripke order, never a lend stack unrelated to the value. With `Mono`, it is enough to prove each
form at σ = [] itself, the embedding of Core into W's nil slice.

**(d) Literature.**

- Timany–Guéneau–Birkedal, POPL 2024: "A program is said to be well-bracketed if every called
  function must return before its caller can resume execution". On handlers: "We conjecture that
  it is the case if there are reasoning principles in place that can be used as the basis for our
  logic".
- Dreyer–Neis–Birkedal 2010, as the survey quotes them: exceptions cause a "well-bracketed" kind
  of control effect.
- The survey's T7: "for every library L proved sound against well-bracketed contexts: L remains
  sound in every context whose operations, as observable from L's callbacks, are in {fn, abort}".
  The survey's §6 calls this open.

`ConservativeWB` is T7 at our kernel: the class `{fn, abort}` read as row-abortive types, the
library "proved sound against well-bracketed contexts" read as a value Core's relation holds, and
"remains sound" read as W's relation holding at every future index. The survey's "realistic first
theorem" is this one ("libraries whose callbacks perform only tail-resumptive or abortive-unwinding
operations keep their proofs"). `Conservative` is the every-type form; it is not in done because
the notebook's P14 is the class-restricted statement and the every-type one is an open problem.
§10 asks the user whether done should hold it.

**(e) Existing Lean.**

- `WBCore` holds by `wpG`'s definition. PROVED.
- `ConservativeWB coreW` and `Conservative coreW` are `vC_local` (both modes). PROVED.
- WorldW's `ewpTS_ewpW` (Core's `ewpTS` embeds into the draft's `ewpW`) is evidence for the
  embedding direction [probe]; the converse, R-T1 for tier-1 programs, is open there.
- Both forms at the end state: OPEN.

**(f) Non-vacuity.** Every Core-valid value, at its own index; at row-abortive types, every
extern of `Core/Stdio.lean` meeting its contract (`stdModel_meets`).

**(g)** P14.a and P14.b (T7's shape) are in the first pass. P14.b′ is beside done. P14.c is a
statement shape only.

---

## 7. The survey's A1–A7 and T0–T9

| survey | here | how |
|---|---|---|
| A1 type soundness with suspended frames | T1, FL, I1 | **Restated.** Semantic: Σ's job (type continuation values and their loans) is I1 (`M.val true (kTy …)`), and preservation is I2's `Arises`. No syntactic preservation (OQ-52, moot). "Resuming a flagged continuation is stuck" is not adopted as a machine flag (OQ-50 (b)); linearity is by typing. |
| A2 effect safety + algebra conditions | P2 `EffSafe`, T0 `RowAlgSafe RF ∧ RowLink RF` | **Adopted.** Def. 3.5 and Def. 5.1 at the row form the typing rules use, with row variables (`orowRF` the restricted instance). Def. 7.1/7.6 apply only if masking or type-argument-erasing dispatch is added. |
| A3 multiplicity soundness | P8 | **Adopted for lin/aff, dropped for ω** (decision 63). The kernel's `unr` capture condition stays as built and is covered at tier 1 (Core σ=[]); the end state's typing pin is unr-free. "Where the condition hides": the core is A-normal (`[let]`/`[then]` are the sequencing points), and deep clauses are `!U` (Tang Thm 3.4.3). |
| A4 lifetime and escape soundness | P9, P2 | **Restated.** 6.60 at every type including suspension types, at the typing system's own outlives judgments (`J.out`); capability extent is P2 for performed operations, and 6.60 for capabilities lent by answering handlers (I4). Stated at W only: the machine does not see a use past a lend's end (P9 (a)). The storage bound is OQ-28 (AT07, AT08). |
| A5 exclusivity across the handler | P10, I4 | **Adopted** via the reborrow encoding: rules (a)–(c) are AT05/AT06, and the invariant counts suspended loans through `held`. |
| A6 discard semantics | I3, T1, D9 | **Resource half adopted; continuation-use half deferred to OQ-50 (P8.b).** For a linear core the survey states two halves. The second, "every owned value is dropped exactly once", is `ReleasedOnceAll` (D9) with I3. The first, "every continuation that captures a must-use value is resumed or explicitly discontinued exactly once", is P8.b, which this design leaves unstated until OQ-50 says how a continuation's use is observed. The interception policy is the survey's option (ii), an uncatchable unwind running only finalisers, with their errors kept or suppressed (decision C4; I3.c). |
| A7 conservativity | P14 | **Leak half dissolves**: a `lin`/`aff` continuation is never forgotten, an `unr` one holds nothing, and a dropped one is unwound (I3). **Re-entry half** in T7's shape (`ConservativeWB`, callbacks in `{fn, abort}`), against today's relation, pinned; the every-type form `Conservative` is beside done, open as the survey says. What tier 2 gives up is a proof principle (P14.c), not claimed. |
| T0 effect algebra | T0 | **Adopted** (§6), with row variables, at the row form the typing rules use (`RowLink`). |
| survey T1 capture lemma | I1 | **Restated** semantically. The split `Λ = Λ_E ⊎ Λ_rest` is `PA ⋆ share` at the stop. The ω clause is dropped. |
| T2 preservation | I2 (`Arises`, `StopVisible`, `ShareResume`, the frames, `SpanBorrows`), I3 (`ShareCancel`) | **Restated**: every run ends in W's family, which arises with the held frames counted, the lends spanning a stop included. |
| T3 progress + effect safety | T1 `SafeRuns`, P2 | **Adopted**; the flagged-continuation clause is not adopted (OQ-50). |
| T4 tagged resource conservation | P8, D9 | **Resource half adopted** (`ReleasedOnceAll`, of which P8.a is a reading); **use-count** described, not stated, behind OQ-50. |
| T5 borrow invariants with suspended frames | P10 (i), I2 and P9 (ii), P2 and P9 (iii) | **Adopted.** (ii) "every loan held by a live continuation has a live lender" is I2 with the spanning rules' FL cases: the lend's frame is not exited before the callback ends or is cancelled. |
| T6 discard | (i) T1, `ReleasedOnceAll` (D9); (ii) I3.b; (iii) **dissolved**: a `lin` or `aff` continuation has no weakening, and an `unr` one can be forgotten (`forgetBang`) but holds no resource (`contShare`'s `unr` conjunct), so no forgotten continuation holds a loan; (iv) I3.a (Voigt Thm 3.6's preservation shape) | |
| T7 conservativity | P14.b | **Adopted in its shape**: `ConservativeWB`, at row-abortive types (the `{fn, abort}` class; answering effects are borrows, not rows), against today's relation pinned. The every-type form is beside done. |
| T8 abstraction safety | T3 | **Adopted**, at full strength (row-polymorphic `Tunnel`), out of the first pass. |
| T9 elaboration | none | **Not a target.** Each elaborated program's derivation is checked (OQ-53: a certifying checker per program, decision 12). The elaborator is not proved. |

---

## 8. The survey's seventeen programs, as acceptance targets

Each is a closed Core term with a verdict at a tier.

- **Accept** means `J.closed e C`, and T1's conclusion holds of `e` with the stated observation.
  AT02, AT04, AT12 and AT17 are the end state's conjunct `AcceptsTier2` (terms in D14).
- **Reject** means `¬ ∃ C, J.closed e C`. Non-derivability needs inversion lemmas, which D21 says
  to take on only with the cost stated. Each reject is proved only where a track needs it, and is
  outside the first pass.

The survey's multi-shot programs are dropped (decision 63). Where a program has a one-shot
analogue, the analogue is kept.

| # | survey program | here | tier 1 | tier 2 | evidence |
|---|---|---|---|---|---|
| 1 | linear or owned value captured by a multi-shot continuation | **dropped** (multi-shot). If `unr` stays, the kernel already refuses it: `unr` share `∅`, and `[let]` asks `Persistent Γ₂` at `Unr` rows. | — | — | `Core/EffDefs.lean:146`, `Core/EffRules.lean:896` |
| 2 | `region (let r = ref local 0 in do Foo r; !r)` | **AT02** (`at02`): a cell lent mutably to a callback that performs a once-resuming `Foo`, handled outside the lend, then reads through the lend. The multi-shot half is dropped. | reject (`Row.Unwind`; semantically R-T1) | accept: `inj₁ ()` | `corpus/reject/gen-self-borrow.bc`; GhostEnd `withbor_spans_yields_cC` (the lend is in `cC` at σ=[]) |
| 3 | `g := λf x. f(); x`, multi-shot `f`, affine `x` | **AT03**, the linear-core analogue: `f` performs an affine (cancellable) operation while an owned `x` with no finaliser is live. | reject (`[let]`: `S.Weak → Γ₂.Drops`); accept with a `[then]` finaliser releasing `x` at the cancel | same | `corpus/reject/effect-abort-live.bc` |
| 4 | `v.push(do choose())`, multi-shot | **AT04** (`at04`), the one-shot analogue: a `Mut` lend of `v` live across a resuming operation, its answer written through the lend. | reject (`Row.Unwind`; semantically R-T1) | accept: `(inj₁ (), inj₂ ())` | as AT02 |
| 5 | two `&mut` into handler state from one handler | **AT05** | reject (the capability is `Mut 'h S`, which has no copy rule) | reject | HandlersAsBorrows `twoBlocks_refused` [PAPER]; `corpus/reject/io-capability-twice.bc` |
| 6 | a clause writes a place the suspended body borrowed | **AT06** | reject (clauses are `!U`: persistent context; a body's lent place reaches a clause only through the operation's argument, as a lend ending at the resume) | reject | `corpus/reject/effect-clause-op.bc`, `effect-try-lend.bc` |
| 7 | a boxed continuation capturing `&x`, stored past `x`'s frame | **AT07** | reject (R-T1: no lend in a continuation) | reject (P9's bound, OQ-28) | — |
| 8 | a continuation in a shared cell, read twice; moving it out allowed | **AT08** | reject reading twice (`kTy` at lin/aff is neither `Drop` nor persistent; an `Imm` view of a thunk is `True` and cannot be forced); accept moving out and using once (`storeCancel`) | same | `storeCancel` PROVED [Core σ=[]] |
| 9 | an abort while guards are live | **AT09** | accept: each finaliser runs once, via unwinding (`UnwindOrder`), and every run frees every cell | same | `reborrowRaise`, `failOutside`, the `*U` constants: PROVED [Core σ=[]] |
| 10 | a higher-order function would accidentally handle its argument's effect | **AT10**: `hof g = hnd_n (g ())`, with `g` performing a name `m ≠ n` handled outside | accept; on every run, no clause of `hnd_n` fires on `g`'s operations (from P2) | same | the full-strength form is T3's `Tunnel` |
| 11 | a resumption applied under a different handler | **AT11** | accept where typed: `κ`'s row is in its type, so the resume site handles it and P2 forbids an unhandled operation. "The same handler instance" is binary (T3). | same | — |
| 12 | `thread::scope` with the handler dropping `k` | **AT12** (`at12`), single-threaded: a lend spanning an affine operation inside a continuation that is cancelled; the lend's finaliser runs exactly once, during the cancel, before the owner's memory is released | accept the lend-free form (`takeProg n`); reject `at12` (`Row.Unwind`) | accept `at12`: `inj₂ ()` | `takeProg n` PROVED [Core σ=[]]; GhostEnd `spans_two_affine_yields` |
| 13 | `forget(k)` where `k` holds an outside loan | **AT13** | reject: a `lin` or `aff` continuation has no weakening (`kTy` at `lin`/`aff` is a thunk, and the `forget` constants are at `Imm`, `Mut`, `!` and `Unk`); discard is an explicit cancel. An `unr` continuation, `!U(…)`, can be forgotten (`forgetBang`), but its share is `∅` (`contShare`), so it holds no loan to leak | reject (the end state's pin has no resuming `unr` operation) | `Core/Fundamental.lean` `forget*` rules; `Core/EffDefs.lean:146` |
| 14 | a frame inside `k` swallows the discard-unwind | **AT14** | impossible: `NoInterception` (I3.c); a finaliser's error is kept or suppressed and never resumes the cancelled code | same | `prog_run`, `prog₃_run` PROVED |
| 15 | `op<'a>()` resumed twice by a multi-shot handler | **dropped** (multi-shot) | — | — | — |
| 16 | `RefCell::borrow_mut` held across a `perform` | interior mutability is absent (open, decision A7); the static analogue is AT06 | reject statically | reject statically | — |
| 17 | a borrow of a local across a `perform`, in a movable first-class continuation | **AT17** (`at17`) | reject (`Row.Unwind`; semantically R-T1) | accept: `inj₁ ()`. Borrowed locals are heap cells, and a frozen continuation holds no address of its own frames (the binder); placement by the lowering is T4's concern | — |

**Existing acceptance programs**, all PROVED at [Core σ=[]] by `adequacyD`/`adequacyD_obs` and run
by the interpreter:

- `logOutside`, `failOutside`, `nLogOutside`, `nFailOutside`;
- `logInBorrow`, `reborrowRaise`;
- `tickProg n`, `tickAnsProg n`, `takeProg n`, `storeCancel` (`Core/EffPrograms.lean`);
- `prog`, `progC` (`Core/EffExamples.lean`);
- `prog_run`, `prog₃_run` (`Core/EffCancel.lean`).

Status.lean records each against T1's restricted instance. The GhostEnd `spans_*` lemmas are σ=[]
evidence that tier-2 programs can be put in Core's relation by the ghost end (OQ-9 (b)), without a
typing rule. The end state does not ask that of them: it asks only that Core embed into W (§4.2).

---

## 9. What to prove now, and what stays open

**First wave.** Each item is provable from existing Lean with modest work. The order is the
builder's. Together with the second wave they make `Tier1End`. Each item's status is in
`Targets/Status.lean`.

| # | target | world | from |
|---|---|---|---|
| 1 | `(closedRowAlg Ξ).Laws ∧ (closedRowAlg Ξ).Safe`, then `RowAlgSafe orowRF`, `RowLink orowRF` | [prog] | list and lookup lemmas on `Row.ofEff`; `ORow` append lemmas; the reading's lemmas (D2) |
| 2 | `coreW`, the transports (`ptoMutSW_core`, `ptoImmSW_core` included); `WLaws coreW` but `AdequateEvery` | Core σ=[] | unfolding; `vC_local`; `Ext.refl`/`trans`; `cC_effOf`; `opTable_mono`; `vC_data` (new); Core's clauses with `cC_nu_iff`, `vC_unfold` |
| 3 | `CDerivesNU`, `CDerivesNU.toCDerives`; `Extends tier1`, `ExtendsNU tier1`, `FL coreW tier1` | Core σ=[] | transcription; `CDerives` pointwise; `fundamentalC` at every instance |
| 4 | `SoundnessOfFL`, `SoundnessContractsOfFL`, `EffSafeOfFL` | generic | composition |
| 5 | `AdequateRetAt coreW Platform.none` | Core σ=[] | `theorem32D`, `adequacyD_obs`, `total_*` |
| 6 | `SoundRetAt tier1 Platform.none` (T1 restricted) | [prog] | 3 + 4 + 5 |
| 7 | `wpG_demonic`, `stop_irreducible`; then `AdequateEvery coreW` and `EffSafe tier1` (P2) | Core σ=[] / [prog] | `wpTS_demonic`'s replay at `wpG`; `head_plug`, `plug_decomp` |
| 8 | `I1 coreW` | Core σ=[] | `ewp_handle`'s `[op]` case + `vC_kTy_of_kapRel` |
| 9 | `I2 coreW OutJ.core admClosedOp .abortive`: `Arises`, `StopVisible`, `ShareResume`, `FramesW coreW .abortive`, `SpanBorrows coreW OutJ.core admClosedOp .abortive`; recorded PROVED AT A RESTRICTION (abortive rows) | Core σ=[] | unfolding; `ewpTS_*_frameU`; `wpG_*_frameX` with `ewp_bot`; the six `*U` compat lemmas |
| 10 | `I3 coreW` (`ShareCancel`); recorded PROVED AT A RESTRICTION (nothing held) | Core σ=[] | `cancelOwed` through `cancelTabW_core` |
| 11 | `AdmExtends admClosedOp`, `OutExtends OutJ.core` | [prog] | `id`; `VOutlives.toLe` |
| 12 | `NoInterception tier1` (I3.c) | [prog] | induction on `CDerives` |
| 13 | `I5 coreW`: `I5beta` (generic), `AntiFrameW coreW`, `FrameW coreW` (proved before it is recorded) | generic / Core σ=[] | `ewpW_step`; GhostEnd `ewpTS_M_antiFrameR` through `ptoMutSW_core`; `ewp_frame_plain` through the transports |
| 14 | `I4a tier1 admClosedOp .abortive` | [prog] | a derived rule from `withbor2U`, `alloc`, `free`, `withswap` |
| 15 | `LifetimeSound coreW OutJ.core` (P9) | Core σ=[] | `vC_outlives`, `vC_outlivesLe` |
| 16 | `Exclusive coreW` (P10) | Core σ=[] | `exclusive_of_arises` with `TW.inv`, `TW.valid` |
| 17 | `HandleCompat coreW` (P11) | Core σ=[] | `handle_compatC` |
| 18 | `WBCore`, `ConservativeWB coreW`, `Conservative coreW` (P14) | Core σ=[] | definitional; `vC_local` |
| 19 | `Targets/Audit.lean`: the step-index audit run on `coreW`; the pin of Core's relation | meta | `run_meta`, after Restrat's audit |
| 20 | the existing acceptance programs against T1 | [prog] | `Core/EffPrograms.lean` |
| 21 | the two-frame `UnwindRun` of §5 I3, in `Targets/Restricted` | [prog] | the scratch check's proof, re-proved |

**Second wave** (still σ=[]):

- `AdequateOfLaws` in general;
- `SoundRetAt tier1 P` for platforms with operations (adequacy across platform answers), then
  `Soundness tier1`;
- `SoundDriveAt tier1 Platform.none` (the drive);
- `SoundnessContracts tier1` (externs at rows, under every platform);
- `ReleasedOnceOfSound` (D9), then `ReleasedOnceAll tier1` (and so P8.a);
- `FinaliserOrder tier1` (`CancelOrder`, `UnwindOrder`);
- `RedLaws coreW` (determinism with the replay);
- `BinderMachine` at `rs = []` (port TwoRun's `steps_rename`, `split` added);
- the arising check of Restrat's `not_vDenNatural` witness at `coreW`, as an elaborating `def`;
- the AT-rejects a track needs, with their inversion lemmas' cost stated.

`status_tier1End : Tier1End` closes the two waves.

**Open: done.** `EndStateAt J₂ W Adm RF` at a named world W and the kernel's unr-free tier-2
judgment, with `audit_W`. Its parts, none proved at any world but `coreW`:

- `FL W J₂` with `Tier2Pinned J₂ Adm` and `AcceptsTier2 J₂`, so `Soundness J₂` for tier 2;
- `I4a J₂ Adm .any`, the borrow form of answering effects at the rows a lend may span;
- `WLaws W` at σ ≠ [] (`SliceShape`, `Mono`, …);
- `I1 W`, `I2 W J₂.out Adm .any` (the frames at resuming tables and the spanning borrows), `I3 W`,
  `I5 W`;
- `LifetimeSound W J₂.out` at the outlives judgments the kernel adopts (OQ-28);
- `Exclusive W`, `P11 W`, `ConservativeWB W`;
- `RowAlgSafe RF ∧ RowLink RF` at the row form OQ-13 settles;
- `audit_W`.

**Beside done** (§1.0's table): `FreezeBinder` and `BinderMachine` at block-affine permutations
(OQ-43 (b)), starting with the arising check; `Conservative W`; `ReleasedOnceReuse J₂`;
`CancelCloses` (named-only, OQ-57); P8.b (named-only, OQ-50); `I4Typing J₂`.

**Binary and cross-language, out of the first pass:** T2 `Laws`, T3 `Abstraction` (its proof
device named-only), T4 `LoweringCorrect` and `ZeroCost` (named-only), I4.b's rejections, `I4c`.

---

## 10. What this design leaves open, and where each question lives

| question | where it sits | how the end state stays open on it |
|---|---|---|
| OQ-56: operation types at a borrow callback | `EndStateAt`'s parameter `Adm`; `RowSpan`; `AdmExtends` | `admClosedOp` is option (a), the restricted instance and the lower bound (`AdmExtends`). Option (c) is a wider `Adm` in the same rule shape. Option (b), lifetime-polymorphic operations instantiated at the lend, changes the rule shape (the callback's row is an instance of the handler's), and `SpanRules` is restated over it when (b) is chosen. A wider `Adm` makes the end state stronger. |
| OQ-28: a stored continuation's bound | the typing system's field `J.out`; `OutExtends`; AT07/AT08 | every rule transcription reads `J.out`, so `LifetimeSound M J.out` certifies the outlives rules the typing system uses; `OutExtends` bounds it below by Core's |
| OQ-8: where the future-world quantifier goes | `SemWorld.share`, `.val`, `.Ext` | `RelElim` is stated at the same index; `ShareResume`/`ShareCancel` are stated over `M.Ext`-futures, a property both options have. **`Mono` constrains it**: it excludes every placement under which W's relation is not monotone along `M.Ext`, and at the binder-clause placement it asks `EwpMono` (index-monotonicity of `ewpW`), which nothing proves at a binder-clause candidate (GhostEnd's `gRL*` lack it). This is the sign-off's "one Kripke world" read as Kripke monotonicity |
| OQ-9, OQ-10: lends across a stop, carried open in σ or ghost-ended | `SemWorld.held`, `.Fam`, `.Stop`; `MutFrameW`/`ImmFrameW` | `Arises` counts the held frames without saying where they are kept; `StopVisible` fixes only the visible discipline; under (b) nothing is held. The frames at W are stated in the printed rule's shape with stops (the lend quantified once, `O151AsStated`); GhostEnd proves the re-lendable (b) variants at Core's `ewpTS`. Whether (b) gives the stated shape is GhostEnd's open `O151AsStated`; if it cannot, `MutFrameW`/`ImmFrameW` decide OQ-9 for (a). Recorded, not assumed |
| **The stop condition at resuming rows** (beside OQ-58) | `SemWorld.Stop`; `SliceShape` | R-T1 (`Core/EffDefs.lean:40`) is "our conjunct, not a printed row" (the brief), and effects change "the wp and its stop condition". The end state pins `Stop` only between nil indices, where nothing is held. It does not pin today's `wpG` at σ = [] for computations at resuming rows: an equivalence there would put every tier-2 computation that starts at σ = [] in today's `cC`, with R-T1 at every stop and `↭` forbidding a run to end with a borrow cell it created (§4.2). LoopBorrow found that a lend spanning runs "needs a model change: a borrow that `↭` lets outlive the run that opens it" (`refoldKripke_false`, `refold_fails_at_consumer_frame`, at a list that arises) |
| OQ-44, OQ-57: what σ holds; a closing obligation beside W | `SemWorld.Stk`, `held`; `ShareCancel`; `CancelCloses` | abstract. `ShareCancel`'s closing clause is option-neutral (the cancel's end holds nothing its start did not). "Ends every lend it holds" needs the frames a continuation froze, which is OQ-57's accounting; `CancelCloses` is named-only until then, and its program-level form (`CancelOrder`, `Final`, `ReleasedOnceAll`) is in done |
| OQ-58: Core as the σ = [] instance | `SliceShape`; `ConservativeWB`; `Conservative` | read as: the nil slice is Core's in structure, and Core's relation embeds into W at σ = [] (at row-abortive types in done; at every type beside done), against today's relation pinned by `Targets/Audit.lean`. Redefining `vC` (OQ-58 (b)) keeps today's as `vC₀`, and both conservativity forms keep reading it |
| OQ-7, OQ-41: finalisers at a resuming table; a continuation captured inside a cancel | I3.b | stated over complete runs only, with no termination claim |
| OQ-43: two-run facts with array steps | `BinderMachine`, `FreezeBinderLoc`, `ReleasedOnceReuse` | stated at block-affine permutations (option (b)), beside done; the array-free instance is the restriction |
| OQ-13 (remaining): the kernel's row-variable form; rank-n row polymorphism | `EndStateAt`'s parameter `RF`; D2 `RowForm`, `RowLink`; §1.2 | T0 is stated at the row form the kernel adopts, linked to the typing rules' row operations; `orowRF` (the minimal tail-variable form) is the restricted instance. Typing reads row variables by their closed instances (prenex). Rank-n needs semantic tables at W as row denotations |
| OQ-46: the world a stored payload is read at | `SemWorld.payStk`; `ptoMutSW`/`ptoImmSW`; `RelShape` | `RelShape` transcribes Core's `Imm`/`Mut` clauses with W's relation for the payload; only the stack the payload is read at, `payStk`, is open |
| OQ-50: how linear use is observed | P8.b | not stated (named-only, beside done); the resource half is `ReleasedOnceAll`, the default (c) |
| OQ-3: does a handler site open a lifetime | none | no target needs it; I4's borrow form opens one by construction (`withbor`) |
| OQ-14: static names or generative instances | D11's instance half; `LawNuOp` | vacuous under static names |
| OQ-19, OQ-30, OQ-34, OQ-51: comodel meaning, I/O presentation, BoLo-as-runner, adequacy at a row | `Platform` (D5), `SoundnessContracts`, T1's scope | the comodel is state-access only and serves linear data operations, so main's row holds only platform operations and an error must be handled before the top (OQ-51 (a)); externs and platform are stated together; allocation stays in the machine |
| OQ-61: effect-recursive signatures | D2 labels | labels carry no typelike argument; T0 is restated if signatures may mention rows |
| OQ-1: answering vs control handlers | `I4Typing` (unary), `I4c` (binary); D13's `capPass` | I4.a holds for the borrow form, which exists today; the two forms are related on the spine, where `capPass` is defined; a translation of every body is OQ-1's design question |
| OQ-23: is lowering correctness a theorem; the control class's cost model | T4 | named-only, out of the first pass; `ZeroCost`'s control class has no reference encoding until answered |
| OQ-27: η and its typing check | T2 `CapEta` | stated up to renaming |
| OQ-47, OQ-49: reduction in `≡`; the composite handler | T2 | the first lemma of the binary relation; `LawFusion` takes the composite construction `fuse` as a parameter |
| OQ-52: syntactic subject reduction | none | no target uses it |
| OQ-16: multi-shot | §1.2 `CDerivesNU`, `Row.NU` | ignored (decision 63): the end state's pin is the unr-free fragment, and W is unconstrained at resuming `unr` rows. `CDerivesNU` copies `CDerives`'s rules into Targets; the alternative decision 63 allows, restricting or removing `unr` in the kernel, would make the copy unnecessary |

**Questions for the user.** Three readings in this design need the user's confirmation, because
each fixes how strongly a signed-off phrase is held:

1. **"vC/cC are the σ = [] instance."** Read at every type as an equivalence, together with tier
   2, it says every tier-2 computation that starts at σ = [] is in today's `cC`, with R-T1 at every
   stop: that decides OQ-9 for the ghost end (b). This design reads it as the structural nil slice
   plus the embedding of Core into W (§4.2). Was the equivalence meant?
2. **Conservativity's scope.** Done holds T7's shape (`ConservativeWB`, row-abortive types), as
   the notebook's P14 states it. The every-type form (`Conservative`, A7 in full) is beside done.
   Should done hold the every-type form?
3. **The freeze binder.** It is beside done (`EndStateBinder`), as the notebook lists its
   unifications as hypotheses to check. Should done require it once its lifetime half's form is
   settled?

---

## Corrections

The builder's departures from the definitions as first printed. Each is minimal, and the
definitions above are the corrected ones.

- **C1. `SemW₀`** (§1.3). As printed, the clause `.val A => SemW₀ M Δ Γ e (.comp (.ret A))` calls
  `SemW₀` at a judgment that is not a subterm of `.val A`; that is not structural recursion, and
  Lean rejects it. Corrected: both clauses read the computation clause through the helper
  `SemWC`. Same meaning.
- **C2. `SoundnessContractsOfFL`** (§4.1). As printed it asked `ConservativeWB M`, the embedding of
  Core's relation into W at row-abortive types. `ExternsMeet Γ γ` admits an extern at every
  persistent type, `!U(C)` at a resuming row included (`VTy.persistent (.bang _) = true`), so the
  row-abortive embedding does not reach every extern; and taking an extern from Core's nil index
  into W's needs the Kripke order's reflexivity, `ExtPre M`. Corrected:
  `FL M J → ExtPre M → Conservative M → Adequate M → SoundnessContracts J`. The route as printed
  is kept at externs of row-abortive type: `SoundnessContractsOfFLWB`, concluding
  `SoundnessContractsAR J` (`SoundnessContracts` with the premise `∀ s ∈ Γ, s.ty.AbortRows`). Both
  are proved, generically.
- **C3. `ansRun`, `lendCell`, `at04`** (D13, D14). As printed they apply `withborUE d` to
  arguments that are not variables (`app2 (withborUE d) (.var 0) f`) and destructure the call's
  result in place. Core's `[app]` (`CDerives.app`) applies a computation only to a variable, and
  `lolliE` applies only at an arrow into `F`; the unwinding borrow's type `U(src ⊸ cb ⊸ F_Σ R)` is
  neither, so the printed terms have no `CDerives` derivation. Corrected: A-normal form. The
  callback and the constant are bound to variables, the call `w c f` is `[app]` twice, and its
  result is bound by `[let]`. D14's observations are unchanged
  (`Targets/Restricted/Acceptance.lean` runs all four terms).
- **C4. `I4a`** (§5 I4). The borrow form's callback `Λ. λm. body` is typed by `∀I`
  (`CDerives.allI`), whose premises ask that the lend's variable `x` be fresh for every bound of
  `Δ` (`hΔx`) and for every live type of the context (`hΓx`). `Δ.find? x = none` gives neither:
  `Δ` may bind a variable to a lifetime that mentions `x`, and a live persistent slot of `Γ`
  (which `Ctx.DeadP` allows) may have a type that mentions `x`. Corrected: the two premises are
  hypotheses of `I4a`; its conclusion is unchanged. They hold of every well-scoped `Δ` and `Γ`
  with `x` fresh, and `i4a_witness` meets them at an abortive row. Whether `I4a tier1` fails
  without them is not checked.

**Elaboration only, no change of meaning.** `S.NU` is written `Row.NU S` (`Row.NU` is Targets'
predicate on Core's `Row`); `T.down`, `en.down`, `K.plug`, `a.interp` and `Δ.Models` are applied as
functions; `none` is `Option.none` where `Platform.none` would capture it; `PMap.empty` is ascribed
`WRes`; `Flag` is `EffPrograms.Flag`; binders carry their types; D11's actions are the functions
`idxLocAct`, `heldLoc`, `predLocAct`, `entLocAct`, `tabLocAct` and `idxLifeAct`, `heldRestrat`,
`predImgLife`, `entImgLife`, `tabImgLife`; `I1`'s value `⟨kappa n H K, .lam⟩` proves `IsVal` after
unfolding `kappa`; `capPass` is a `def` by well-founded recursion on `Expr.size`, with its
termination proof; `coreW` and the row algebras are reducible; `RowClass` and `Phase` derive
`DecidableEq`.

## Unresolved review findings

The statement review ended with ten major findings. This file was revised in answer to each; the
revised statements were not reviewed again. Each is listed as the review left it, with the
revision that answers it.

1. **`UnwindRun.fin` (§5 I3.b).** A finaliser that raises its own abortive operation leaves
   `(raise p′; raise p)`, a raise under the `seq` frame `ufin` leaves, which no rule reduces and no
   `UnwindRun` reached. *Revision:* `fin`'s `hD` ends at `Kd.plug (raise …)` with
   `Kd.Catches m = false`, and `hr` starts at `(K₀.comp Kd).plug …`. The two-frame program is
   proved in `Targets/Restricted/Unwind.lean` (`two_frame`, `two_frame_steps`, `one_frame`). The
   finding asked for no `ubind`/`hnd` frame in `Kd`; the revision allows handler frames of other
   names (a finaliser may install a handler and raise through it).
2. **I2 and I3 did not state spanning lends or the frames a cancel closes.** *Revision:*
   `FramesW` (6.64 and 6.65 at W, in the printed rule's shape, at resuming tables) and
   `SpanBorrows` are conjuncts of `I2`; `ShareCancel` has the option-neutral closing clause; at
   `coreW` both are recorded PROVED AT A RESTRICTION. `CancelCloses` is named-only under OQ-57.
3. **`FreezeBinder` was a conjunct of done.** *Revision:* it is beside done (`EndStateBinder`),
   its lifetime clauses forward implications.
4. **`Adm` had no lower bound, and the outlives judgment was not the typing system's.**
   *Revision:* `AdmExtends Adm` is a conjunct of `EndStateAt`; `TypingJ` carries `out : OutJ`, read
   by every rule transcription, by `OutExtends J.out` and by `LifetimeSound M J.out`.
5. **Done as an existential could not carry decision 7.** *Revision:* done is `EndStateAt` at a
   named `W` with `audit_W`; `Targets/Audit.lean` runs the audit on `coreW`.
6. **A6 and T7 overclaimed.** *Revision:* A6's continuation-use half is P8.b (named-only, OQ-50);
   `ConservativeWB` (T7's shape) is in done and `Conservative` beside it; Core's relation is pinned
   by hash in `Targets/Audit.lean`, so a redefined Core cannot meet either by definition.
7. **`Slice` pinned R-T1 at σ = [] at every type.** *Revision:* `SliceShape` pins the nil slice
   structurally only; the embedding is `ConservativeWB`; §10 asks the user whether the
   equivalence was meant, and cites LoopBorrow.
8. **`FreezeBinder`'s lifetime half against `not_vDenNatural`.** *Revision:* beside done; the
   arising check of the witness at `coreW` is stated (`NotVDenNaturalArises`) and OPEN.
9. **`Extends` needed resuming `unr` operations at W.** *Revision:* done asks `ExtendsNU`
   (`CDerivesNU`, Core's rules without resuming `unr` operations); `Tier1End` keeps `tier1` at
   Core σ = [] only.
10. **`RelShape`'s `Imm`/`Mut` clauses were not Core's.** *Revision:* they transcribe Core's
    clauses with W's relation for the payload (`ptoImmSW`, `ptoMutSW`, `CohE`); OQ-46 is open only
    in `payStk`.

## Builder's notes

- **`ReleasedOnceAll` holds at every typing system** (`releasedOnceAll`,
  `Targets/Restricted/Release.lean`). Its run premises carry the empty memory at the run's start and
  `Final` at its end; with `NoReuse`, that is all the occupancy argument reads (every allocation
  of `ℓ` is followed by a release, every release preceded by an allocation, and two releases have
  an allocation between them). So the conjunct states exactly-once release in its own words, as
  D9 intends, and its typing content is T1's `Terminates` and `SafeRuns`. `ReleasedOnceOfSound`
  does not use its `SafeRuns` and `Terminates` premises either.
- **`RedLaws` holds at every world whose operation tables are monotone** in what they owe
  (`redLaws_of_mono`), by determinism under one allocator; with `HandleCompat coreW`, `P11 coreW`.
- **`Tier1End` follows from `Adequate coreW` and `FinaliserOrder tier1`** (`status_tier1End_of`):
  every other conjunct is proved, and `Soundness tier1` and `SoundnessContracts tier1` follow from
  `FL coreW tier1`, `ExtPre coreW`, `Conservative coreW` and adequacy.
- **`NoInterception tier1`** is proved at the environment of empty rows, which models every row
  context (`models_empty`).
- **`CDerives.insert_dead`**, weakening by dead slots inserted inside a context with the term
  shifted, is new: Core has `CDerives.append_dead` (at the end) only. I4.a's borrow form needs it,
  because `body` sits under the `Λ`'s slot and the cell.
- **The audit** (`Targets/Audit.lean`) reports, in `coreW`'s closure, recursion on a lifetime
  (`Cell`) and on an array's length (`sepRange`, `tabFill`, `dropFill`), and none on a count of
  steps.

## Sources read

**Repository** (`~/repos/borrow-core-targets`, branch `targets`):

- `docs/effects-state/BRIEF.md`; `01-kernel.md`, `06-bolo-machinery.md`; `04-decisions.md` (summary, K9, K10, F3);
  `05a` (header, F1–F5, OQ-7–OQ-16, OQ-21–OQ-28) and `05b` (header, OQ-35, OQ-40–OQ-46, OQ-50–OQ-52,
  OQ-56–OQ-61).
- `research/effects/src`: intro, method, register, decisions, literature, design-space,
  foundations/*, properties/*, side/multi-shot, tracks/*.
- `research/effects/survey.md`: TL;DR, §1 in full (A1–A7, B1–B5, C1–C7, D1–D4, §1.7–§1.11), §2.
- Core:
  - `EffDefs.lean`, `Relation.lean`, `World.lean`, `FrameRecords.lean`, `Alloc.lean` (all);
  - `Types.lean` (:1-220, :1155-1290, :1725-1770), `EffRules.lean` (:1-260, :284-460, :486-700,
    :960-1156), `EffBorrow.lean` (:1-210), `Fundamental.lean` (:1-440), `EffWp.lean`
    (:540-600, :800-870), `Demonic.lean` (:1-40, :150-359), `Stdio.lean` (:1-60, :590-700),
    `EffPrograms.lean` (:1-140, :540-660, :755-910), `Stale.lean` (:1-40), `RelationFacts.lean`
    (:265, :479-490), `Count.lean` (:39-52).
- `Paper/S3_Dynamics/Definitions.lean` (:290-594, `Kont`, `Head`, `kappa`); `Paper/S1_Syntax`
  (`Expr`, `Prim`); `Support/Dynamics/Arrays.lean` (`Val.arr`, `tabFill`, `dropFill`, `idxAns`,
  `splitAns`).
- Experiments: GhostEnd `Frames.lean` (all), `Program.lean` (:1-230); Restrat README,
  `Injection.lean` (:20-70, :147-170); TwoRun README, `Rename.lean` (:325-430).
- `Backend/Flat/Interp.lean` (`FState`, `interp`), `Backend/Driver.lean` (:230-260),
  `Backend/Counts.lean` (header), `Backend/Kernel.lean` (:1-60).

**Read again for the revision after review.**

- Core: `Relation.lean` (all: `vCE`'s clauses, `ptoMutS`, `ptoImmS`, `CohE`), `EffDefs.lean`
  (all), `World.lean` (all), `FrameRecords.lean` (all), `Fundamental.lean` (:50-420, `CDerives`
  in full: `forgetBang`, the `*U` constants, `effLet`, `effThen`, `effHandle`), `EffRules.lean`
  (:30-50, :150-260 `ewp_frame_plain`, :695-715, :960-1000 `kTy`), `EffBorrow.lean` (:125-215
  `Row.Unwind`, `withborUE`), `EffWp.lean` (:60-100, :355-380, :800-870, :1000-1020), `Types.lean`
  (:30-160, :1720-1860 the outlives judgments), `RelationFacts.lean` (:260-270, :475-585),
  `Stdio.lean` (:585-640 `ExternsMeet`), `Wp.lean` (:455-470 `AddAt`), `EffPrograms.lean`
  (`storeCancel`, `Flag`, `suspSig`).
- `Paper/S3_Dynamics/Definitions.lean` (:280-600: `Kont.Catches`, `Head.ufin`, `ufinC`, `cfret`,
  `cferr`), `Paper/S1_Syntax/Definitions.lean` (:100-260), `Paper/S5_Model/Definitions.lean`
  (:660-690 `box`, `fresh`), `Support/Dynamics/Machine.lean` (`Kont.comp`, `plug_comp`, `Steps`),
  `Support/Dynamics/Host.lean` (`Val.i32`).
- Experiments: GhostEnd `Open.lean`, `Relend.lean`, `ImmLend.lean`, `Frames.lean` (all);
  Restrat README and `Audit.lean` (:1-140); LoopBorrow README; HandlersAsBorrows README (§1–§2);
  WorldW README (branch `probe-open-frames`).
- `docs/decisions.md` decision 59; `docs/effects-state/05a` (OQ-1, OQ-7–OQ-11) and `05b`
  (OQ-43–OQ-46, OQ-50, OQ-51, OQ-56–OQ-58); `06-bolo-machinery.md` §2.2–§2.3.
- A scratch Lean file outside the repository, elaborated against this branch's built `Core`
  (`lake env lean`), checked the revised `UnwindRun` on the two-frame program of §5 I3.

**Paper.** `[TR]` `~/repos/borrow_lang/3764117-supplement.pdf` via `pdftotext`: 6.60, 6.64, 6.65,
6.66 (statement checked against the PDF), 6.151, and the wp row (p. 6). `[CONF]` `3764117.pdf`:
Lemma 3.1, Theorem 3.2, Corollary 3.3 (415:17–18), 415:2, and 415:21.

**Primary literature, fetched and read at the cited statements.**

- Yoshioka–Sekiyama–Igarashi (ICFP 2024, arXiv 2404.16381): Def. 3.1, 3.4, 3.5 (verbatim), Ex.
  3.6–3.8, Def. 5.1, 5.3, Lemma 5.4–5.7, Thm 5.8–5.9.
- Zhang–Myers, Tunneling (POPL 2019, author PDF): abstract, §2 (accidental handling), §6 Example 1
  and Example 2, Thm 1–3, Lemma 6.
- Tang–Hillerström–Lindley–Morris (POPL 2024, arXiv 2307.09383): Thm 3.2–3.4, Def. 3.5, Thm 3.6.
- Brachthäuser–Schuster–Lee–Boruch-Gruszecki, System C (TR version): Thm 3, Lemma 4, Thm 5,
  Lemma 7, Def. 8, Cor. 9.
- Voigt–Schuster–Brachthäuser, Dynamic Wind (OOPSLA 2025): Thm 3.3–3.6.
- Plotkin–Pretnar, Handling Algebraic Effects (LMCS 2013, arXiv 1312.1399): §1.1–1.3,
  Def. 4.2–4.5, Prop. 4.3.
- Ahman–Bauer, Runners in Action (ESOP 2020, arXiv 1910.11629): Def. 1–2, Prop. 3, Thm 6–7.
- Timany–Guéneau–Birkedal (POPL 2024): abstract, §1, Thm 3.1, §8's conjecture.
- van Rooij–Krebbers, Affect (POPL 2025): §2.1 Thm 2.1, §3.2 safety, §5.2 adequacy, §8.
- Congard–Munch-Maccagnoni–Douence (ESOP 2026, arXiv 2510.23517): §3, Thm 9–10, §6.1.
- Ma–Ge–Jung–Zhang, Zero-Overhead Lexical Effect Handlers (OOPSLA 2025): §4 Thm 1, Cor. 1.

**Not read, so cited only through the survey:** Biernacki et al. 2020 (instances as binders),
Lexa 2024, Kammar–Plotkin 2012, Dreyer–Neis–Birkedal 2010.
