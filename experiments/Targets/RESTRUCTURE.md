# RESTRUCTURE: an effect system, a borrow calculus, and their interaction

**What this is.** The design that reorganises `experiments/Targets` (branch `targets`, at `938d280`)
into four parts:

- **A**: an effect system, stated abstractly;
- **B**: the borrow calculus, whose guarantees are given;
- **I**: the interaction, the only place where A and B meet, and the combined theorem;
- **the Instance**: our calculus as one instance of A.

No Lean is written by this design. It supersedes `RESTRUCTURE-v1.md`, whose design and twenty review
findings (`restructure-v1-reviews.json`) are inputs. It also supersedes the architecture of
`DESIGN.md` (§1.0–§1.5, §4.3, §9, and §10's shape of done). The semantic world of `DESIGN.md`
§1.3–§1.4 and `FIX-RUN-END.md` is carried over as the interaction's proof device. Every proved
result of the library at `938d280` gets a home in §4.5, or is listed in §4.6 with the reason it is
restated or retired. Earlier drafts of this file were reviewed three times; §9 maps each finding to
the section that resolves it, and lists what was removed as hardening. **The build** of this design
is recorded in §Unresolved, at the end: the third review's findings, answered and not reviewed
again; every place the Lean departs from this text; and what is not built.

**The framing** (the user, 2026-10-05).

> "We were to define the desired properties of _an effect system_ and tie it in to the core _in the
> interaction between effects and borrows_."
>
> "We have to design this as two systems, which may or may not overlap or be orthogonal. It might
> be possible to use BoLo primitives to produce effect system properties we want… but the primary
> thing is we need an effect system that satisfies the effect algebra and a borrow calculus that
> satisfies BoLo's guarantees and the rules for their interaction."
>
> "There might be a way to get some effect properties we want by leaning on borrow properties but
> it's not necessary."

**The correction this design implements** (the user, 2026-10-06): "if things are still vacuous and
we don't need row variables, i feel like that means our properties are underspecified."

Every target of the library and of v1 was a **soundness** property, an upper bound saying that
nothing goes wrong. A system that rejects every program satisfies all of them. v1 tried to fix this
by requiring the features as fields of the structure:

- row variables as `EffAlg.var`, `VarLaws`, `All`, `genV`, `instV`, `TySubst` and `RowPoly`;
- divergence as a `Loop` type former, typing rules for `next` and `close` at it, and a drive phase
  defined in A;
- linearity as the structural predicates `Drop`, `Pers` and `Structural`;
- acceptance witnesses that the instance itself picks (`Witness`, `AccRowPoly`).

That decreed the mechanisms instead of stating what they are for, and left what must be accepted
to the instance. This design keeps loop formers (`unfold`, `next`, `close`, `drive`) only as
vocabulary for writing the loop programs: A has no loop type and no typing rule for them, and their
laws say only what they do. `unfold`, `next` and `close` are definable from general recursion;
`drive` is the runtime's primitive driver (decision 35: "the runtime drives `main` forever"), and A
treats it as a context, so that every law stated in every context holds inside a driven program
(§1.3).

In this design every target has one of two kinds, and done needs both:

- **(S) soundness**: an upper bound, saying that nothing goes wrong. This covers safety, effect
  safety, termination where it is claimed, the laws of handling, cancellation as built, the
  linear and affine use of continuations, finalisation, and B's guarantees in the composite.
- **(E) expressiveness**: a lower bound, saying what the system **must** accept and run. Each is
  stated with A's own formers, and comes in two forms:
  - a **concrete program** that every instance must type and run with a stated observable
    behaviour: its answer, and the trace of platform operations and finaliser events;
  - a **schema**: one typing of a higher-order value serves a callback at every row, and the value
    calls its callback. This is effect polymorphism in the shape Zhang–Myers give it,
    `f : ∀α. (N → [N]α) → [N]α` used as `f [∅] …` and `f [h.lbl] …`, stated without a `∀` former.

  Each property holds at any distinct labels with the stated signatures, and some such labels
  exist. These are conjuncts of done, not premises.

A decided feature that widens what the system accepts enters A only through an (E) property that
needs it. The user's decision then fixes the mechanism our instance uses to meet that property, and
the Instance records the mechanism (§1.8, §4.2). Where a feature is needed, a Lean lemma shows that
an instance without it fails the property; the lemma is abstract, over every instance, wherever the
absence of the feature can be stated as a Prop (§6.1). A decided restriction (rows as sums of
signatures; no forget for continuations) enters as an (S) requirement instead.

**How these targets are read** (the user, 2026-10-06: "maybe we should tell the agents to use
common sense and not try and game the properties"). The targets state what we are building, and
are read in good faith, as the literature's theorems are. They are not a contract against an
implementer who would special-case a test program, pad a lowering, list rows one by one, or add
frames of its own that catch operations, and they are not hardened against one. So:

- each property is stated as the literature states it, as simply as its intended reading allows;
- non-vacuity is checked against reasonable instances: one with no effects, one that rejects every
  program, and, where a decided feature is needed, one without that feature (§6.1);
- a finding against a target says that its intended meaning is wrong or missing, contradicts a
  decision or the literature, or is vacuous at a reasonable reading. "A contrived instance could
  meet this" is not a finding.

§9.2 lists what this revision removed on that ground.

**Conventions.**

- **Tags.** `[A]` is a statement about every instance of A. `[B]` is about a borrow world
  `M : B.BWorld`. `[I]` is about `M : I.SemWorld`, which extends it. `[prog]` mentions a typing
  system and runs, and no world. `[Core σ=[]]` means `coreB`, `coreW`, `tier1` or `tier1Open`.
  `[PAPER]`, `[SIB]` and `[GE]` are as in the brief.
- **Status.** Status words are `Status.lean`'s: PROVED, PROVED AT σ=[], PROVED AT A RESTRICTION, and
  OPEN. **(checked)** marks a result proved in the library at `938d280`. **to build** marks Lean this
  design asks for.
- **Quotes.** Literature quotes are verbatim from the texts read for this design (§Sources). Symbols
  are transcribed from the PDF (`↠`, `⟦·⟧`).
- **Lean-shaped code.** It fixes each definition's content. Field order, universes and encodings are
  the builder's.
- **Programs.** Each program is given twice, in a named surface notation and as A-terms. The A-terms
  use de Bruijn indices with the innermost binder at `0`.
  - `M to x. N` is `bind M N`.
  - `let (x, y) = V in M` is `split V M`, with `y = 0` and `x = 1`.
  - A clause `op (v, k) ⇒ N` is `lam (split (var 0) N)`, with `k = 0` and `v = 1` inside `N`.
  - `f a` is `call f a`, and `f a b` is `call2 f a b` (both `apps`, §1.3).
  - `let f = V in N` is `bind (ret V) N`, and `lets [v₀, …, vₙ] N` binds `vₙ` outermost and `v₀`
    innermost, so that `var k` in `N` is `vₖ`.

---

## 0. The shape on one page

| part | module | contents | imports |
|---|---|---|---|
| **A** | `Targets/A/*` | `EffAlg` (moved unchanged); `EffectSystem` (§1.3); the machine and typing laws and the (S) properties (§1.4–§1.5); the (E) programs and schemas (§1.6); `Props`; the binary laws (A₂) and the erased lowering over a fixed target with fixed reference programs (A₃), stated and out of the first pass; the abstract non-vacuity lemmas (§6.1) | Mathlib only |
| base | `Targets/Base/*` | Core's machine, typing and rows as B, I and the Instance read them: `Rows.lean` (`RVar`, `Row.NU`, `RowClass`, `RowCon`, `RowCtx`, `RowEnv`, `RowCtx.Models`, `EffCtx`, `RowEq`, `Row.Has`, `Kont.fins`, `cancelOf`); `Machine.lean` (platforms, `PStep`, `RStep`, `Final`, `SafeRuns`, `Terminates`, `SafeDrive`, `SafeDriveFrom`, `StopsIn`, `DivFree`, `PRun`, `Released`, `NoReuse`, `ReleasedOnce`, `VTy.Data`, `DataVal`, and for B5 `Named`, `Expr.mapLoc`, `Heap.push`, `Bump`, `BumpSim`); `RunProps.lean` (the statements about runs that mention no world: `SoundRetAt`, `SoundDriveAt`, `Soundness` as `Sound`, `SoundnessContracts`, `TypedSound`, Core's `EffSafe` and `EffSafeDrive`); `Typing.lean` (`OutJ`, `TypingJ`, `tier1`, `CDerivesNU`, `tier1NU`, the `RC_*`, `Extends`, `ExtendsNU`); `CoreCancel.lean` (Core's `CancelRun`, `UnwindRun`, `CancelOrder`, `UnwindOrder`, `NoInterception`, `HasPrim`, `HndNamesNZ`, `Kont.NoCtl`); `Ctx.lean` (`Obs`, `thunkF`, `CtxApprox`, `CtxEquiv`); `Programs.lean` (the answering implementations: `AnsImpl`, `ansCall`, `ansRun`, `ctlClause`, `ctlRet`, `clausesV`, `ctlForm`, `capPass`); `Data.lean`; `Support.lean` | `Core` |
| **B** | `Targets/B/*` | BoLo's guarantees over a typing system and a **borrow world** `BWorld` with borrow fields only, B0 (`ExtendsB`) among them; each guarantee proved at BoLo by citing `Core` and `Paper`; the routes among them; `Conservativity.lean` (`WBCore`, `ConservativeWB`, `Conservative`); `ReleasedOnceAll` as a lemma about runs | base, `Core`, `Paper` |
| **Instance** | `Targets/Instance/*` | our calculus as one instance of A: `Rows.lean` (`orowAlg`, `closedRowAlg`, `RowForm`, `RowLink`, `orowRF`); `Types.lean` (open types with row variables, and their reading into Core's types); `Typing.lean` (`OurTyping`, `tier1Open`, `J₁`, `J₂`, `⟦·⟧`, `RowVarKernel` as a recorded lemma); `Core.lean` (`AdmEff`, `ourInst`, Core's contexts marked with the driver's phase and the named frames among them, the encodings, the loop interface and the drive, `runnerOf`/`platformOf`); `Bridges.lean` (hypothesis-taking: from Core's statements to A's); `Restricted/*` (results that need no B); `Binary.lean` (A₂ at our instance: the binary laws and abstraction over Core, stated); `NonVacuity.lean` (typing inversions, `monoCallback_tier1Open`, the ContUse witnesses R1–R4, the positive (E) runs); A₃ at the backend | A, base, `Core` |
| **I** | `Targets/I/*` | `World.lean` (`SemWorld extends BWorld`, `coreW`, the effectful wp, the transports); `Interface.lean`; `Pins.lean` (with `spanRules_J₂` recorded); `Programs.lean` (the composite programs); `OpenRel.lean` (`ovalW`, `FLOpen`: the relation at the open types, §4.2); `Device.lean` (with `EmbedsNil`); `RunEnd.lean`; `Binder.lean`; `Restricted/InstanceProps.lean` (every A property discharged at our instance through B); `NonVacuity.lean`; `Combined.lean` | everything above |
| meta | `Audit.lean`, `Status.lean`, `AxiomCheck.lean` | the extended step-index audit with negative tests (§5.2), the record, the axiom check | everything |

**Imports, for definitions and for proofs.**

- A imports nothing of ours.
- Base imports no A.
- B imports no A, no I and no Instance.
- The Instance imports no B and no I.
- So every definition that B or the Instance reads lives in base (if it reads no world) or in B
  (if it reads only `BWorld`'s fields), never in I. §4.5 checks this file by file.

**Where A and B meet.** In proofs, only in I: a theorem that uses a B theorem to prove an A
property lives in I (§4.5's `I/Restricted/InstanceProps.lean`). In statements, the Instance's
bridges take the base's run statements as hypotheses (`Sound ⟦J⟧ → A.Safety (ourInst J)`, Core's
`EffSafe`, `NoInterception`, §4.1). B reads the same statements as guarantees, but the Instance
mentions no B world and no B theorem.

**The combined theorem** (§3.5) is one definition for both tiers:

```lean
/-- **The combined theorem** at our calculus with row form `RF` and typing `J`, world `M`, OQ-56's
admissibility `Adm`, and the class `c` of rows a lend may span. -/
def I.Combined (RF : Inst.RowForm) (J : Inst.OurTyping RF) (M : I.SemWorld) (Adm : I.OpAdm)
    (c : RowClass) : Prop :=
  (∀ Ξ, Inst.AdmEff Ξ → A.Props (Inst.ourInst RF Ξ J))  -- nothing breaks the effect algebra, whatever effects are declared
  ∧ B.Guarantees ⟦J⟧ M.toBWorld       -- nothing breaks the borrow calculus: B's guarantees
  ∧ I.Bounds M ∧ I.Interface M        -- the interaction's option-neutral rules at the world
  ∧ I.Pins J Adm c                    -- what the composite's typing must contain
  ∧ I.Accepts ⟦J⟧ c ∧ I.Rejects ⟦J⟧   -- the composite's (E) programs and the rejections that pin soundness
```

- **Done** is `Combined orowRF J₂ W admClosedOp .any` at a **named** tier-2 typing system `J₂` and
  a **named** world `W`, together with `audit_W`, the step-index audit of `W`'s definition (§5.2).
  Done is fixed at `admClosedOp` until OQ-56 is chosen, and at the row form `orowRF` until OQ-13's
  remaining question (the row form) is answered; a wider `Adm` would make it stronger (§3.5).
- **The effect contexts.** A's properties are asked at **every** admissible effect context Ξ
  (`AdmEff`, §4.1: no resuming `unr` operation, operation types closed in lifetimes, two names at
  each signature the (E) programs use), so the effect algebra holds for whatever effects a program
  declares, not only for the test labels.
- **Tier 1** is `Combined orowRF J₁ coreW admClosedOp .abortive`. It is the same definition at a
  typing system without spanning rules and a row class that admits only abortive operations.
- Tier 1's typing `J₁` has row variables, because A's (E) properties need effect polymorphism at
  every tier (§1.8, §4.3, §7 Q1).

**Where the library's end state went.** §3.5 has the full table. In short:

- A takes the row algebra, effect safety and the continuation discipline, with their (E)
  counterparts.
- B takes soundness, adequacy, the fundamental lemma, lifetimes and exclusivity, and exactly-once
  release with content (#2), which follows from soundness and leak freedom given a machine lemma
  (§2.4).
- I takes arising, the bounds of the world, the pins and the composite programs.
- The option-sensitive conjuncts move to the proof device, beside done: `Mono`, `ShareResume`,
  `ShareCancel`, `StopVisible`, `FramesW`, `SpanBorrows`, `I1`, `I5`, `P11`, `ConservativeWB`
  (#5) and `EmbedsNil` (§3.6).
- Tier 2's spanning rules leave the pins: they are `J₂`'s mechanism for the tier-2 programs, which
  done requires, and `spanRules_J₂` records them, as `rowVarKernel_J₂` records the row `∀` (§3.5).
- `ReleasedOnceAll` leaves done, because it is a tautology about runs (#2).

---

## 1. System A: an effect system on its own

A is judged on its own terms, with no borrows in sight. Its definitions mention no BoLo and no Core.
Our calculus is one instance of it (§4).

### 1.1 What the sources say an effect system must satisfy

| what | source | statement shape (verbatim) |
|---|---|---|
| handlers as models; handling as the induced homomorphism | Plotkin–Pretnar, *Handling Algebraic Effects*, LMCS 9(4:23) 2013 | §1.2: "return V handled with {raise_e () ↦ N_e}_{e∈exc} to x : A. N(x) = N(V)" and "raise_e′ () handled with {raise_e () ↦ N_e}_{e∈exc} to x : A. N(x) = N_e′". §1.3: "computations are interpreted in the free model and handling constructs are interpreted by the induced homomorphisms". Def. 4.2: "A model M of the effect theory T is a set \|M\|, called the carrier of the model, together with an operation op_M : ⟦α⟧ × \|M\|^⟦β⟧ → \|M\| for each operation symbol op : α ↠ β". Def. 4.5: "A handler … is correct at c if the op_H(c) are all total and the set U⟦C⟧ together with the op_H(c) forms a model of T". And: "If the effect theory is empty, then any handler is correct" |
| deep handling | Yoshioka–Sekiyama–Igarashi, arXiv 2404.16381, R_Handle2; Tang–Hillerström–Lindley–Morris, POPL 2024, Thm 3.4 (3) | "v_cont = λz.handle_l S E[z] with h"; "Deep handlers are unlimited: if Δ; Γ ⊢ H : C ⇒ D, then Δ ⊢ Γ : •" |
| progress at the row | Bauer–Pretnar, *An Effect System for Algebraic Effects and Handlers*, LMCS 10(4:9) 2014, Thm 4.1; Tang et al. Thm 3.2 | "If ⊢ c : A ! ∆ then either • there exists a computation c′ such that c ⇝ c′, or • c is of the form val e for some expression e, or • c is of the form ι#op e (x. c′) for some ι#op ∈ ∆"; "If ⊢ M : A ! E, then either there exists N such that M ⇝ N or M is in a normal form with respect to E" |
| effect safety | Bauer–Pretnar Cor. 4.2; Yoshioka Lemma 5.7, Thm 5.8 | "A terminating computation of type A ! ∆ returns a value of type A, or calls an operation in ∆. In particular, a terminating computation of type A ! ∅ does not call any operations and returns a pure value of type A"; "If Γ ⊢ e : A \| 0, then there exist no E, l, S, op, T, and v such that both e = E[op_l S T v] and 0−free(l S, E) hold"; "If ∅ ⊢ e : A \| 0 and e −→∗ e′ ↛, then e′ = v for some v" |
| the row algebra | Yoshioka Def. 3.5, Def. 5.1 | Def. 3.5: "⟨Eff(Σ), ⊙, 0⟩ is a partial monoid under ∼"; "Typelike substitution respecting well-formedness is a homomorphism for ⊙, (−)↑, and ∼". Def. 5.1: "(1) For any L, (L)↑ < 0 does not hold. (2) If (L)↑ < ε and (L′)↑ ⊙ ε′ ∼ ε and L ≠ L′, then (L)↑ < ε′." The gloss: condition (1) "disallows the subeffecting to hide an invoked effect label L as if it were not performed" |
| annotations are operations | Kammar, *An Algebraic Theory of Type-and-Effect Systems*, thesis 2014 (Kammar–Plotkin POPL 2012 could not be retrieved; the thesis, which cites it as previous work [KP12], is quoted instead) | "The key observation is that annotation effects can be identified with the effect operations." |
| linearity of continuations | Tang et al. Def. 3.5, Thm 3.6; van Rooij–Krebbers, *Affect*, POPL 2025, Thm 2.1, §5 | "For any closed, well-typed and linear safe computation M in F◦eff, if M ⇝^S_T N, then N is linear safe and ℒ(M) ∪ S = ℒ(N) ∪ T", so that "tagged linear values are not duplicated or discarded during evaluation". Affect: "Every closed well-typed program is safe w.r.t. the operational semantics", where safety "captures that continuations corresponding to one-shot effects are resumed at most once"; its adequacy says that "one-shot continuations are called at most once, no effects are left unhandled and the expression either diverges or reaches a value" |
| no accidental handling | Zhang–Myers, POPL 2019, abstract and Example 1 | "it is impossible for higher-order, effect-polymorphic code to accidentally handle effects raised by functions passed in; such effects tunnel through the higher-order, calling procedures polymorphic to them"; "Let f be a variable with an effect-polymorphic type T = ∀α . (N → [N]α ) → [N]α", used as "f [∅] (λx : N. x + x)" and "f [h.lbl] (g h)" |
| the platform | Ahman–Bauer, *Runners in Action*, ESOP 2020, Def. 1 | "A runner R for a signature Σ is given by a carrier set \|R\| together with, for each op ∈ Σ, a co-operation op_R : A_op → (\|R\| ⇒ B_op × \|R\|)" |
| effect-dependent equations (binary) | Kammar thesis (11.1), Thm 12.5 | Discard: "Γ ⊢_ε M : F_ε A, Γ ⊢_ε′ N : B (ε ⊆ ε′) ⟹ M ⊨ coerce_{ε⊆ε′} M to x : A. N = N"; "the theory Th_Ax satisfies the Discard optimisation if and only if for every op : n in σ, op(x, …, x) = x" |
| divergence as an effect, and the delay bind | our decision 35 (`docs/decisions.md`); SPEC §14 | "Any function may loop without bound if its type says so; it is not a privilege of `main`, and code without it is total … A div function returns a loop, `A ⇒ U(Loop B R)`; sequencing loops is the delay bind, library code over `unfold`, and running a loop is handling the effect: the runtime drives `main` forever, and `div_fuel` runs `n` steps, which turns div code into total code"; "A higher-order function serves total and div callbacks alike by specialization at the callback's computation type"; SPEC §14: "running a divergent computation is handling the effect" |
| what an effect system must accept | the survey §1.10's test programs; SPEC §19 *Acceptance* and *Programs*; the user's decisions (§1.8) | quoted at each (E) property in §1.6 |

Three things follow from these sources.

- **A is CBPV with an effect index.** It needs:
  - a signature of operations with arities and a control class;
  - rows over the signature;
  - a typing judgement at a row, closed under binding a value (the let law);
  - handlers given by a return clause and a clause per operation;
  - continuations as values that are resumed or cancelled;
  - a way to write a loop that is observed one step at a time, and a driver that runs one without
    bound (vocabulary for the loop programs: codata or general recursion provides the loop, and the
    runtime provides the driver);
  - a labelled small-step semantics whose evaluation contexts include `□ to x. N` and `□ V`;
  - a platform that answers the operations left at the top.
- **The handler laws are equations of reduction.** Our signatures carry no equations (OQ-22). So
  every handler is correct in Plotkin–Pretnar's sense, and correctness means that handling reduces
  as the induced homomorphism does.
- **Cancellation and finalisation are ours.** They are SPEC §19 as built (decision 62). Ahman–Bauer
  Thm 7 and Voigt–Schuster–Brachthäuser Thm 3.6 are possible routes for proving them, not the
  shape of the statements.

### 1.2 Two kinds of property

| kind | what it bounds | what fails it | what a trivial instance does |
|---|---|---|---|
| (S) soundness | from above: a typed program never does something bad | an instance that types a bad program, or whose semantics breaks a law | meets it (typing nothing is sound) |
| (E) expressiveness | from below: these programs are typed and run like this, and one typing serves every row | an instance that rejects a program, cannot express it, runs it differently, or types a higher-order value at one callback row only | fails it (§6.1) |

The (E) properties are chosen so that each decided feature that widens what the system accepts is
**needed** by at least one of them. The property is stated first, and the mechanism comes second:

- effect polymorphism is the property, and row variables are our mechanism;
- divergence that any function may have when its type says so, with loops sequenced, handled,
  fuelled and run by the runtime, is the property, and `Loop` codata with the delay bind is our
  mechanism;
- abandoning a suspension, typably and with cleanup, and using every continuation once, are the
  property, and linear or affine continuations with an explicit cancel are our mechanism.

A decided restriction is an (S) requirement, not an (E) property: rows are sums of signatures
(S1's `RowSig`, which gives effect safety's `has` its meaning), and no continuation is forgotten
(S6).

The rejections (the REJECT side) follow from (S) properties stated universally (§1.5 S6). The
concrete rejected programs R1–R4 are kept as the witnesses that S6 bites (§6.1).

### 1.3 The structure

A has only the formers that the (S) properties and the (E) programs need. On the type side that
means the data types of the answers and the returner `F_ε A`. A has no function type, thunk type,
continuation type, row binder or loop type. Those are the instance's own.

- **The loop formers are vocabulary.** `unfold`, `next`, `close` and `drive` are how A writes the
  loop programs of E3 and E10. They are not a mechanism: A has no loop type and no typing rule for
  them, and `LoopLaws` and `DriveLaws` (§1.4) say only what they do. `unfold`, `next` and `close`
  are definable in any calculus with general recursion (`unfold f g s` as a recursively defined
  pair of thunks, the first running `f s` and wrapping the next state in `unfold f g`, the second
  running `g s`). `drive` is the runtime's primitive driver (decision 35: "the runtime drives
  `main` forever"): `DriveLaws` asks each of its transitions to be one `top` step, which a driver
  defined by recursion, reaching `drive (next l)` by several steps, would not be. Our instance meets
  the loop formers with `Loop_Σ` codata and the driver with `RStep`'s drive phase (§4.1).
- **The driver is a context.** `driveF` is a named frame with `plug driveF M = drive M`, which
  catches nothing, stops no raise and holds no finaliser. So a driven program stopped at an
  operation is `plug (kcomp driveF K) (perform l i v)`, and every matcher that A states in every
  context (the runner's answer `RStep.io`, `OpStuck`, `StopsIn`, and S4–S6) applies inside a driven
  loop with no change. A driver step acts only on the whole program (`Congr` excepts `top` steps).
- **Contexts.** `Kont` is the instance's whole type of evaluation contexts. A names five frames in
  it (`bindF`, `appF`, `handleF`, `thenF`, `driveF`) and states their laws; the instance may have
  others. Ours is Core's `Kont` marked with the driver's phase, whose `seq`, `cfin` and `ccatch`
  frames are where its finalisers run (§4.1).

```lean
namespace A

-- `EffAlg`, `EffAlg.Laws` (Yoshioka Def. 3.5), `EffAlg.Safe` (Def. 5.1) and `EffAlg.Sub` (`ε₁ < ε₂`)
-- move unchanged from `Targets/Defs/Effects.lean` and `Targets/Statements/EffectSafety.lean`, which
-- define them with no Core in them.

/-- Never resumed (a raise); resumed exactly once; resumed or cancelled exactly once. -/
inductive OpClass | abortive | linear | affine

/-- `op : A ↠ B` at a class.  Arities are value types: operations are algebraic (higher-order
operations: not now). -/
structure OpSig (Ty : Type) where
  arg : Ty
  ans : Ty
  cls : OpClass

/-- What a step shows.  `fire` and `finEnd` mark a finaliser's start and end (the cancellation
traces and the behaviours read them); `io` is the platform's answer, emitted only by the runner's
steps; `top` is a step of the runtime's driver, which acts only on a whole program. -/
inductive Ev (Lab Val Term : Type)
  | tau
  | fire (D : Term)
  | finEnd (r : Option (Lab × ℕ × Val))
  | io (l : Lab) (i : ℕ) (v w : Val)
  | top

/-- **An effect system**: any calculus with effects, read as call-by-push-value with an effect
index. -/
structure EffectSystem where
  -- rows: an effect algebra over labels, and the one signature object
  EA      : EffAlg
  Ty CTy  : Type
  sig     : EA.Lab → List (OpSig Ty)
  has     : EA.Eff → EA.Lab → ℕ → Prop          -- the row admits operation `i` of label `l`
  -- types: the answers' data types, and the returner at a row (Bauer–Pretnar's `A ! ∆`)
  UnitT ZeroT : Ty
  Tensor Sum  : Ty → Ty → Ty
  F       : EA.Eff → Ty → CTy
  DivFree : CTy → Prop                          -- the types whose programs the instance claims terminate
  -- terms (CBPV, de Bruijn)
  Val Term Hnd Kont Conf : Type
  var     : ℕ → Val
  unitV   : Val
  pair    : Val → Val → Val
  inl inr : Val → Val
  lam     : Term → Val                          -- the thunk of `λx. M`
  force   : Val → Term
  app     : Term → Val → Term                   -- `M V`
  ret     : Val → Term
  bind    : Term → Term → Term                  -- `M to x. N`
  split   : Val → Term → Term                   -- `let (x, y) = V in M`
  case    : Val → Term → Term → Term
  perform raise : EA.Lab → ℕ → Val → Term
  hnd     : Val → List Val → Hnd                -- a return clause, and a clause per operation
  handle  : EA.Lab → Hnd → Term → Term
  resume  : Val → Val → Term
  cancel  : Val → Term
  thenT   : Term → Term → Term → Term           -- `M then x. N unwind D`
  -- loop vocabulary: a loop from a step, a close and a state; its two observations; the runtime's driver
  unfold  : Val → Val → Val → Val               -- `unfold f g s`: `next` runs `f s`, `close` runs `g s`
  next close : Val → Term
  drive   : Term → Term                         -- runs `M`, which answers `inl a` (done) or `inr l` (drive `l`)
  -- evaluation contexts (all of the instance's), five named frames, and the captured continuation
  hole    : Kont
  kcomp   : Kont → Kont → Kont                  -- `kcomp K₁ K₂`: `K₂` plugged into `K₁`
  bindF   : Term → Kont                         -- `□ to x. N`
  appF    : Val → Kont                          -- `□ V`
  handleF : EA.Lab → Hnd → Kont
  thenF   : Term → Term → Kont                  -- `□ then x. N unwind D`
  driveF  : Kont                                -- the runtime's driver around a program: `drive □`
  plug    : Kont → Term → Term
  catches : Kont → EA.Lab → Bool                -- has a handler frame of the label
  unwindClear : Kont → Prop                     -- no frame of it stops a raise, other than a handler of the raise's label
  fins    : Kont → List Term                    -- its finalisers, innermost first
  capture : EA.Lab → Hnd → Kont → Val           -- κ, handed to the clause of a caught operation
  cancelOf : EA.Lab → Hnd → Kont → Term         -- the start of κ's cancel run
  -- runs
  init    : Term → Conf
  term    : Conf → Term
  setT    : Conf → Term → Conf                  -- the same store, another term
  step    : Conf → Ev EA.Lab Val Term → Conf → Prop
  -- typing: values and computations in a context of value types
  derV    : List Ty → Val → Ty → Prop
  der     : List Ty → Term → CTy → Prop

/-- **The platform**: a runner (Ahman–Bauer Def. 1) for the operations it answers. -/
structure Runner (S : EffectSystem) where
  answers : S.EA.Lab → ℕ → Prop
  St      : Type
  s₀      : St
  co      : St → S.EA.Lab → ℕ → S.Val → Option (S.Val × St)
```

**Each field, and what needs it.**

| field(s) | needed by |
|---|---|
| `EA`, `sig`, `has` | S1 (the row algebra and the one signature object), S3 (`StopsIn`), the programs' labels |
| `UnitT`, `ZeroT`, `Tensor`, `Sum`, `F` | the (E) programs' answer types; `sigExn`'s answer `0`; S2's and S3's types |
| `DivFree` | S2's termination clause, pinned from below by `DataDiv` |
| the value and computation formers | every (E) program; the S4 laws; the let law |
| `perform`, `raise`, `hnd`, `handle`, `resume`, `cancel`, `thenT` | the effect formers of the programs; S4, S5, S6 |
| `unfold`, `next`, `close`, `drive` | writing E3 and E10 (loops built and observed anywhere; the driver at the top); `LoopLaws`, `DriveLaws` say what they do |
| `Kont`, `hole`, `kcomp`, `bindF`, `appF`, `handleF`, `thenF`, `plug`, `catches`, `unwindClear`, `fins` | `StopsIn`; S4 in every context, under binds and applications included; S4's finaliser law and S5's traces, whose finalisers run in contexts of the instance's; `CallsThrough` |
| `driveF` | the runner's answers, `StopsIn` and S4–S6 inside a driven program (E3a–f, E10), through the laws stated in every context; `DriveLaws`' non-`top` steps, as `Congr` at `driveF` |
| `capture`, `cancelOf` | S4's catch, resume and cancel laws; S5; S6's observation |
| `Conf`, `init`, `term`, `setT`, `step` | runs; every behaviour |
| `derV`, `der` | typing at a context: the let law; the schemas of E1, E2, E6 and E10 type the use of a higher-order value with its type in the context |
| `Runner` | the platform; S2; the programs that observe platform operations |

**Derived, in `Targets/A/System.lean`, one line each.** `S.Ev` is `Ev S.EA.Lab S.Val S.Term`.

```lean
def IsVal (c : S.Conf) : Prop := (∃ v, S.term c = S.ret v) ∧ ∀ ev c', ¬ S.step c ev c'   -- returned, and done
def PureStep (c ev c') : Prop := S.step c ev c' ∧ c' = S.setT c (S.term c')    -- the store unchanged
def PureSteps : S.Conf → S.Conf → Prop := ReflTransGen (fun c c' => ∃ ev, S.PureStep c ev c')
def PureJoin (c c' : S.Conf) : Prop := ∃ d, S.PureSteps c d ∧ S.PureSteps c' d
def Reach : S.Conf → S.Conf → Prop := ReflTransGen (fun c c' => ∃ ev, S.step c ev c')
abbrev RConf (R : S.Runner) := S.Conf × R.St
def rinit (R) (e) : S.RConf R := (S.init e, R.s₀)
def setR (c : S.RConf R) (t) : S.RConf R := (S.setT c.1 t, c.2)
inductive RStep (R) : S.RConf R → S.Ev → S.RConf R → Prop
  | mach {c ev c' s} : S.step c ev c' → RStep (c, s) ev (c', s)
  | io {c s s' K l i v w} : S.term c = S.plug K (S.perform l i v) → S.catches K l = false →
      R.answers l i → R.co s l i v = some (w, s') → RStep (c, s) (.io l i v w) (S.setT c (S.plug K (S.ret w)), s')
-- `RPath R c q` (a run step by step, `q : List (S.Ev × S.RConf R)`), `q.cfg c j`, `q.last c`;
-- `RReach R c c'`; `PurePath c q c'` (a path of `PureStep`s from `c` to `c'`, the runner's state unchanged)
/-- The observable events of a path: the platform's answers and the finaliser events, in order. -/
def Ev.Obs : S.Ev → Bool | .io .. => true | .fire _ => true | .finEnd _ => true | _ => false
def obs (q) : List S.Ev := (q.map Prod.fst).filter Ev.Obs
def CompleteFrom (R) (c) (q) : Prop := S.RPath R c q ∧ S.IsVal (q.last c).1
def SafeRuns (R) (e) : Prop := ∀ c, S.RReach R (S.rinit R e) c → S.IsVal c.1 ∨ ∃ ev c', S.RStep R c ev c'
def Terminates (R) (e) : Prop := (∀ c, S.RReach R (S.rinit R e) c → ∃ c', S.RReach R c c' ∧ S.IsVal c'.1) ∧
  ¬ ∃ f : ℕ → S.RConf R, f 0 = S.rinit R e ∧ ∀ n, ∃ ev, S.RStep R (f n) ev (f (n + 1))
def Answers (R) (ε) : Prop := ∀ l i, S.has ε l i → R.answers l i
-- data: the least types and values built by the data formers
inductive DataTy : S.Ty → Prop | unit | zero | tensor .. | sum ..
inductive DataVal : S.Ty → S.Val → Prop | unit | pair .. | inl .. | inr ..
def Runner.Respects (R) : Prop :=
  ∀ l i o, R.answers l i → (S.sig l)[i]? = some o → o.cls = .linear ∧ S.DataTy o.arg ∧ S.DataTy o.ans ∧
    ∀ s v, S.DataVal o.arg v → ∃ w s', R.co s l i v = some (w, s') ∧ S.DataVal o.ans w
def R₀ : S.Runner := ⟨fun _ _ => False, Unit, (), fun _ _ _ _ => none⟩       -- answers nothing
-- **behaviours**: the answer and the observable trace of every complete run, and that there is one
def RunsTo (R) (e) (v : S.Val) (tr : List S.Ev) : Prop :=
  (∃ q, S.CompleteFrom R (S.rinit R e) q ∧ S.term (q.last _).1 = S.ret v ∧ S.obs q = tr) ∧
  ∀ q, S.CompleteFrom R (S.rinit R e) q → S.term (q.last _).1 = S.ret v ∧ S.obs q = tr
-- a run that never completes: every prefix of `tr` is shown, and every run shows a prefix of `tr`
def RunsForever (R) (e) (tr : ℕ → List S.Ev) : Prop :=
  S.SafeRuns R e ∧ (∀ q, ¬ S.CompleteFrom R (S.rinit R e) q) ∧
  (∀ n, ∃ q, S.RPath R (S.rinit R e) q ∧ S.obs q = tr n) ∧
  ∀ q, S.RPath R (S.rinit R e) q → ∃ n, S.obs q <+: tr n
-- labels: a program's labels have the stated signatures and are distinct; some exist, and every
-- such choice works
def LabelsAt (sigs : List (List (OpSig S.Ty))) (ls : List S.EA.Lab) : Prop :=
  ls.length = sigs.length ∧ ls.Nodup ∧ ∀ k (h₁ : k < ls.length) (h₂ : k < sigs.length), S.sig ls[k] = sigs[k]
def ForLabels (sigs) (P : List S.EA.Lab → Prop) : Prop :=
  (∃ ls, S.LabelsAt sigs ls) ∧ ∀ ls, S.LabelsAt sigs ls → P ls
/-- `apps f [a₁, …, aₙ]` is `f a₁ … aₙ`. -/
def apps (f : S.Val) (as : List S.Val) : S.Term := as.foldl S.app (S.force f)
def call (f a : S.Val) : S.Term := S.apps f [a]
def call2 (f a b : S.Val) : S.Term := S.apps f [a, b]
/-- `lets [v₀, …, vₙ] N`: `vₙ` bound outermost, `v₀` innermost (`var 0` in `N`). -/
def lets : List S.Val → S.Term → S.Term | [], N => N | v :: vs, N => S.lets vs (S.bind (S.ret v) N)
def bool : S.Ty := S.Sum S.UnitT S.UnitT
def tt : S.Val := S.inr S.unitV
def ff : S.Val := S.inl S.unitV
```

**The schemas' vocabulary** (also in `Targets/A/System.lean`):

```lean
/-- `P` calls `M` without catching a label of `L`: it reaches `M` by administrative steps, under a
context that catches no label of `L` and holds no finaliser. -/
def CallsThrough (L : S.EA.Lab → Prop) (P M : S.Term) : Prop :=
  ∃ K, (∀ m, L m → S.catches K m = false) ∧ S.unwindClear K ∧
    S.PureSteps (S.init P) (S.setT (S.init P) (S.plug K M))

/-- `ε` does not admit `l`. -/
def Lacks (ε : S.EA.Eff) (l : S.EA.Lab) : Prop := ∀ i, ¬ S.has ε l i

/-- **A polymorphic use** (schematic).  In the context `Γ`, the use `use g` serves a callback at every
row: for every row `ε` and every closed callback body `M` at `F ε B`, the use is typed at `F ε B'`. -/
def PolyUse (Γ : List S.Ty) (use : S.Val → S.Term) (B B' : S.Ty) : Prop :=
  ∀ ε M, S.der [] M (S.F ε B) → S.der Γ (use (S.lam M)) (S.F ε B')

/-- The same at every row that does not admit `l`: for a higher-order value that handles `l` itself
somewhere, since a handler's label is not in its outer row (SPEC §19's `[handle]`: "`n` not in
`Σ`"). -/
def PolyUseLacks (Γ : List S.Ty) (l : S.EA.Lab) (use : S.Val → S.Term) (B B' : S.Ty) : Prop :=
  ∀ ε M, S.Lacks ε l → S.der [] M (S.F ε B) → S.der Γ (use (S.lam M)) (S.F ε B')

/-- For a higher-order value that handles its own label `l` around the callback: the body is at
`l ⊙ ε`, the use at `ε`, for every row `ε` that does not admit `l`. -/
def PolyUseOpen (Γ : List S.Ty) (l : S.EA.Lab) (use : S.Val → S.Term) (B B' : S.Ty) : Prop :=
  ∀ ε ε' M, S.Lacks ε l → S.EA.comp (S.EA.lift l) ε = some ε' →
    S.der [] M (S.F ε' B) → S.der Γ (use (S.lam M)) (S.F ε B')
```

The schemas quantify over `M` with `der [] M _`, and put `M` under `lam` without shifting: a body the
instance types in the empty context is closed, so the binder of `lam` and those of `lets` do not
capture it. A has no shift or substitution; §1.4 says why it needs none.

### 1.4 S0: the shape of the machine, and the let law

These are the laws that make the formers mean what they are called. They are upper bounds on the
semantics, except the let law, which is a lower bound on typing.

```lean
def ConfLaws (S) : Prop :=
  (∀ e, S.term (S.init e) = e) ∧ (∀ c t, S.term (S.setT c t) = t) ∧
  (∀ c, S.setT c (S.term c) = c) ∧ (∀ c t t', S.setT (S.setT c t) t' = S.setT c t')

/-- Plugging composes.  The five named frames plug as their formers.  A handler frame of `l` catches
`l` and nothing else, a finaliser frame stops a raise and holds its finaliser, the driver catches
nothing and stops nothing, and `catches`, `unwindClear` and `fins` are computed frame by frame.
Forwarding is structural.  The instance's other frames are its own (ours: Core's, §4.1). -/
def KontLaws (S) : Prop :=
  (∀ t, S.plug S.hole t = t) ∧ (∀ K₁ K₂ t, S.plug (S.kcomp K₁ K₂) t = S.plug K₁ (S.plug K₂ t)) ∧
  (∀ N M, S.plug (S.bindF N) M = S.bind M N) ∧
  (∀ l H t, S.plug (S.handleF l H) t = S.handle l H t) ∧ (∀ N D M, S.plug (S.thenF N D) M = S.thenT M N D) ∧
  (∀ M, S.plug S.driveF M = S.drive M) ∧
  (∀ m, S.catches S.hole m = false) ∧ (∀ N m, S.catches (S.bindF N) m = false) ∧
  (∀ V m, S.catches (S.appF V) m = false) ∧ (∀ l H m, S.catches (S.handleF l H) m = decide (m = l)) ∧
  (∀ N D m, S.catches (S.thenF N D) m = false) ∧ (∀ m, S.catches S.driveF m = false) ∧
  (∀ K₁ K₂ m, S.catches (S.kcomp K₁ K₂) m = (S.catches K₁ m || S.catches K₂ m)) ∧
  S.unwindClear S.hole ∧ (∀ N, S.unwindClear (S.bindF N)) ∧ (∀ V, S.unwindClear (S.appF V)) ∧
  (∀ l H, S.unwindClear (S.handleF l H)) ∧ (∀ N D, ¬ S.unwindClear (S.thenF N D)) ∧ S.unwindClear S.driveF ∧
  (∀ K₁ K₂, S.unwindClear (S.kcomp K₁ K₂) ↔ S.unwindClear K₁ ∧ S.unwindClear K₂) ∧
  S.fins S.hole = [] ∧ (∀ N, S.fins (S.bindF N) = []) ∧ (∀ V, S.fins (S.appF V) = []) ∧
  (∀ l H, S.fins (S.handleF l H) = []) ∧ (∀ N D, S.fins (S.thenF N D) = [D]) ∧ S.fins S.driveF = [] ∧
  (∀ K₁ K₂, S.fins (S.kcomp K₁ K₂) = S.fins K₂ ++ S.fins K₁) ∧ (∀ K, S.unwindClear K → S.fins K = [])

/-- An application reaches its function's evaluation position by administrative steps: `M V` is
`□ V` around `M` after them.  (Our instance's `[app]` takes a variable argument, so its `M V` binds
`V` first; §4.1.) -/
def AppLaw (S) : Prop := ∀ c M V, S.PureSteps (S.setT c (S.app M V)) (S.setT c (S.plug (S.appF V) M))

/-- A step of a term is its step in every context (Yoshioka E_Eval), the driver's frame included.
The driver's own steps are excepted: they act on a whole program only. -/
def Congr (S) : Prop :=
  ∀ c t ev c' K, ev ≠ .top → S.step (S.setT c t) ev c' →
    S.step (S.setT c (S.plug K t)) ev (S.setT c' (S.plug K (S.term c')))

/-- The machine never answers an operation: io comes from the runner only, and an operation no
handler catches takes no step. -/
def NoIO (S) : Prop := ∀ c l i v w c', ¬ S.step c (.io l i v w) c'
def OpStuck (S) : Prop :=
  (∀ c K l i v, S.term c = S.plug K (S.perform l i v) → S.catches K l = false → ∀ ev c', ¬ S.step c ev c') ∧
  (∀ c K l i v, S.term c = S.plug K (S.raise l i v) → S.catches K l = false → S.unwindClear K → ∀ ev c', ¬ S.step c ev c')

/-- Answers are told apart: `ret` and the data formers are injective, `inl` and `inr` disjoint,
and a term stopped at an operation, or being driven, is no answer. -/
def DataInj (S) : Prop :=
  Function.Injective S.ret ∧ (∀ a b a' b', S.pair a b = S.pair a' b' → a = a' ∧ b = b') ∧
  Function.Injective S.inl ∧ Function.Injective S.inr ∧ (∀ a b, S.inl a ≠ S.inr b) ∧
  (∀ a b, S.unitV ≠ S.pair a b) ∧ (∀ a, S.unitV ≠ S.inl a ∧ S.unitV ≠ S.inr a) ∧
  (∀ a b c, S.pair a b ≠ S.inl c ∧ S.pair a b ≠ S.inr c) ∧
  (∀ K l i v w, S.plug K (S.perform l i v) ≠ S.ret w ∧ S.plug K (S.raise l i v) ≠ S.ret w) ∧
  (∀ M w, S.drive M ≠ S.ret w)

/-- **A loop value's observations** (decision 35; SPEC §14: "`next` in the first loop observes it").
`next (unfold f g s)` runs `f s` under a context that catches nothing and holds no finaliser, and
answers `inl a` when `f s` does, and `inr (unfold f g s')` when `f s` answers `inr s'`.  `close` runs
`g s` the same way and answers what it answers. -/
def LoopLaws (S) : Prop :=
  (∀ c f g s, ∃ K', (∀ m, S.catches K' m = false) ∧ S.unwindClear K' ∧
     S.PureSteps (S.setT c (S.next (S.unfold f g s))) (S.setT c (S.plug K' (S.app (S.force f) s))) ∧
     (∀ a, S.PureSteps (S.setT c (S.plug K' (S.ret (S.inl a)))) (S.setT c (S.ret (S.inl a)))) ∧
     (∀ s', S.PureSteps (S.setT c (S.plug K' (S.ret (S.inr s')))) (S.setT c (S.ret (S.inr (S.unfold f g s')))))) ∧
  (∀ c f g s, ∃ K', (∀ m, S.catches K' m = false) ∧ S.unwindClear K' ∧
     S.PureSteps (S.setT c (S.close (S.unfold f g s))) (S.setT c (S.plug K' (S.app (S.force g) s))) ∧
     ∀ v, S.PureSteps (S.setT c (S.plug K' (S.ret v))) (S.setT c (S.ret v)))

/-- **The driver** ("the runtime drives `main` forever"): `drive M` runs `M` (that is `Congr` at
`driveF`); at `inr l` it drives `next l`, at `inl a` it answers `a`.  Each of those transitions is
one `top` step and the only step there, and the driver's are the only `top` steps. -/
def DriveLaws (S) : Prop :=
  (∀ c l ev c', S.term c = S.drive (S.ret (S.inr l)) → (S.step c ev c' ↔ ev = .top ∧ c' = S.setT c (S.drive (S.next l)))) ∧
  (∀ c a ev c', S.term c = S.drive (S.ret (S.inl a)) → (S.step c ev c' ↔ ev = .top ∧ c' = S.setT c (S.ret a))) ∧
  (∀ c c', S.step c .top c' → ∃ v, S.term c = S.drive (S.ret v))

def MachShape (S) : Prop :=
  ConfLaws S ∧ KontLaws S ∧ AppLaw S ∧ Congr S ∧ NoIO S ∧ OpStuck S ∧ DataInj S ∧ LoopLaws S ∧ DriveLaws S

/-- **The let law** (CBPV's `[let]` at a returned value), in every context: a closed value typed at
`A` and a body typed with `A` in front give the let. -/
def LetLaw (S) : Prop :=
  ∀ Γ V A N C, S.derV [] V A → S.der (A :: Γ) N C → S.der Γ (S.bind (S.ret V) N) C
```

- **Evaluation contexts.** The handler laws, `OpStuck` and `StopsIn` hold in every context, binds
  and applications included, as Yoshioka's `E_Eval` has them: `bind (perform l i v) N` is
  `plug (bindF N) (perform l i v)`, so it is stuck when no handler of `l` encloses it.
- **`appF` up to administrative steps.** `AppLaw` asks that `M V` *reach* `plug (appF V) M`, not that
  it be equal to it. Our instance's `[app]` types `M x` at a variable `x`, so its `M V` is `V to x.
  M x` (§4.1); one β-step reaches the frame `□ V`.
- **The formers are constructors** (`DataInj`): answers are told apart, and an operation or a
  driven term is no answer. **`OpStuck`** says that the machine does not answer operations, the
  platform does; that is what gives effect safety (S3) its content (`not_der_unhandled`, §6.1).
- **An answer is a returned value at which nothing steps** (`IsVal`). The driver acts on a value at
  the top, with `top` steps, and those are the only steps `Congr` excepts.
- **Inside a driven program.** `drive M` is `plug driveF M`, so a driven program is a term in a
  context like any other: a non-`top` step of `M` is a step of `drive M` (`Congr` at `driveF`), the
  runner answers an operation that a driven loop performs (`RStep.io` at `kcomp driveF K`), a
  driven program stopped at an operation of its row is `StopsIn` that row, and S4–S6 hold in a
  driven loop's contexts. The library's runs have this shape: `RStep.run` lifts every platform step
  into the drive phase (`Targets/Defs/Runs.lean`).
- **Plugging need not be injective.** At our instance a drive is a property of the whole
  configuration (`RStep`'s phase), so `drive (drive M)` is `drive M`, and a drive under another
  frame is dropped (§4.1). No property reads injectivity, so `KontLaws` does not ask it.
- **The let law and substitution.** The schemas of §1.6 type a use with the higher-order value's
  type in the context, and `LetLaw` ties that to the program that binds the value
  (`not_noColouring_of_monoCallback` uses it). A typing law for **value substitution** is not added:
  it would need a substitution operation, and no property needs one. Where the properties need a
  β-behaviour, they state it per program (`CallsThrough`) or as a law of the former (`LoopLaws`).

### 1.5 The soundness properties

**S1: the row algebra (T0).** The rows form a safe effect algebra over one signature object, and
typing is closed under its subeffecting.

```lean
/-- **One signature object**: `(l)↑` admits exactly `sig l`'s operations, `⊙` unions, `0` admits
nothing, `∼` preserves what is admitted, substitution adds the substituted row's operations and
nothing else, and no signature is empty.  Kammar: "annotation effects can be identified with the
effect operations". -/
def RowSig (S) : Prop :=
  (∀ l m i, S.has (S.EA.lift l) m i ↔ m = l ∧ i < (S.sig l).length) ∧ (∀ l i, ¬ S.has S.EA.unit l i) ∧
  (∀ ε₁ ε₂ ε l i, S.EA.comp ε₁ ε₂ = some ε → (S.has ε l i ↔ S.has ε₁ l i ∨ S.has ε₂ l i)) ∧
  (∀ ε₁ ε₂ l i, S.EA.eqv ε₁ ε₂ → (S.has ε₁ l i ↔ S.has ε₂ l i)) ∧
  (∀ α ε' ε l i, S.has ε l i → S.has (S.EA.subst α ε' ε) l i) ∧
  (∀ α ε' ε l i, S.has (S.EA.subst α ε' ε) l i → S.has ε l i ∨ S.has ε' l i) ∧ (∀ l, S.sig l ≠ [])

/-- Subeffecting is a typing rule: what the algebra's `<` relates, the typing relates.  This is what
gives Def. 5.1 (1) its teeth: an algebra with `(l)↑ < 0` would type an unhandled operation at `0`. -/
def SubClosed (S) : Prop :=
  ∀ Γ e ε₁ ε₂ A, S.der Γ e (S.F ε₁ A) → S.EA.Sub ε₁ ε₂ → S.der Γ e (S.F ε₂ A)

def RowAlgebra (S) : Prop := S.EA.Laws ∧ S.EA.Safe ∧ RowSig S ∧ SubClosed S
```

Yoshioka's Def. 7.1 (the safety condition for lift coercions, that is, masking) and Def. 7.6 (the
safety condition for type erasure) apply only to an instance with masking, or with labels whose
type arguments dispatch reads. Ours has no masking, and its labels are names without type arguments,
so erasing rows changes no dispatch. Rows are sums of signatures, since
`(l)↑` is a whole signature and `⊙` is union. A part of a signature is a row only where SPEC §19
builds one (`Σ^abort`, the finaliser row), so operations enter a row through `has`.

**S2: safety, and termination where claimed.** Bauer–Pretnar Thm 4.1 and Cor. 4.2; Affect Thm 2.1;
[CONF] 415:18.

```lean
/-- Every program at a data answer on the pure row is claimed to terminate (decision 35: "code
without [div] is total").  The instance may claim more: ours claims every `F_Σ A` at a data `A`. -/
def DataDiv (S) : Prop := ∀ A, S.DataTy A → S.DivFree (S.F S.EA.unit A)

/-- Under every platform that keeps its protocol, at every row it answers:
* a program at a data answer has every run never stuck, terminates where the type is div-free, and
  every complete run ends at a value of the answer type (Bauer–Pretnar Cor. 4.2: it "returns a value
  of type A");
* a driven program whose current step answers `A ⊕ L`, `A` data, has every run never stuck, and every
  complete run ends at a value of `A`. -/
def Safety (S) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ ε, S.Answers R ε →
    (∀ e A, S.DataTy A → S.der [] e (S.F ε A) →
       S.SafeRuns R e ∧ (S.DivFree (S.F ε A) → S.Terminates R e) ∧
       ∀ q, S.CompleteFrom R (S.rinit R e) q → ∃ v, S.term (q.last _).1 = S.ret v ∧ S.DataVal A v) ∧
    (∀ M A L, S.DataTy A → S.der [] (S.drive M) (S.F ε (S.Sum A L)) →
       S.SafeRuns R (S.drive M) ∧
       ∀ q, S.CompleteFrom R (S.rinit R (S.drive M)) q → ∃ a, S.term (q.last _).1 = S.ret a ∧ S.DataVal A a)
```

- Main's row is the platform's (OQ-51 (a)). `R.Respects` leaves only linear data operations in a row
  the runner answers, so an error must be handled before the top.
- A driven program is never claimed to terminate, and S2 asks that every run of it is safe on every
  finite prefix; `SafeRuns` over an infinite run is exactly that. Its type is its current step's,
  `A ⊕ L` with `L` the instance's loop type, which is not data, so `DataDiv` claims nothing of it.
- S2 covers data answers and driven programs. That is the scope the library proves (its `Soundness`
  holds `SoundRetAt` at data answers and `SoundDriveAt` at loops, AGREE 7). Progress at every answer
  type, with no platform, is S3.
- **Termination is required at the pure row only, and that is weaker than decision 35.** `DataDiv`
  claims termination only of data answers at the pure row. So an instance in which a computation at
  a non-empty row may diverge silently at a data answer, as in ML, meets S2 and E3, and decision
  35's "code without [div] is total" is enforced by done only at the pure row. This is deliberate:
  it keeps §7 Q3 open (divergence as a row effect would make `F_{div} bool` not div-free). If Q3 is
  answered "codata", as decision 35 is built, `DataDiv` becomes `∀ ε A, S.DataTy A → S.DivFree
  (S.F ε A)`, which our instance already claims (§4.1's `DivFree`).
- **The answer's type, beyond data.** The answer clause is stated at data answers only. At other
  answer types our instance's final value may be a location, which its typing types semantically
  and not syntactically, so `derV [] v A` at a value would fail at our instance; it is not added
  to S3 either.

**S3: effect safety.** Yoshioka Lemma 5.7, Thm 5.8; Bauer–Pretnar Cor. 4.2; Tang Thm 3.2.

```lean
def StopsIn (S) (ε) (c : S.Conf) : Prop :=
  ∃ K l i v o, (S.sig l)[i]? = some o ∧ S.has ε l i ∧ S.catches K l = false ∧
    ((S.term c = S.plug K (S.perform l i v) ∧ o.cls ≠ .abortive) ∨
     (S.term c = S.plug K (S.raise l i v) ∧ o.cls = .abortive ∧ S.unwindClear K))

def EffSafe (S) : Prop :=
  ∀ e ε A, S.der [] e (S.F ε A) → ∀ c, S.Reach (S.init e) c →
    S.IsVal c ∨ (∃ ev c', S.step c ev c') ∨ S.StopsIn ε c
```

At `ε = 0`, `RowSig` makes `StopsIn 0` empty, so no operation goes unhandled. `K` ranges over every
context, binds and applications included, so an operation inside `M to x. N` is covered, and the
driver's frame included, so an operation that a driven loop performs is covered too.

**S4: the handler laws, unary.** These are Plotkin–Pretnar's equations as reductions, in every
context `K₀`, binds, applications and the driver's frame included. Two configurations are related
when they have a common reduct by steps that change no store (`PureJoin`). So an instance whose encodings differ by
administrative steps still meets them.

```lean
def HandlerSem (S) : Prop :=
  -- return: "return V handled with … to x : A. N(x) = N(V)"
  (∀ c K₀ l r cs v, S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.ret v)) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force r) v)))) ∧
  -- a resuming operation caught: the clause gets the argument and κ
  (∀ c K₀ l r cs K i v o cl, S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v))) →
     S.catches K l = false → (S.sig l)[i]? = some o → o.cls ≠ .abortive → cs[i]? = some cl →
     S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force cl) (S.pair v (S.capture l (S.hnd r cs) K)))))) ∧
  -- an abortive operation caught: the clause gets the argument only, and κ is never reified
  (∀ c K₀ l r cs K i v o cl, S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.raise l i v))) →
     S.catches K l = false → S.unwindClear K → (S.sig l)[i]? = some o → o.cls = .abortive →
     cs[i]? = some cl → S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force cl) v)))) ∧
  -- deep resume: resuming κ runs the frozen context under the same handler again
  (∀ c K₀ l H K w, S.term c = S.plug K₀ (S.resume (S.capture l H K) w) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.handle l H (S.plug K (S.ret w)))))) ∧
  -- cancel starts κ's cancel run, in the canceller's context
  (∀ c K₀ l H K, S.term c = S.plug K₀ (S.cancel (S.capture l H K)) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.cancelOf l H K)))) ∧
  -- a finaliser frame whose body returned continues with `N`
  (∀ c K₀ v N D, S.term c = S.plug K₀ (S.thenT (S.ret v) N D) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.bind (S.ret v) N)))) ∧
  -- an unwind that reaches a finaliser frame fires the finaliser and runs it where the frame was,
  -- inside a context `Kp` of the instance's that catches nothing; once it returns `()`, the raise
  -- goes on (SPEC [finalise])
  (∀ c K₀ N D K m j w, S.term c = S.plug K₀ (S.thenT (S.plug K (S.raise m j w)) N D) →
     S.catches K m = false → S.unwindClear K →
     ∃ c₁ Kp, S.step c (.fire D) c₁ ∧ (∀ m', S.catches Kp m' = false) ∧ S.unwindClear Kp ∧
       S.PureSteps c₁ (S.setT c (S.plug (S.kcomp K₀ Kp) D)) ∧
       S.PureSteps (S.setT c (S.plug (S.kcomp K₀ Kp) (S.ret S.unitV))) (S.setT c (S.plug K₀ (S.raise m j w))))
```

**Where a finaliser runs.** `Kp` is any context of the instance's, not one of the five named frames.
At ours it is Core's `seq` frame: `[finalise]` steps the frame to `D (); raise p`, so `D` runs under
`□; raise p`, which has no handler, `ubind` or `cfin` frame (§4.1).

**The laws are joins.** They say what handling reduces to, up to steps that change no store. They do
not ask the machine to be deterministic; ours is, up to the choice of a fresh location (Core's
`head_det_eff`), and the Instance uses that to compute runs (§6.1).

**Forwarding** is structural. `KontLaws` says that a handler frame of `l` catches only `l`, so an
operation of another label passes it. Deep resume then reinstalls every frame of `K`, the passed
handler included.

**Deep handling** is the deep-resume conjunct (Yoshioka's "v_cont = λz.handle_l S E[z] with h"). It
is checked observably by E4.

**Handler correctness.** With no equations in signatures (OQ-22), Plotkin–Pretnar's correctness
condition (Def. 4.5) holds of every handler: "If the effect theory is empty, then any handler is
correct". Handler correctness is then exactly these equations. The semantic form, the `[handle]`
rule sound in a logical relation, belongs to the proof device (§3.7, `HandleCompat`), not to A.

**S4 excludes OQ-50 (b), and this design says so.** OQ-50 (b) is "the TR's one-shot-cell machine
change": a continuation as a heap cell, allocated at the catch and freed by its use. S4 excludes it
twice over:

- `capture l H K` is a value computed from the handler and the context, with no store; under (b)
  the clause would get a fresh location;
- the catch, deep-resume and cancel laws relate configurations by `PureJoin`, steps that change no
  store; under (b) the catch allocates and the resume and cancel free.

S4 states Core's continuation as built (`kappa`, a value). Admitting (b) would need A to carry a
continuation's cell: `capture` as a relation on configurations, and the three laws up to steps that
touch only that cell. This design does not do that, and asks the user (§7 Q9).

**S5: cancellation, as built** (SPEC §19; decision 62). This is our semantics, not a theorem of the
literature. SPEC §19 states what is built:

- "A cancel is not interceptable. The frames of the cancelled region … are being torn down: nothing
  in the region resumes, and its handlers are dying, so they catch nothing";
- "An error raised by a finaliser during a cancel is re-raised at the canceller, after every frame
  of the region has finalised";
- "Several failures: the first is re-raised, and the rest are suppressed";
- "An error of a name in `N` … is suppressed";
- "Ordinary unwinding … a finaliser's raise supersedes the pending one and is caught by the live
  handlers around the finaliser".

The traces below state each of these over A's steps. They are v1's §1.4 A-CAN with five changes:

1. A finaliser is a computation `D : Term`.
2. A fire step may be followed by pure administrative steps before `D` runs.
3. Catching ends an unwind trace, and no event marks it, because S4's abortive law covers what
   follows.
4. The traces are quantified at every row the runner answers.
5. The context in which a finaliser runs alone (`Kf` in a cancel, `Kp` in an unwind) is any
   context of the instance's. At ours a cancel runs `D` under Core's `cfin` frame, inside the
   canceller's `ccatch`, and an unwind runs it under a `seq` frame (§4.1); neither is a named frame
   of A's.

```lean
abbrev Err (S) := Option (S.EA.Lab × ℕ × S.Val)

/-- [cfin-raise]: "err′ = err if err ≠ none; none if m ∈ N; (m, v) otherwise". -/
noncomputable def keep (N : S.EA.Lab → Prop) : S.Err → S.Err → S.Err
  | some e, _ => some e
  | none, none => none
  | none, some (m, j, w) => by classical exact if N m then none else some (m, j, w)

/-- The region a cancel of `capture l H K` tears down: `l` and every label a handler frame of `K`
catches. -/
def Region (l : S.EA.Lab) (K : S.Kont) (m : S.EA.Lab) : Prop := m = l ∨ S.catches K m = true

/-- The canceller is answered ([cancel], [cancel-raise]): `()`, or the kept error raised at it. -/
def Answered (K₀ : S.Kont) : S.Err → S.Term → Prop
  | none, t => t = S.plug K₀ (S.ret S.unitV)
  | some (m, j, w), t => t = S.plug K₀ (S.raise m j w)

/-- Along `q` from `c`, the term inside the context `Kf` runs alone. -/
inductive Alone (R) (Kf : S.Kont) : S.RConf R → List (S.Ev × S.RConf R) → S.RConf R → Prop
  | nil {c} : Alone c [] c
  | cons {c ev c' t t' q c''} : S.term c.1 = S.plug Kf t → S.term c'.1 = S.plug Kf t' →
      S.RStep R c ev c' → S.RStep R (S.setR c t) ev (S.setR c' t') → Alone c' q c'' → Alone c ((ev, c') :: q) c''

/-- At `c` the term inside `Kf` has ended: it returned, or a raise escaped it. -/
def Ended (Kf : S.Kont) (c : S.RConf R) : S.Err → Prop
  | none => ∃ v, S.term c.1 = S.plug Kf (S.ret v)
  | some (m, j, w) => ∃ K, S.term c.1 = S.plug Kf (S.plug K (S.raise m j w)) ∧ S.catches K m = false ∧ S.unwindClear K

mutual
/-- **A cancel trace**: `fs` are the frozen finalisers not yet fired, and `err` is the error kept
so far.  Each finaliser fires, innermost first, then runs alone to its end, and its end updates the
kept error.  Last, the canceller is answered.  A trace may stop anywhere, and after the answer
anything may follow. -/
inductive CancelTrace (R) (N : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.RConf R → List S.Term → S.Err → List (S.Ev × S.RConf R) → Prop
  | stop {c fs err} : CancelTrace c fs err []
  | answer {c c' err q} : S.RStep R c .tau c' → S.Answered K₀ err (S.term c'.1) → CancelTrace c [] err ((.tau, c') :: q)
  | fire {c c₁ c₂ D fs err Kf q₀ q} : S.RStep R c (.fire D) c₁ → S.PurePath c₁ q₀ c₂ →
      S.term c₂.1 = S.plug Kf D → FinTrace R N K₀ Kf c₂ fs err q → CancelTrace c (D :: fs) err ((.fire D, c₁) :: q₀ ++ q)
inductive FinTrace (R) (N : S.EA.Lab → Prop) (K₀ Kf : S.Kont) :
    S.RConf R → List S.Term → S.Err → List (S.Ev × S.RConf R) → Prop
  | running {c fs err q c'} : S.Alone R Kf c q c' → FinTrace c fs err q
  | ended {c fs err q c' r c'' q'} : S.Alone R Kf c q c' → S.Ended Kf c' r →
      S.RStep R c' (.finEnd r) c'' → CancelTrace R N K₀ c'' fs (keep N err r) q' →
      FinTrace c fs err (q ++ (.finEnd r, c'') :: q')
end

/-- **Not interceptable, in order, with the error policy**: every run of a typed program from the
start of a cancel of `capture l H K` follows a cancel trace of `fins K` with nothing kept. -/
def NoIntercept (S) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ c₀ c K₀ l H K q, S.RReach R (S.rinit R e) c₀ → S.term c₀.1 = S.plug K₀ (S.cancel (S.capture l H K)) →
      S.PureSteps c₀.1 c.1 → c.2 = c₀.2 → S.term c.1 = S.plug K₀ (S.cancelOf l H K) →
      S.RPath R c q → S.CancelTrace R (S.Region l K) K₀ c (S.fins K) none q

/-- The frames of `K` that stop a raise are handler frames and finaliser frames. -/
inductive Std : S.Kont → Prop
  | clear {K} : S.unwindClear K → Std K
  | frame {K₁ K₂ F} : S.unwindClear K₁ → ((∃ l H, F = S.handleF l H) ∨ (∃ N D, F = S.thenF N D)) →
      Std K₂ → Std (S.kcomp K₂ (S.kcomp F K₁))

mutual
/-- **An unwind trace**: a raise is pending under `K`, inside the fixed context `K₀`, and the first
frame of `K` that stops it decides.  If that frame is a handler of its label, the trace ends there;
S4's abortive law says what follows.  If it is a finaliser frame, its finaliser fires and runs
alone.  If the finaliser returns, the pending raise goes on through the rest of `K`.  If a raise
escapes the finaliser, that raise supersedes the pending one.  Once the pending raise has left `K`,
the trace is over. -/
inductive UnwindTrace (R) (K₀ : S.Kont) : S.RConf R → S.Kont → List (S.Ev × S.RConf R) → Prop
  | stop {c K} : UnwindTrace c K []
  | out {c K m j w q} : S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      S.unwindClear K → UnwindTrace c K q
  | caught {c K K₁ K₂ H m j w q} : K = S.kcomp K₂ (S.kcomp (S.handleF m H) K₁) → S.catches K₁ m = false →
      S.unwindClear K₁ → S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → UnwindTrace c K q
  | fire {c c₁ c₂ K K₁ K₂ N D Kp m j w q₀ q} : K = S.kcomp K₂ (S.kcomp (S.thenF N D) K₁) →
      S.catches K₁ m = false → S.unwindClear K₁ → S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) →
      S.RStep R c (.fire D) c₁ → S.PurePath c₁ q₀ c₂ → (∀ m', S.catches Kp m' = false) → S.unwindClear Kp →
      S.term c₂.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) D → PendTrace R K₀ K₂ Kp (m, j, w) c₂ q →
      UnwindTrace c K ((.fire D, c₁) :: q₀ ++ q)
inductive PendTrace (R) (K₀ K₂ Kp : S.Kont) (p : S.EA.Lab × ℕ × S.Val) :
    S.RConf R → List (S.Ev × S.RConf R) → Prop
  | running {c q c'} : S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' → PendTrace c q
  | returned {c q c' q₁ c'' q₂} : S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.Ended (S.kcomp (S.kcomp K₀ K₂) Kp) c' none → S.PurePath c' q₁ c'' →
      S.term c''.1 = S.plug K₀ (S.plug K₂ (S.raise p.1 p.2.1 p.2.2)) → UnwindTrace R K₀ c'' K₂ q₂ →
      PendTrace c (q ++ q₁ ++ q₂)
  | superseded {c q c' K' m' j' w' q₂} : S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.term c'.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) (S.plug K' (S.raise m' j' w')) →
      S.catches K' m' = false → S.unwindClear K' → UnwindTrace R K₀ c' (S.kcomp K₂ (S.kcomp Kp K')) q₂ →
      PendTrace c (q ++ q₂)
end

def UnwindOrder (S) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ c K₀ K m j w q, S.RReach R (S.rinit R e) c → S.Std K →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false → S.RPath R c q →
      S.UnwindTrace R K₀ c K q

def Cancellation (S) : Prop := NoIntercept S ∧ UnwindOrder S
```

What each piece carries:

- **The order.** `CancelTrace` fires `fins K` innermost first, each once. Its only `answer` case is
  at `fs = []`, so a run that reaches the canceller's answer has fired every finaliser.
- **Not interceptable.** Between the start of the cancel and its answer, each step is one of: a
  fire, a step of the running finaliser alone, a `finEnd`, or the answer. No other code of the
  region runs. The trace is bounded by the answer: after it, anything may follow.
- **The error policy.** `Region l K` reads the labels the region's handlers catch. `keep` is
  [cfin-raise], and `Answered` is [cancel] and [cancel-raise].
- **The unwind.** It reads `catches K m = false`, which answers the library's minor finding on
  `UnwindOrder`. Handler frames of other labels may stand in `K`.
- **Over runs under a runner, at every row it answers.** So programs at the platform's row are
  covered (the library's minor finding on `CancelOrder`).
- **Inside driven programs.** `K₀` may hold the driver's frame, so a cancel or an unwind inside a
  driven loop follows the same traces: E10's cancel of the suspended wait, under the driver, is
  covered by `NoIntercept`.

**The traces are reached, at every instance.** `RunsTo` observes `fire` and `finEnd` events (§1.3),
and E7, E8 and E9c (§1.6) state the exact sequence of them. So every instance that meets done runs
those programs through a cancel or an unwind that fires each finaliser once, in the stated order,
and with the stated ends. At our instance their runs are computed (§6.3).

**S6: the linear and affine use of continuations (the REJECT side, universally).** Tang et al.
Thm 3.6 ("tagged linear values are not duplicated or discarded during evaluation"); Affect's
one-shot safety ("continuations corresponding to one-shot effects are resumed at most once"); survey
A6 for a linear core ("every continuation that captures a must-use value is resumed or explicitly
discontinued exactly once"). On every run of a typed program, no continuation is used more often
than it was caught, and a continuation caught at a linear operation is never cancelled. On every
complete run **at a data answer**, each is used exactly as often as it was caught. The observation
is A's own, read off the terms of the run.

The exactly-once clause has S2's scope, data answers. A data answer holds no continuation, so a
continuation caught and not used has been dropped. At another answer type a complete run may end
with a continuation inside its value: a handler may answer a closure over κ, as E1′'s `sched` does,
and `let f = hof in sched (f async)` completes at `U(1 → F 0 bool)` with κ caught once and used
never. Tang et al.'s Thm 3.6 allows exactly that: linear values are preserved, "ℒ(M) ∪ S = ℒ(N) ∪ T",
not consumed.

```lean
/-- Step `j` of the path `q` from `c₀` catches `κ` at an operation of class `k`: the configuration
before it is stopped at a resuming operation that a handler catches, and `κ` is the continuation the
catch hands its clause. -/
def CatchAt (c₀ : S.RConf R) (q) (j : ℕ) (κ : S.Val) (k : OpClass) : Prop :=
  j < q.length ∧ ∃ K₀ l r cs K i v o, S.term (q.cfg c₀ j).1 = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v))) ∧
    S.catches K l = false ∧ (S.sig l)[i]? = some o ∧ o.cls = k ∧ k ≠ .abortive ∧ κ = S.capture l (S.hnd r cs) K
/-- Step `j` resumes `κ`, or cancels it. -/
def ResumeAt (c₀ : S.RConf R) (q) (j) (κ) : Prop := j < q.length ∧ ∃ K₀ w, S.term (q.cfg c₀ j).1 = S.plug K₀ (S.resume κ w)
def CancelAt (c₀ : S.RConf R) (q) (j) (κ) : Prop := j < q.length ∧ ∃ K₀, S.term (q.cfg c₀ j).1 = S.plug K₀ (S.cancel κ)
-- the counts along `q` from `c₀`, each `(List.range q.length).countP …` of the above:
-- `caughtLin c₀ q κ`, `caughtAff c₀ q κ`, `resumes c₀ q κ`, `cancels c₀ q κ`; `uses := resumes + cancels`,
-- `caught := caughtLin + caughtAff`

def ContUse (S) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ q, S.RPath R (S.rinit R e) q → ∀ κ, let c₀ := S.rinit R e
      S.uses c₀ q κ ≤ S.caught c₀ q κ ∧ S.cancels c₀ q κ ≤ S.caughtAff c₀ q κ ∧
      (S.DataTy A → S.IsVal (q.last c₀).1 → S.uses c₀ q κ = S.caught c₀ q κ)
```

- **No forget, no second use, no cancel of a linear κ, no use after cancel.** Each is a run on which
  the counts break: a forgotten κ is caught and never used on a complete run at a data answer; a
  second use, or a use after a cancel, uses κ more often than it was caught; a cancel of a linear κ
  cancels one that no affine catch made. The concrete rejected programs R1–R4 below, each at
  `F 0 bool`, are the witnesses that S6 bites: at our machine each has a complete run that breaks
  the counts, so no typing system over our machine that types one of them meets S6 (§6.1,
  `not_contUse_of_der_R1` … `_R4`).
- **Counts are per continuation value.** Two catches that hand out equal values are counted
  together; no run's answer or trace tells equal values apart either.
- **OQ-50.** OQ-50 asks how "κ used exactly once" is observed and proved: syntactic subject
  reduction (a), the one-shot-cell machine (b), or stating only the resource half (c), the spec's
  default. Done now states the use count, so done no longer settles for (c), and S4 excludes (b)
  (above). Its proof route at our instance is (a)'s subject reduction, or the logical relation with
  a ghost token per continuation. Which of them is the builder's; that done states S6 at all is
  §7 Q9.

The rejected programs, for the witnesses:

```lean
def sigWait : List (OpSig S.Ty) := [⟨S.UnitT, S.UnitT, .affine⟩]    -- an affine, resuming operation
def sigLin  : List (OpSig S.Ty) := [⟨S.UnitT, S.UnitT, .linear⟩]
/-- `op (v, k) ⇒ return ff`: κ dropped. -/
def dropCl : S.Val := S.lam (S.split (S.var 0) (S.ret S.ff))
/-- `op (v, k) ⇒ resume k () to _. resume k ()`: κ used twice. -/
def twiceCl : S.Val := S.lam (S.split (S.var 0) (S.bind (S.resume (S.var 0) S.unitV) (S.resume (S.var 1) S.unitV)))
/-- `op (v, k) ⇒ cancel k to _. return ff`. -/
def cancelCl : S.Val := S.lam (S.split (S.var 0) (S.bind (S.cancel (S.var 0)) (S.ret S.ff)))
/-- `op (v, k) ⇒ cancel k to _. resume k ()`. -/
def cancelResumeCl : S.Val := S.lam (S.split (S.var 0) (S.bind (S.cancel (S.var 0)) (S.resume (S.var 1) S.unitV)))
/-- `handle l {return x ⇒ x; op (v, k) ⇒ cl} (op () to _. return tt)`. -/
def withCl (l : S.EA.Lab) (cl : S.Val) : S.Term :=
  S.handle l (S.hnd (S.lam (S.ret (S.var 0))) [cl]) (S.bind (S.perform l 0 S.unitV) (S.ret S.tt))
-- R1: `withCl l dropCl` at `l` affine or linear; R2: `withCl l twiceCl`; R3: `withCl ll cancelCl` at
-- `ll` linear; R4: `withCl lw cancelResumeCl` at `lw` affine
```

R1 to R4 run safely when κ holds nothing, so S1–S5 do not exclude them; S6 does. In the composite,
where κ holds resources, B's guarantees would also exclude R1 (a leak) and R2 and R4 (a use of what
the first use or the cancel released) (§3.4).

**The (S) properties together.**

```lean
def SProps (S) : Prop :=
  MachShape S ∧ LetLaw S ∧ RowAlgebra S ∧ DataDiv S ∧ Safety S ∧ EffSafe S ∧ HandlerSem S ∧
  Cancellation S ∧ ContUse S
```

### 1.6 The expressiveness properties

Each (E) property names its labels and signatures, its runner, its programs as A-terms, the types
the programs must have, and the behaviour they must show. Where a decided feature is needed, the
property also states a **schema** (§1.3: `PolyUse`, `PolyUseLacks`, `PolyUseOpen`, `CallsThrough`)
over every row and every closed callback body the instance types.

**Signatures and runners used below.**

| name | signature | class | role |
|---|---|---|---|
| `sigExn` | `1 ↠ 0` | abortive | `raise`, an error (decision E1: "error is a control flow effect full stop") |
| `sigWait` | `1 ↠ 1` | affine | a suspension: async wait, or a timer's target |
| `sigYield` | `bool ↠ 1` | affine | a generator's yield |
| `sigLog` | `bool ↠ 1` | linear | an answering operation, resumed in tail position |
| `sigTick` | `1 ↠ 1` | linear | a platform operation, observed in the io trace |
| `sigKube` | `1 ↠ bool` | linear | a platform API call that may fail |

- `Rtick lt` answers `lt.0` with `()`. `Rtl lt llog` answers `lt.0` and `llog.0` with `()`.
- `Rrec lk llog` answers `lk.0` alternately `ff` then `tt` (its state is a `Bool`), and answers
  `llog.0` with `()`. The runners respect their protocol (§6.1).
- `tickEv lt := .io lt 0 unitV unitV`; `logEv llog := .io llog 0 tt unitV`.

**Shared clauses and handlers** (A-level definitions):

```lean
def toResult (le : S.EA.Lab) (M : S.Term) : S.Term :=     -- handle le {return x ⇒ inl x; raise _ ⇒ inr ()} M
  S.handle le (S.hnd (S.lam (S.ret (S.inl (S.var 0)))) [S.lam (S.ret (S.inr S.unitV))]) M
def resumeCl : S.Val := S.lam (S.split (S.var 0) (S.resume (S.var 0) S.unitV))
def resumer (l : S.EA.Lab) (M : S.Term) : S.Term :=       -- handle l {return x ⇒ x; op (_, k) ⇒ resume k ()} M
  S.handle l (S.hnd (S.lam (S.ret (S.var 0))) [resumeCl]) M
def timeoutCl : S.Val := S.lam (S.split (S.var 0) (S.bind (S.cancel (S.var 0)) (S.ret (S.inr S.unitV))))
def timeoutH (lw : S.EA.Lab) (M : S.Term) : S.Term :=     -- handle lw {return x ⇒ inl x; wait (_, k) ⇒ cancel k; inr ()} M
  S.handle lw (S.hnd (S.lam (S.ret (S.inl (S.var 0)))) [timeoutCl]) M
def tickingCl (lt : S.EA.Lab) : S.Val :=                  -- op (_, k) ⇒ tick (); resume k ()
  S.lam (S.split (S.var 0) (S.bind (S.perform lt 0 S.unitV) (S.resume (S.var 1) S.unitV)))
def pureCb : S.Val := S.lam (S.ret S.tt)
def failCb (le) : S.Val := S.lam (S.raise le 0 S.unitV)
def asyncCb (lw) : S.Val := S.lam (S.bind (S.perform lw 0 S.unitV) (S.ret S.tt))
```

---

**E1: no colouring (effect polymorphism).** This is the lead axis (decisions F1/F2): "one function
for every context" (`docs/operator/README.md` G1). One higher-order function is typed **once**, and
that one typing serves a callback at **every** row: the pure row, a failing row, a suspending row,
and every other row the instance types a callback body at, open rows included. Zhang–Myers
Example 1 has the same shape (`f [∅] …`, `f [h.lbl] …`), and so does
`corpus/pending/yield-callback.bc` (#161). Two concrete programs pin the behaviour: the three uses
in one program, the pure one unhandled at the pure row; and a use whose callback really suspends,
its continuation held after its handler returned while `f` runs again.

```
f = λg. g ()
E1   let f = f in
       f pure                                                          to b₁.   -- at the pure row
       handle exn {return x ⇒ inl x; raise _ ⇒ inr ()} (f fail)       to b₂.   -- fail = λ_. raise exn ()
       handle wait {return x ⇒ x; wait (_, k) ⇒ resume k ()} (f async) to b₃.   -- async = λ_. wait (); return tt
       return (b₁, (b₂, b₃))                                                     ⇒ (tt, (inr (), tt))
sched M = handle wait {return x ⇒ λ_. return x; wait (_, k) ⇒ λ_. resume k () to g. g ()} M
E1′  let f = f in
       sched (f async) to g.        -- the call of f suspends; the handler answers a closure holding κ
       f pure to b.                 -- f runs again while the first call is suspended
       g () to b₃.                  -- κ resumed after its handler returned
       return (b, b₃)                                                            ⇒ (tt, tt)
```

```lean
def hof : S.Val := S.lam (S.app (S.force (S.var 0)) S.unitV)
def uses (le lw) : S.Term :=                                   -- `f` is `var 0`
  S.bind (S.call (S.var 0) pureCb)
  (S.bind (toResult le (S.call (S.var 1) (failCb le)))
  (S.bind (resumer lw (S.call (S.var 2) (asyncCb lw)))
  (S.ret (S.pair (S.var 2) (S.pair (S.var 1) (S.var 0))))))
def noColour (le lw) : S.Term := S.lets [hof] (uses le lw)
def ans1 : S.Val := S.pair S.tt (S.pair (S.inr S.unitV) S.tt)
def ty1 : S.Ty := S.Tensor S.bool (S.Tensor (S.Sum S.bool S.UnitT) S.bool)
def schedRet : S.Val := S.lam (S.ret (S.lam (S.ret (S.var 1))))
def schedCl : S.Val := S.lam (S.split (S.var 0) (S.ret (S.lam
  (S.bind (S.resume (S.var 1) S.unitV) (S.app (S.force (S.var 0)) S.unitV)))))
def sched (lw) (M : S.Term) : S.Term := S.handle lw (S.hnd schedRet [schedCl]) M
def usesS (lw) : S.Term :=                                     -- `f` is `var 0`
  S.bind (sched lw (S.call (S.var 0) (asyncCb lw)))
  (S.bind (S.call (S.var 1) pureCb)
  (S.bind (S.app (S.force (S.var 1)) S.unitV)
  (S.ret (S.pair (S.var 1) (S.var 0)))))
def noColourS (lw) : S.Term := S.lets [hof] (usesS lw)

def NoColouring (S) : Prop :=
  S.ForLabels [sigExn, sigWait] fun ls => ∀ le lw, ls = [le, lw] →
    ∃ A, S.derV [] hof A ∧
      -- the schema: this one typing of `f` serves a callback at every row …
      S.PolyUse [A] (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      -- … and `f` calls the callback, catching nothing
      (∀ ε M, S.der [] M (S.F ε S.bool) →
         S.CallsThrough (fun _ => True) (S.lets [hof] (S.call (S.var 0) (S.lam M))) M) ∧
      -- the three callbacks' bodies, each at its own row
      S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧ S.der [] (S.raise le 0 S.unitV) (S.F (S.EA.lift le) S.bool) ∧
      S.der [] (S.bind (S.perform lw 0 S.unitV) (S.ret S.tt)) (S.F (S.EA.lift lw) S.bool) ∧
      -- E1: one program, three uses; E1′: a real suspension (`LetLaw` types the whole programs)
      S.der [A] (uses le lw) (S.F S.EA.unit ty1) ∧ S.RunsTo S.R₀ (noColour le lw) ans1 [] ∧
      S.der [A] (usesS lw) (S.F S.EA.unit (S.Tensor S.bool S.bool)) ∧ S.RunsTo S.R₀ (noColourS lw) (S.pair S.tt S.tt) []
```

**Why it needs effect polymorphism** (`not_noColouring_of_monoCallback`, §6.1, abstract). Say an
instance has none: at a use that applies a context variable to a callback, a callback accepted at
one type of the use is accepted at every type at which the use accepts some callback with the same
data answer (`MonoCallback`, a Prop over the instance). The schema accepts `ret tt` at the pure row
and `raise le 0 ()` at `(le)↑`, so `MonoCallback` accepts the raise's use at the pure row too. The
let law then types the closed program `let f = hof in f (λ_. raise le 0 ())` at the pure row.
`CallsThrough` makes that program reach the raise under a context that catches nothing, where
`OpStuck` stops it, `DataInj` says it is no answer, and `RowSig` says the pure row admits nothing:
`EffSafe` fails. So no instance meets S1, S3, S0 and E1 without effect polymorphism. The proof uses
no typing rule of the instance, only the let law and the schema, which A states.

The answer types are the same for all three callbacks (`bool`). So failure lives in the row, not in
a sum, as decisions E1 and E2 ask: failing operations raise, and the kernel's error is an abortive
operation.

**E2: higher-order polymorphism** (PR #233's closing comment, from the user's account: "the
higher-order cases (callbacks taking callbacks, stored or returned callbacks, policies as values,
effectful codata) were left pending behind workarounds. The goal was the general form."). There
are four programs. Each binds its higher-order functions once, uses them at two rows, one of which
is the pure row, and states the schema of its higher-order function. Each needs only let-bound
polymorphism with open rows, at one answer type per function. None needs a polymorphic value passed
as an argument and used at two rows, so rank-n stays OQ-13's question (§7 Q2).

```
E2a (callbacks taking callbacks)
  twice = λh. λg. h g to x. h g to y. return (x, y)
  let f = hof; let tw = twice in
    tw f pure to p₁.  handle exn {…inl/inr…} (tw f fail) to p₂.  return (p₁, p₂)       ⇒ ((tt, tt), inr ())
E2b (stored and returned callbacks)
  compose = λg₁. λg₂. return (λ_. g₁ () to _. g₂ ())
  let c = compose in
    c pure pure to k₀.  c async pure to k₁.  k₀ () to b₀.
    handle wait {…resume…} (k₁ ()) to b₁.  return (b₀, b₁)                                ⇒ (tt, tt)
E2c (policies as values)
  retry = λpol. λbody. handle exn {return x ⇒ x; raise _ ⇒ pol () to b. case b of inl _ ⇒ ff | inr _ ⇒ tt} (body ())
  let r = retry in
    r (λ_. ff) fail to a₁.
    handle log {return x ⇒ x; log (_, k) ⇒ resume k ()} (r (λ_. log tt; tt) fail) to a₂.  return (a₁, a₂)   ⇒ (ff, tt)
E2d (effectful codata: a generator over a row)
  sumGen = λgen. handle yield {return _ ⇒ ff; yield (x, k) ⇒ resume k () to r. case x of inl _ ⇒ r | inr _ ⇒ tt} (gen ())
  let s = sumGen in
    s (λ_. yield ff; yield tt) to c₁.
    handle exn {…inl/inr…} (s (λ_. yield ff; raise exn ())) to c₂.  return (c₁, c₂)               ⇒ (tt, inr ())
```

```lean
def twice : S.Val := S.lam (S.lam (S.bind (S.app (S.force (S.var 1)) (S.var 0))
  (S.bind (S.app (S.force (S.var 2)) (S.var 1)) (S.ret (S.pair (S.var 1) (S.var 0))))))
def body2a (le) : S.Term :=                                     -- `tw` is `var 0`, `f` is `var 1`
  S.bind (S.call2 (S.var 0) (S.var 1) pureCb)
  (S.bind (toResult le (S.call2 (S.var 1) (S.var 2) (failCb le))) (S.ret (S.pair (S.var 1) (S.var 0))))
def prog2a (le) : S.Term := S.lets [twice, hof] (body2a le)

def compose : S.Val := S.lam (S.lam (S.ret (S.lam
  (S.bind (S.app (S.force (S.var 2)) S.unitV) (S.app (S.force (S.var 2)) S.unitV)))))
def body2b (lw) : S.Term :=                                     -- `c` is `var 0`
  S.bind (S.call2 (S.var 0) pureCb pureCb) (S.bind (S.call2 (S.var 1) (asyncCb lw) pureCb)
  (S.bind (S.call (S.var 1) S.unitV) (S.bind (resumer lw (S.call (S.var 1) S.unitV))
  (S.ret (S.pair (S.var 1) (S.var 0))))))
def prog2b (lw) : S.Term := S.lets [compose] (body2b lw)

def retryP (le) : S.Val := S.lam (S.lam (S.handle le (S.hnd (S.lam (S.ret (S.var 0)))
  [S.lam (S.bind (S.app (S.force (S.var 2)) S.unitV) (S.case (S.var 0) (S.ret S.ff) (S.ret S.tt)))])
  (S.app (S.force (S.var 0)) S.unitV)))
def logPol (llog) : S.Val := S.lam (S.bind (S.perform llog 0 S.tt) (S.ret S.tt))
def body2c (le llog) : S.Term :=                                -- `r` is `var 0`
  S.bind (S.call2 (S.var 0) (S.lam (S.ret S.ff)) (failCb le))
  (S.bind (resumer llog (S.call2 (S.var 1) (logPol llog) (failCb le))) (S.ret (S.pair (S.var 1) (S.var 0))))
def prog2c (le llog) : S.Term := S.lets [retryP le] (body2c le llog)

def sumGen (ly) : S.Val := S.lam (S.handle ly (S.hnd (S.lam (S.ret S.ff))
  [S.lam (S.split (S.var 0) (S.bind (S.resume (S.var 0) S.unitV) (S.case (S.var 2) (S.ret (S.var 1)) (S.ret S.tt))))])
  (S.app (S.force (S.var 0)) S.unitV))
def gen1 (ly) : S.Val := S.lam (S.bind (S.perform ly 0 S.ff) (S.perform ly 0 S.tt))
def gen2 (ly le) : S.Val := S.lam (S.bind (S.perform ly 0 S.ff) (S.raise le 0 S.unitV))
def body2d (ly le) : S.Term :=                                  -- `s` is `var 0`
  S.bind (S.call (S.var 0) (gen1 ly)) (S.bind (toResult le (S.call (S.var 1) (gen2 ly le)))
  (S.ret (S.pair (S.var 1) (S.var 0))))
def prog2d (ly le) : S.Term := S.lets [sumGen ly] (body2d ly le)

def HigherOrderPoly (S) : Prop :=
  S.ForLabels [sigExn, sigWait, sigYield, sigLog] fun ls => ∀ le lw ly llog, ls = [le, lw, ly, llog] →
    -- E2a: `twice` and `f` typed once; `twice f g` serves `g` at every row, and calls it
    (∃ Af At, S.derV [] hof Af ∧ S.derV [] twice At ∧
       S.PolyUse [At, Af] (fun g => S.call2 (S.var 0) (S.var 1) g) S.bool (S.Tensor S.bool S.bool) ∧
       (∀ ε M, S.der [] M (S.F ε S.bool) →
          S.CallsThrough (fun _ => True) (S.lets [twice, hof] (S.call2 (S.var 0) (S.var 1) (S.lam M))) M) ∧
       S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧ S.der [] (S.raise le 0 S.unitV) (S.F (S.EA.lift le) S.bool) ∧
       S.der [At, Af] (body2a le) (S.F S.EA.unit ty2a) ∧
       S.RunsTo S.R₀ (prog2a le) (S.pair (S.pair S.tt S.tt) (S.inr S.unitV)) []) ∧
    -- E2b: `compose`; the composed callback, stored and called later, serves every row
    (∃ Ac, S.derV [] compose Ac ∧
       S.PolyUse [Ac] (fun g => S.bind (S.call2 (S.var 0) g pureCb) (S.call (S.var 0) S.unitV)) S.bool S.bool ∧
       S.der [Ac] (body2b lw) (S.F S.EA.unit ty2b) ∧ S.RunsTo S.R₀ (prog2b lw) (S.pair S.tt S.tt) []) ∧
    -- E2c: `retry`: the policy at every row without `exn`, the body at every `exn ⊙ ρ`
    (∃ Ar, S.derV [] (retryP le) Ar ∧
       S.PolyUseLacks [Ar] le (fun g => S.call2 (S.var 0) g (failCb le)) S.bool S.bool ∧
       S.PolyUseOpen [Ar] le (fun g => S.call2 (S.var 0) (S.lam (S.ret S.ff)) g) S.bool S.bool ∧
       S.der [Ar] (body2c le llog) (S.F S.EA.unit ty2b) ∧ S.RunsTo S.R₀ (prog2c le llog) (S.pair S.ff S.tt) []) ∧
    -- E2d: `sumGen`: the generator at every `yield ⊙ ρ`
    (∃ As, S.derV [] (sumGen ly) As ∧
       S.PolyUseOpen [As] ly (fun g => S.call (S.var 0) g) S.UnitT S.bool ∧
       S.der [As] (body2d ly le) (S.F S.EA.unit ty2d) ∧
       S.RunsTo S.R₀ (prog2d ly le) (S.pair S.tt (S.inr S.unitV)) [])
-- ty2a = (bool ⊗ bool) ⊗ ((bool ⊗ bool) ⊕ 1); ty2b = bool ⊗ bool; ty2d = bool ⊗ (bool ⊕ 1)
```

Each higher-order function is used at the pure row and at one other row:

- `twice` at `{exn}`;
- `compose` at `{wait}`;
- `retry` at `{log}`, with its body at the open row `exn ⊙ ρ`;
- `sumGen` at `{exn}`, its generator at `yield ⊙ ρ`, with the raise forwarded through the reinstalled
  yield handler.

The schemas say more than the two uses: one typing serves every row. `PolyUseLacks` and
`PolyUseOpen` quantify only at rows that do not admit the function's own label, because SPEC §19's
`[handle]` asks that a handler's label not be in its outer row. The non-vacuity argument of E1
applies to E2a unchanged, with `twice f` in place of `f` (`not_higherOrderPoly_of_monoCallback`,
§6.1).

**E3: divergence, an effect any function may have.** Decision 35: "Any function may loop without
bound if its type says so; it is not a privilege of `main` … A div function returns a loop …
sequencing loops is the delay bind … running a loop is handling the effect: the runtime drives
`main` forever, and `div_fuel` runs `n` steps". SPEC §19 *Acceptance* (4): "An infinite loop that
logs", with "a handler … installed per observation". In A's vocabulary (§1.3) a loop is built from
a step function, a close and a state (`unfold`), observed anywhere (`next`, `close`), and run
without bound by the runtime's driver (`drive`) at the top; `LoopLaws` and `DriveLaws` (§1.4) say
what each does.

```
tickStep s = tick (); return (inr s)          countStep s = case s of inl _ ⇒ tick (); return (inr (inr ())) | inr _ ⇒ return (inl tt)
logStep s = log tt; return (inr s)            tickL = unfold tickStep drop ()      countL = unfold countStep drop (inl ())
logL = unfold logStep drop ()                 spinL = unfold (λs. return (inr s)) drop ()
seqL l₁ l₂ = the delay bind of SPEC §14: run l₁ to its end, then l₂
handleL l = unfold (λl. handle log {return x ⇒ x; log (_, k) ⇒ tick (); resume k ()} (next l)) (λl. close l) l
fuel n l = observe l at most n times, then close it
divF = λs. return (unfold countStep drop s)                          -- a div function: its result is a loop
E3a  drive (return (inr tickL))                                      ⇒ never completes; tick, tick, …
E3b  drive (return (inr countL))                                     ⇒ tt, after [tick]
E3c  drive (let d = divF in d (inl ()) to l₁. d (inl ()) to l₂. return (inr (seqL l₁ l₂)))
                                                                     ⇒ tt, after [tick, tick]
E3d  drive (return (inr (handleL logL)))                             ⇒ never completes; tick, tick, … (log handled in-program)
E3e  drive (return (inr (seqL countL logL)))                         ⇒ never completes; tick, then log, log, …
E3f  drive (let f = hof in f (λ_. return tickL) to l. return (inr l)) ⇒ never completes; tick, tick, …
E3g  fuel 3 spinL                                                    ⇒ inr (), at the pure row and a data answer
E3g′ drive (return (inr spinL))                                      ⇒ never completes, silently, at the pure row
```

```lean
def dropS : S.Val := S.lam (S.ret S.unitV)                        -- close: a data state is dropped
def runL (l : S.Val) : S.Term := S.drive (S.ret (S.inr l))
def tickStep (lt) : S.Val := S.lam (S.bind (S.perform lt 0 S.unitV) (S.ret (S.inr (S.var 1))))
def countStep (lt) : S.Val := S.lam (S.case (S.var 0)
  (S.bind (S.perform lt 0 S.unitV) (S.ret (S.inr (S.inr S.unitV)))) (S.ret (S.inl S.tt)))
def logStep (llog) : S.Val := S.lam (S.bind (S.perform llog 0 S.tt) (S.ret (S.inr (S.var 1))))
def tickL (lt) : S.Val := S.unfold (tickStep lt) dropS S.unitV
def countL (lt) : S.Val := S.unfold (countStep lt) dropS (S.inl S.unitV)
def logL (llog) : S.Val := S.unfold (logStep llog) dropS S.unitV
def spinL : S.Val := S.unfold (S.lam (S.ret (S.inr (S.var 0)))) dropS S.unitV
/-- The delay bind at two loops (SPEC §14's `div_bind`, whose continuation here returns the second
loop): the state is `inl (l₁, l₂)`, in the first loop, or `inr l₂`, in the second. -/
def seqStep : S.Val := S.lam (S.case (S.var 0)
  (S.split (S.var 0) (S.bind (S.next (S.var 1)) (S.case (S.var 0)
     (S.ret (S.inr (S.inr (S.var 2))))                             -- the first finished: go on in `l₂`
     (S.ret (S.inr (S.inl (S.pair (S.var 0) (S.var 2))))))))       -- the first goes on
  (S.bind (S.next (S.var 0)) (S.case (S.var 0)
     (S.ret (S.inl (S.var 0)))                                     -- the second finished
     (S.ret (S.inr (S.inr (S.var 0)))))))                          -- the second goes on
def seqClose : S.Val := S.lam (S.case (S.var 0)
  (S.split (S.var 0) (S.bind (S.close (S.var 1)) (S.close (S.var 1)))) (S.close (S.var 0)))
def seqL (l₁ l₂ : S.Val) : S.Val := S.unfold seqStep seqClose (S.inl (S.pair l₁ l₂))
/-- A handler installed per observation (SPEC §19), its clause performing the platform `tick`. -/
def handleL (lt llog) (l : S.Val) : S.Val :=
  S.unfold (S.lam (S.handle llog (S.hnd (S.lam (S.ret (S.var 0))) [tickingCl lt]) (S.next (S.var 0))))
    (S.lam (S.close (S.var 0))) l
/-- `div_fuel`: observe at most `n` times, then close. -/
def fuel : ℕ → S.Val → S.Term
  | 0, l => S.bind (S.close l) (S.ret (S.inr S.unitV))
  | n + 1, l => S.bind (S.next l) (S.case (S.var 0) (S.ret (S.inl (S.var 0))) (fuel n (S.var 0)))
def divF (lt) : S.Val := S.lam (S.ret (S.unfold (countStep lt) dropS (S.var 0)))
def e3cBody (lt) : S.Term :=                                     -- `d` is `var 0`
  S.bind (S.call (S.var 0) (S.inl S.unitV)) (S.bind (S.call (S.var 1) (S.inl S.unitV))
  (S.ret (S.inr (seqL (S.var 1) (S.var 0)))))
def e3c (lt) : S.Term := S.drive (S.lets [divF lt] (e3cBody lt))
def divCb (lt) : S.Val := S.lam (S.ret (tickL lt))
def e3fBody (lt) : S.Term := S.bind (S.call (S.var 0) (divCb lt)) (S.ret (S.inr (S.var 0)))   -- `f` is `var 0`
def e3f (lt) : S.Term := S.drive (S.lets [hof] (e3fBody lt))

def Loops (S) : Prop :=
  S.ForLabels [sigTick, sigLog] fun ls => ∀ lt llog, ls = [lt, llog] →
    -- E3a, E3b: a loop that never ends, and one that ends
    (∃ ε L, S.Answers (Rtick lt) ε ∧ S.der [] (runL (tickL lt)) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (Rtick lt) (runL (tickL lt)) (fun n => List.replicate n (tickEv lt)) ∧
    (∃ ε L, S.Answers (Rtick lt) ε ∧ S.der [] (runL (countL lt)) (S.F ε (S.Sum S.bool L))) ∧
    S.RunsTo (Rtick lt) (runL (countL lt)) S.tt [tickEv lt] ∧
    -- E3c: a div function, typed once, called twice inside a program that sequences its loops
    (∃ Ad ε L, S.derV [] (divF lt) Ad ∧ S.Answers (Rtick lt) ε ∧
       S.der [Ad] (e3cBody lt) (S.F ε (S.Sum S.bool L)) ∧ S.der [] (e3c lt) (S.F ε (S.Sum S.bool L))) ∧
    S.RunsTo (Rtick lt) (e3c lt) S.tt [tickEv lt, tickEv lt] ∧
    -- E3d: a loop under a user handler whose clause performs the platform tick
    (∃ ε L, S.Answers (Rtick lt) ε ∧ S.der [] (runL (handleL lt llog (logL llog))) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (Rtick lt) (runL (handleL lt llog (logL llog))) (fun n => List.replicate n (tickEv lt)) ∧
    -- E3e: two loops sequenced, the first ending and the second not
    (∃ ε L, S.Answers (Rtl lt llog) ε ∧ S.der [] (runL (seqL (countL lt) (logL llog))) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (Rtl lt llog) (runL (seqL (countL lt) (logL llog)))
      (fun n => tickEv lt :: List.replicate n (logEv llog)) ∧
    -- E3f: the no-colouring function applied to a div callback
    (∃ A' ε L, S.derV [] hof A' ∧ S.Answers (Rtick lt) ε ∧
       S.der [A'] (e3fBody lt) (S.F ε (S.Sum S.UnitT L)) ∧ S.der [] (e3f lt) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (Rtick lt) (e3f lt) (fun n => List.replicate n (tickEv lt)) ∧
    -- E3g: fuel makes a silent loop total at a data answer of the pure row; the driver runs it forever
    S.der [] (fuel 3 spinL) (S.F S.EA.unit S.bool) ∧ S.RunsTo S.R₀ (fuel 3 spinL) (S.inr S.unitV) [] ∧
    (∃ L, S.der [] (runL spinL) (S.F S.EA.unit (S.Sum S.UnitT L))) ∧ S.RunsForever S.R₀ (runL spinL) (fun _ => [])
```

What each program pins, and how our instance meets it:

| program | what it pins | our mechanism (§4.1) |
|---|---|---|
| E3a, E3b | a loop value, observed step by step, run by the driver to its end or forever | `unfold` at `Loop_Σ A 1` (`unfoldV` over `λs. ⟨f s, g s⟩`); `next` is `π₁`, `close` is `π₂`; `drive` is `RStep`'s phase |
| E3c | a div function (its result is a loop), defined once and called twice inside a larger program, whose loops the delay bind sequences | `divF`'s type `!U(S ⊸ F(U(Loop_Σ bool 1)))`, decision 35's `A ⇒ U(Loop B R)`; `seqL` is `div_bind`'s shape (SPEC §14) |
| E3d | an infinite loop that logs, the log handled in-program by a handler whose clause performs the platform operation | a handler installed per observation (SPEC §19, *Acceptance* (3), (4)) |
| E3e | two loops sequenced, the second never ending | `div_bind` |
| E3f | a higher-order function serves a div callback | `hof` typed at the div callback's computation type: decision 35's specialization |
| E3g | div code made total by fuel, at a data answer of the pure row | `div_fuel` (`driveE n`, `Core/DelayPrograms.lean`) |
| E3g′ | the same loop, driven, diverges silently at the pure row, at a type that is not data | the runtime's driver |

- **Divergence appears in types.** S2 claims termination at every div-free type, and `DataDiv` makes
  the pure row's data answers div-free. E3g′ diverges at the pure row, so its type is not a data
  type there (`divInTypes_of_loops`, §6.1); E3g runs the same loop totally at a data answer. An
  instance that claims termination of every pure-row program fails S2 or E3. Totality is not a
  goal: an instance in which every typed program terminates fails E3 (`not_loops_of_total`).
- **A div callback, and "typed once".** E3f types `hof` at the div callback's type by a typing of
  its own (`∃ A'`). One typing across E1's total callbacks and a div callback would need
  polymorphism over the callback's answer type, `bool` against a loop type, which no decision asks:
  decision 35 meets "serves total and div callbacks alike" by specialization at the callback's
  computation type. E1's single typing is decision 62's, over rows. If divergence moved into rows,
  E1's schema would cover div callbacks with no change; that is §7 Q3.
- **Where a loop runs.** In our instance only the driver runs a loop without bound, at the top;
  every other computation is total (`total_no_infinite_run`). A does not require that: `LoopLaws`
  is also met by a calculus with `fix`, whose runtime has a primitive driver as ours does
  (`DriveLaws`), and which may diverge inside a computation at a type that is not div-free. So done
  does not fix the whole-program reading; §7 Q3 keeps it open.
- **Inside the driven loops.** The tick traces of E3a–f are the runner's answers to operations that
  a driven loop performs: `RStep.io` fires at `kcomp driveF K` (§1.4). E3a's program is typed at
  `{tick}`, and its run stops at nothing: each `tick` is answered under the driver.

**E4: deep handlers** (decision 62, "Handlers are deep"). One handler, written once, catches every
yield of the computation, including those performed after a resume. Its clause performs a platform
`tick`, so the trace counts the catches.

```
handle yield {return _ ⇒ (); yield (_, k) ⇒ tick (); resume k ()} (yield tt; yield ff)    ⇒ (), trace [tick, tick]
```

```lean
def deepGen (ly lt) : S.Term :=
  S.handle ly (S.hnd (S.lam (S.ret S.unitV)) [tickingCl lt]) (S.bind (S.perform ly 0 S.tt) (S.perform ly 0 S.ff))
def DeepHandler (S) : Prop :=
  S.ForLabels [sigYield, sigTick] fun ls => ∀ ly lt, ls = [ly, lt] →
    S.der [] (deepGen ly lt) (S.F (S.EA.lift lt) S.UnitT) ∧
    S.RunsTo (Rtick lt) (deepGen ly lt) S.unitV [tickEv lt, tickEv lt]
```

A shallow handler leaves the second `yield` without a handler, under the bind frame of the first.
The program is typed at `{tick}`, so S3 and `OpStuck` exclude that run.

**E5: nested handlers, in both orders** (K4: the reconciler chain must "work, full stop"; SPEC §19
*Acceptance* (1), "in both nesting orders, with each order's observable result"). `log` is a native
answering operation with a state-passing handler that keeps the last logged value (decision 59:
handler state "passed to each clause and at each resume").

```
body        = log tt; raise exn ()
withLog M   = handle log {return x ⇒ λs. (x, s); log (b, k) ⇒ λs. resume k () to g. g b} M to g. g ff
logOutside  = withLog (handle exn {…inl/inr…} body)     ⇒ (inr (), tt): the log state survives the error
failOutside = handle exn {…inl/inr…} (withLog body)     ⇒ inr (): the unwind drops the log handler and its state
```

```lean
def body5 (llog le) : S.Term := S.bind (S.perform llog 0 S.tt) (S.raise le 0 S.unitV)
def logRet : S.Val := S.lam (S.ret (S.lam (S.ret (S.pair (S.var 1) (S.var 0)))))
def logCl : S.Val := S.lam (S.split (S.var 0) (S.ret (S.lam
  (S.bind (S.resume (S.var 1) S.unitV) (S.app (S.force (S.var 0)) (S.var 3))))))
def withLog (llog) (M : S.Term) : S.Term := S.bind (S.handle llog (S.hnd logRet [logCl]) M) (S.app (S.force (S.var 0)) S.ff)
def NestedHandlers (S) : Prop :=
  S.ForLabels [sigLog, sigExn] fun ls => ∀ llog le, ls = [llog, le] →
    S.der [] (withLog llog (toResult le (body5 llog le))) (S.F S.EA.unit (S.Tensor (S.Sum S.UnitT S.UnitT) S.bool)) ∧
    S.RunsTo S.R₀ (withLog llog (toResult le (body5 llog le))) (S.pair (S.inr S.unitV) S.tt) [] ∧
    S.der [] (toResult le (withLog llog (body5 llog le))) (S.F S.EA.unit (S.Sum (S.Tensor S.UnitT S.bool) S.UnitT)) ∧
    S.RunsTo S.R₀ (toResult le (withLog llog (body5 llog le))) (S.inr S.unitV) []
```

The first program forwards a resuming operation, `log`, through `exn`'s handler, and the resume
reinstalls that handler (deep). The second forwards an abortive operation, `raise`, through `log`'s
handler and its pending clause, which the unwind drops. Core's `nLogOutside` and `nFailOutside` are
the same two programs at Core's encoding (checked at tier 1, `acceptedT1_nLogOutside`,
`acceptedT1_nFailOutside`).

**E6: no accidental handling** (survey #10; Zhang–Myers' abstract and Example 1). A higher-order
function handles its own instance of an effect, and is typed once, polymorphic in its callback's
row. Its call reaches the callback without catching any label of the callback's but its own, and a
callback that raises another instance of the effect, whose label is different, has its raise tunnel
through to the outer handler.

```
fwrap = λg. handle exnᵢ {return x ⇒ x; raise _ ⇒ ff} (g ())
handle exnₒ {…inl/inr…} (let w = fwrap in w (λ_. raise exnₒ ()))     ⇒ inr ()   (accidental handling would give inl ff)
```

```lean
def fwrap (li) : S.Val := S.lam (S.handle li (S.hnd (S.lam (S.ret (S.var 0))) [S.lam (S.ret S.ff)])
  (S.app (S.force (S.var 0)) S.unitV))
def tunnel (li lo) : S.Term := toResult lo (S.lets [fwrap li] (S.call (S.var 0) (failCb lo)))
def Tunnel (S) : Prop :=
  S.ForLabels [sigExn, sigExn] fun ls => ∀ li lo, ls = [li, lo] →
    ∃ Af, S.derV [] (fwrap li) Af ∧
      -- one typing of `fwrap`: the callback and the use at the same row ε, every ε without `li`
      -- (Zhang–Myers' `f : ∀α. (N → [N]α) → [N]α`, used as `f [∅] …` and `f [h.lbl] (g h)`)
      S.PolyUseLacks [Af] li (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      (∀ ε M, S.Lacks ε li → S.der [] M (S.F ε S.bool) →
         S.CallsThrough (· ≠ li) (S.lets [fwrap li] (S.call (S.var 0) (S.lam M))) M) ∧
      S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧ S.der [] (S.raise lo 0 S.unitV) (S.F (S.EA.lift lo) S.bool) ∧
      S.der [] (tunnel li lo) (S.F S.EA.unit (S.Sum S.bool S.UnitT)) ∧ S.RunsTo S.R₀ (tunnel li lo) (S.inr S.unitV) []
```

- **What is a corollary.** The run of `tunnel`, and the `CallsThrough` clause, follow from
  `KontLaws` and S4: a handler frame of `li` catches only `li`, and `li ≠ lo`. They are kept as a
  check, not counted as a lower bound.
- **What E6 adds.** `fwrap`'s one typing for every callback row without its own label, with the
  callback and the use at the **same** row (`PolyUseLacks`): the shape of Zhang–Myers' Example 1,
  `f : ∀α. (N → [N]α) → [N]α`, where "f [∅] (λx : N. x + x)" and "f [h.lbl] (g h)" use one `f` and
  the callee's own handler does not appear in its type. A callback that raises `li` is not in the
  schema: typing one, with the use at a row from which `fwrap`'s handler has removed `li`, would be
  the accidental handling E6 excludes. (`PolyUseOpen`, the body at `l ⊙ ε` and the use at `ε`, is
  for `retry`, `timeout` and `sumGen`, which are meant to handle their body's label.) The argument
  of E1 applies at `fwrap`: both callbacks, `ret tt` at `0` and `raise lo 0 ()` at `(lo)↑`, lack
  `li`, since `li ≠ lo`, and `fwrap`'s handler does not catch `lo` (`not_tunnel_of_monoCallback`,
  §6.1).
- **The substantive form is binary.** Zhang–Myers' guarantee is that `fwrap g` behaves as `g` at
  every row without `li` (T3's `Tunnel`, out of the first pass, §1.7). In A, labels are global, so a
  callback may raise `li` itself, and `fwrap` catches it. Static names per handler site keep
  `fwrap`'s label out of every caller's row in the surface language, which is why T3 is stated at
  rows without `li`.

**E7: abandoning a suspension, and the cancel policy as built** (SPEC §19 *Cancels*; *Acceptance*
(5), (6); survey #9, #12, #14; `Core/EffCancel.lean`'s `prog` and `prog₃`). A timer cancels a
suspended body whose frame holds a finaliser. The traces fix which finalisers fire, in which order,
and how each ends; the answers fix each clause of SPEC §19's policy.

```
body D = (wait (); return tt) then x. return x unwind D
timeout M = handle wait {return x ⇒ inl x; wait (_, k) ⇒ cancel k; inr ()} M
E7a  timeout (body ())                                                   ⇒ inr ()   [fire (), finEnd none]
E7b  handle exnₒ {…} (timeout (body (raise exnₒ ())))                     ⇒ inr ()   [fire (raise exnₒ ()), finEnd exnₒ]
E7c  timeout (handle exnᵢ {…} (body (raise exnᵢ ())))                     ⇒ inr ()   [fire (raise exnᵢ ()), finEnd exnᵢ]
E7d  handle exn_a {…} (handle exn_b {…} (timeout
       ((body (raise exn_a ())) then x. return x unwind raise exn_b ())))  ⇒ inr ()   [fire (raise exn_a ()), finEnd exn_a,
                                                                                      fire (raise exn_b ()), finEnd exn_b]
```

| program | which clause of SPEC §19 it pins | the answer and trace under the alternative |
|---|---|---|
| E7a | abandoning is typable, the canceller proceeds, and the frozen finaliser runs once | `[]`, if the finaliser did not run |
| E7b | the finaliser runs once, and its error is re-raised at the canceller ([cancel-raise]) | `inl (inr ())`, if the finaliser did not run or its error were suppressed (the #186 record's "always cancelled", F4) |
| E7c | the error of a label the cancelled region handles is suppressed, and the region's dying handler does not catch it | `inl (inr ())`, if the region's handler intercepted it |
| E7d | innermost first, and the first error is kept | the fires in the other order, and `inl (inr ())`, if outermost first or the last error kept |

```lean
def bodyF (lw) (D : S.Term) : S.Term := S.thenT (S.bind (S.perform lw 0 S.unitV) (S.ret S.tt)) (S.ret (S.var 0)) D
def e7a (lw) := timeoutH lw (bodyF lw (S.ret S.unitV))
def e7b (lw lo) := toResult lo (timeoutH lw (bodyF lw (S.raise lo 0 S.unitV)))
def e7c (lw li) := timeoutH lw (toResult li (bodyF lw (S.raise li 0 S.unitV)))
def e7d (lw la lb) := toResult la (toResult lb (timeoutH lw
  (S.thenT (bodyF lw (S.raise la 0 S.unitV)) (S.ret (S.var 0)) (S.raise lb 0 S.unitV))))
def finTr (l) : List S.Ev := [.fire (S.raise l 0 S.unitV), .finEnd (some (l, 0, S.unitV))]
def CancelPolicy (S) : Prop :=
  S.ForLabels [sigWait, sigExn, sigExn] fun ls => ∀ lw la lb, ls = [lw, la, lb] →
    S.der [] (e7a lw) (S.F S.EA.unit (S.Sum S.bool S.UnitT)) ∧
    S.RunsTo S.R₀ (e7a lw) (S.inr S.unitV) [.fire (S.ret S.unitV), .finEnd none] ∧
    S.der [] (e7b lw la) (S.F S.EA.unit ty7) ∧ S.RunsTo S.R₀ (e7b lw la) (S.inr S.unitV) (finTr la) ∧
    S.der [] (e7c lw la) (S.F S.EA.unit ty7) ∧ S.RunsTo S.R₀ (e7c lw la) (S.inr S.unitV) (finTr la) ∧
    S.der [] (e7d lw la lb) (S.F S.EA.unit ty7d) ∧ S.RunsTo S.R₀ (e7d lw la lb) (S.inr S.unitV) (finTr la ++ finTr lb)
-- ty7 = (bool ⊕ 1) ⊕ 1; ty7d = ((bool ⊕ 1) ⊕ 1) ⊕ 1
```

**E8: unwinding through finalisers** (survey #9, "Each destructor runs exactly once, via
unwinding"; SPEC [finalise], with supersession). An unwind fires a finaliser with no `finEnd`: the
finaliser runs in place, and S4's finaliser law says what follows.

```
E8a  handle exn {…} ((raise exn ()) then x. return x unwind ())                          ⇒ inr ()        [fire ()]
E8b  handle exn_a {…} (handle exn_b {…} ((raise exn_a ()) then x. return x unwind raise exn_b ()))
                                                                                          ⇒ inl (inr ())  [fire (raise exn_b ())]
```

```lean
def e8a (le) := toResult le (S.thenT (S.raise le 0 S.unitV) (S.ret (S.var 0)) (S.ret S.unitV))
def e8b (la lb) := toResult la (toResult lb (S.thenT (S.raise la 0 S.unitV) (S.ret (S.var 0)) (S.raise lb 0 S.unitV)))
def UnwindPolicy (S) : Prop :=
  S.ForLabels [sigExn, sigExn] fun ls => ∀ la lb, ls = [la, lb] →
    S.der [] (e8a la) (S.F S.EA.unit (S.Sum S.UnitT S.UnitT)) ∧ S.RunsTo S.R₀ (e8a la) (S.inr S.unitV) [.fire (S.ret S.unitV)] ∧
    S.der [] (e8b la lb) (S.F S.EA.unit (S.Sum (S.Sum S.UnitT S.UnitT) S.UnitT)) ∧
    S.RunsTo S.R₀ (e8b la lb) (S.inl (S.inr S.unitV)) [.fire (S.raise lb 0 S.unitV)]
```

In E8b the finaliser's raise supersedes the pending one. If the finaliser did not run, the trace
would be empty, and the pending raise would reach `exn_a`'s handler: the answer would be `inr ()`.

**E9: a stored continuation** (SPEC §19 *Acceptance* (6): "A stored continuation is unwound";
`takeProg`'s shape; the survey's "Stores it and resumes it elsewhere" (A4), and its #8: "moving it
out with `replace` is allowed"). The handler returns a closure that holds `κ`. The closure is
applied **after the handler has returned**, and it resumes or cancels `κ` there.

```
stash M = handle yield {return _ ⇒ λc. ff;
                        yield (x, k) ⇒ λc. case c of inl _ ⇒ cancel k; x | inr _ ⇒ resume k () to g. g (inr ())} M
gen = yield tt; yield ff
E9a  stash gen to g. g (inr ())                                                     ⇒ ff
E9b  stash gen to g. g (inl ())                                                     ⇒ tt
E9c  handle exnₒ {…} (stash (gen then x. return x unwind raise exnₒ ()) to g. g (inl ()))   ⇒ inr ()   [fire (raise exnₒ ()), finEnd exnₒ]
```

```lean
def stashRet : S.Val := S.lam (S.ret (S.lam (S.ret S.ff)))
def stashCl : S.Val := S.lam (S.split (S.var 0) (S.ret (S.lam (S.case (S.var 0)
  (S.bind (S.cancel (S.var 2)) (S.ret (S.var 4)))
  (S.bind (S.resume (S.var 2) S.unitV) (S.app (S.force (S.var 0)) (S.inr S.unitV)))))))
def stash (ly) (M : S.Term) : S.Term := S.handle ly (S.hnd stashRet [stashCl]) M
def gen9 (ly) : S.Term := S.bind (S.perform ly 0 S.tt) (S.perform ly 0 S.ff)
def e9 (ly) (M : S.Term) (c : S.Val) : S.Term := S.bind (stash ly M) (S.app (S.force (S.var 0)) c)
def e9c (ly lo) : S.Term := toResult lo (e9 ly (S.thenT (gen9 ly) (S.ret (S.var 0)) (S.raise lo 0 S.unitV)) (S.inl S.unitV))
def StoredK (S) : Prop :=
  S.ForLabels [sigYield, sigExn] fun ls => ∀ ly lo, ls = [ly, lo] →
    S.der [] (e9 ly (gen9 ly) (S.inr S.unitV)) (S.F S.EA.unit S.bool) ∧ S.RunsTo S.R₀ (e9 ly (gen9 ly) (S.inr S.unitV)) S.ff [] ∧
    S.der [] (e9 ly (gen9 ly) (S.inl S.unitV)) (S.F S.EA.unit S.bool) ∧ S.RunsTo S.R₀ (e9 ly (gen9 ly) (S.inl S.unitV)) S.tt [] ∧
    S.der [] (e9c ly lo) (S.F S.EA.unit (S.Sum S.bool S.UnitT)) ∧ S.RunsTo S.R₀ (e9c ly lo) (S.inr S.unitV) (finTr lo)
```

In E9c the cancel runs after its handler has returned. It fires the frozen finaliser once, and the
error reaches the handlers around the canceller. A storage location for `κ` (a cell) is the
composite's I1 and AT17 (§3.4), because cells are B's.

**E10: the reconciler** (K4, U5: "need to work, full stop"; OQ-13: the reconciler chain's `timeout`
and `retry` "are generic over rows"; the operator: "`call`, which is `retry` of `timeout` of the
call"). A driven loop. Each iteration does three things. It retries a call under a timeout. It
times out a retried call. It times out a retried body that waits, which is cancelled while
suspended under the retry's handler. Then it logs to the platform. `timeout` and `retry` are bound
once, each serves a body at every row with its own label added (the schemas), and each is used at
two rows in the loop. Every body and every use answers `bool`: `timeout` answers its default `ff`
when it cancels, and `retry` answers `ff` when the second attempt fails. So each function has one
type, and only its row varies between uses; no use needs polymorphism over value types (§4.2). The
operator's `timeout(d, body)` is `race(body, { sleep(d) })`, "and the loser unwinds like a raise"
(`docs/operator/README.md` §4.4): when the timer wins, the answer is the timer branch's, here `ff`.

```
timeout = λb. handle wait {return x ⇒ x; wait (_, k) ⇒ cancel k; return ff} (b ())
retry   = λb. handle exn {return x ⇒ x; raise _ ⇒ handle exn {return x ⇒ x; raise _ ⇒ ff} (b ())} (b ())
call    = λ_. kube () to ok. case ok of inl _ ⇒ raise exn () | inr _ ⇒ tt
waitCall = λ_. wait (); call ()
drive (let timeout = timeout; let retry = retry in return (inr (unfold (λs.
          retry (λ_. timeout call) to a.           -- retry at {kube}; timeout at {exn, kube}
          timeout (λ_. retry call) to b.           -- timeout at {kube}; retry at {kube}
          timeout (λ_. retry waitCall) to c.       -- timeout at {kube}; retry at {wait, kube}; the wait is
                                                   --   cancelled under retry's handler, and c is ff
          log c; return (inr s)) drop ())))
```

```lean
/-- `wait (_, k) ⇒ cancel k; return ff`: the clause `cancelCl` of §1.5, here at an affine operation. -/
def timeoutR (lw) : S.Val := S.lam (S.handle lw (S.hnd (S.lam (S.ret (S.var 0))) [cancelCl])
  (S.app (S.force (S.var 0)) S.unitV))
def retryR (le) : S.Val := S.lam (S.handle le (S.hnd (S.lam (S.ret (S.var 0)))
  [S.lam (S.handle le (S.hnd (S.lam (S.ret (S.var 0))) [S.lam (S.ret S.ff)])
     (S.app (S.force (S.var 1)) S.unitV))])
  (S.app (S.force (S.var 0)) S.unitV))
def callK (lk le) : S.Val := S.lam (S.bind (S.perform lk 0 S.unitV) (S.case (S.var 0) (S.raise le 0 S.unitV) (S.ret S.tt)))
def waitCall (lw lk le) : S.Val := S.lam (S.bind (S.perform lw 0 S.unitV) (S.app (S.force (callK lk le)) S.unitV))
/-- The step, with `retry` as `var 1` and `timeout` as `var 2` inside it (the context `[retry, timeout]`
outside it).  After the third bind, `c` is `var 0` and the state `s` is `var 3`. -/
def iterOpen (lw le lk llog) : S.Val := S.lam
  (S.bind (S.call (S.var 1) (S.lam (S.call (S.var 3) (callK lk le))))
  (S.bind (S.call (S.var 3) (S.lam (S.call (S.var 3) (callK lk le))))
  (S.bind (S.call (S.var 4) (S.lam (S.call (S.var 4) (waitCall lw lk le))))
  (S.bind (S.perform llog 0 (S.var 0)) (S.ret (S.inr (S.var 4)))))))
def reconBody (lw le lk llog) : S.Term := S.ret (S.inr (S.unfold (iterOpen lw le lk llog) dropS S.unitV))
def recon (lw le lk llog) : S.Term := S.drive (S.lets [retryR le, timeoutR lw] (reconBody lw le lk llog))
def iterTrace (lk llog) : List S.Ev :=
  [.io lk 0 S.unitV S.ff, .io lk 0 S.unitV S.tt, .io lk 0 S.unitV S.ff, .io lk 0 S.unitV S.tt, .io llog 0 S.ff S.unitV]
def Reconciler (S) : Prop :=
  S.ForLabels [sigWait, sigExn, sigKube, sigLog] fun ls => ∀ lw le lk llog, ls = [lw, le, lk, llog] →
    ∃ At Ar ε L, S.derV [] (timeoutR lw) At ∧ S.derV [] (retryR le) Ar ∧
      -- the schemas: one typing of each serves a body at every row with its own label added
      S.PolyUseOpen [At] lw (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      (∀ ε M, S.Lacks ε lw → S.der [] M (S.F ε S.bool) →
         S.CallsThrough (· ≠ lw) (S.lets [timeoutR lw] (S.call (S.var 0) (S.lam M))) M) ∧
      S.PolyUseOpen [Ar] le (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧ S.der [] (S.raise le 0 S.unitV) (S.F (S.EA.lift le) S.bool) ∧
      -- the loop: both bound once, each used at two rows, at `bool` throughout
      S.der [Ar, At] (reconBody lw le lk llog) (S.F ε (S.Sum S.UnitT L)) ∧
      S.der [] (recon lw le lk llog) (S.F ε (S.Sum S.UnitT L)) ∧ S.Answers (Rrec lk llog) ε ∧
      S.RunsForever (Rrec lk llog) (recon lw le lk llog) (fun n => (List.replicate n (iterTrace lk llog)).flatten)
```

Each iteration's trace: in `a`, the first attempt's `kube` answers `ff` and raises. The raise
passes `timeout`'s handler, `retry` catches it, and the second attempt's `kube` answers `tt`, so
`a` is `tt`. `b` does the same. In `c`, the `wait` is forwarded through `retry`'s handler to
`timeout`. The timeout cancels `κ`, which holds `retry`'s handler frame and no finaliser, so the
cancel fires nothing, calls `kube` no more, and `c` is the default `ff`. Then `log ff`. The
runner's state is back at `ff`, so the pattern repeats. Had the timeout resumed instead, `c` would
be `tt` after two more `kube` calls, so the trace pins the cancel. The two rows of each function
are: `timeout` at `{exn, kube}` and `{kube}`, and `retry` at `{kube}` and `{wait, kube}`. The
non-vacuity argument of E1 applies at `timeout`, whose handler does not catch `le`
(`not_reconciler_of_monoCallback`, §6.1).

**The (E) properties together.**

```lean
def EProps (S) : Prop :=
  NoColouring S ∧ HigherOrderPoly S ∧ Loops S ∧ DeepHandler S ∧ NestedHandlers S ∧ Tunnel S ∧
  CancelPolicy S ∧ UnwindPolicy S ∧ StoredK S ∧ Reconciler S

/-- **System A, first pass.** -/
def Props (S) : Prop := SProps S ∧ EProps S
```

### 1.7 Outside the first pass

**A₂: binary, out of the first pass** (U22: "optional and don't get pursued unless they become
necessary for safety"). These are stated over A's contextual approximation. `CtxApprox S R t₁ t₂`
says that every closing context typed at a data answer observes no more of `t₁` than of `t₂`,
where the observations are A's `RunsTo`-style answers and observable traces.

A has no typing of contexts (`der` types terms, and `Kont` has none), so a closing context is a
term with a hole variable, which the let law binds: at every value type `T` at which both thunks
are typed (`derV [] (lam t₁) T` and `derV [] (lam t₂) T`), every term `C` with `der [T] C (F ε A)`
at a data `A`, run under every respecting runner that answers `ε`, observes of
`lets [lam t₁] C` no more than of `lets [lam t₂] C`. `LetLaw` types both programs. This needs no new
judgement, and it is the form A₂ is written in when it is taken up.

| target | statement | source |
|---|---|---|
| `Laws S` (T2) | return, operation, forwarding, the tail-resumptive law, algebraicity at linear and affine operations, capture β and η, hiding, and fusion (at a composite-handler parameter, OQ-49), each as `CtxApprox` both ways | Plotkin–Pretnar §1.2, Def. 4.5 |
| `EffDepLaws S` | Discard, Copy and Swap, each graded by the operations a row may perform | Kammar thesis (11.1), Thm 12.5 |
| `Abstraction S` (T3) | `Tunnel` (Zhang–Myers Example 1 at E6's shape, binary: `fwrap g` against `g` at every row without `li`), `RepInd`, `Encap` | Zhang–Myers Thm 1, Thm 3 |

Our signatures carry no equations (OQ-22). So absorption, `op(x, …, x) = x`, holds of no operation,
and `EffDepLaws` reduces to the pure row until equations are added.

**A₃: the erased lowering, against a fixed target and fixed references** (finding #4; L1: "Part of
18 needs to be effect handling is erased", and, as relayed, "The criterion is cost parity. A handler
never adds cost of its own"; L2; L3). It is out of the first pass, and OQ-23 (is it a theorem?)
needs the user.

```lean
namespace A.Tgt
/-- **The fixed target**: a first-order machine, defined here and not supplied by the instance.
Functions over words with numbered locals; a heap of word ranges with `alloc` and `free`; direct
calls and tail calls; structured branches (`switch`); and a `dispatch`, a switch on a code tag
followed by direct calls, which is the only indirect call.  Platform calls are io events.  No
instruction captures, saves, restores or searches a stack.  It is modelled on the backend's flat IR
(`Backend/Flat/Syntax.lean`), which is a `Tgt` program up to a fixed embedding. -/
inductive Exp | loc (i : ℕ) | lit (n : ℕ) | load (a : Exp) (k : ℕ) | prim (o : ℕ) (as : List Exp)
inductive Stmt
  | set (i : ℕ) (e : Exp) | store (a : Exp) (k : ℕ) (v : Exp) | alloc (i n : ℕ) | free (a : Exp)
  | switch (e : Exp) (cs : List (List Stmt)) | call (ds : List ℕ) (f : ℕ) (as : List Exp)
  | dispatch (ds : List ℕ) (tag : Exp) (fs : List ℕ) (as : List Exp) | tail (f : ℕ) (as : List Exp)
  | ret (es : List Exp) | io (d : ℕ) (lab op : ℕ) (arg : Exp)
structure Fn where params locals : ℕ; body : List Stmt
structure Prog where fns : List Fn; main : ℕ
/-- A target platform: a word-level runner, `(label, op, argument words) ↦ (answer words, state)`. -/
structure Platform where St : Type; s₀ : St; co : St → ℕ → ℕ → List ℕ → Option (List ℕ × St)
/-- `Run ρ p ws tr k`: a complete run of `p` under `ρ` answers the words `ws` with the io trace `tr`,
having made `k.1` allocations and `k.2` dispatches. -/
inductive Run (ρ : Platform) : Prog → List ℕ → List IoEv → ℕ × ℕ → Prop

/-- **The reference programs**: for each terminating (E) program, its hand-written, handler-free
equivalent, lowered by hand to `Tgt` — a fixed `Prog` for each choice of label numbers.  They are the
hand versions of `corpus/capture-*-hand.bc`: for E1 the pure call, a sum-returning copy of the failing
callback (a branch per call), and a direct call for the asynchronous one, whose handler resumes at once. -/
def ref : CorpusId → List ℕ → Prog
/-- Their costs, computed once (`refCost_spec` checks each by running `ref`). -/
def refCost : CorpusId → ℕ × ℕ
end A.Tgt

/-- An entry of the corpus: a terminating (E) program at its labels, its runner, and its signatures. -/
structure CorpusEntry (S : EffectSystem) where
  id : CorpusId
  term : List S.EA.Lab → S.Term
  runner : List S.EA.Lab → S.Runner
  sigs : List (List (OpSig S.Ty))
/-- E1, E1′, E2a–d, E3b, E3c, E3g, E4, E5, E6, E7a–d, E8a–b, E9a–c. -/
def corpus (S) : List (CorpusEntry S)

structure Lowering (S : EffectSystem) where
  lower  : S.Term → Tgt.Prog
  labNum : S.EA.Lab → ℕ
  labNum_inj : Function.Injective labNum
-- `dataEnc : S.Val → List ℕ`, A-defined on `DataVal`s: `unitV ↦ []`, `pair a b ↦ enc a ++ enc b`,
-- `inl a ↦ 0 :: enc a`, `inr a ↦ 1 :: enc a`; `isIo` keeps a trace's io events, and `ioEnc` maps them
-- through `labNum` and `dataEnc`; `L.tgt R : Tgt.Platform` is the runner `R` through `labNum` and
-- `dataEnc`, A-defined.

/-- The target observes exactly what the source does. -/
def LoweringCorrect (S) (L : Lowering S) : Prop :=
  ∀ R e ε A v tr, R.Respects → S.Answers R ε → S.DataTy A → S.der [] e (S.F ε A) →
    (S.RunsTo R e v tr ↔ ∃ k, Tgt.Run (L.tgt R) (L.lower e) (dataEnc v) ((tr.filter isIo).map ioEnc) k)

/-- **Zero cost**: on the corpus, each lowered program costs no more than the fixed reference. -/
def ZeroCost (S) (L : Lowering S) : Prop :=
  ∀ P ∈ corpus S, ∀ ls, S.LabelsAt P.sigs ls → ∀ ws tr k,
    Tgt.Run (L.tgt (P.runner ls)) (L.lower (P.term ls)) ws tr k →
      k.1 ≤ (Tgt.refCost P.id).1 ∧ k.2 ≤ (Tgt.refCost P.id).2
```

- **Erasure is structural.** `Tgt` has no handler or continuation instruction, so every correct
  lowering has erased handling.
- **The baseline is the hand-written equivalents.** The reference programs and their costs are
  `Tgt` constants in A, as the criterion "cost parity with the hand-written equivalents" reads. A
  lowering that keeps a handler runtime on the heap does not meet it (`not_zeroCost_of_heapRuntime`,
  to build with A₃: a handler record allocated at E4's `handle` costs one allocation, and `ref E4`
  allocates none).
- **What the instance supplies** is the lowering and the label numbering, nothing else.
- **The driven programs are not in the corpus.** `ZeroCost` reads complete runs, so the corpus
  holds the terminating (E) programs only, and leaves out E3a, E3d–f and E10, the reconciler that is
  the project's north star. Cost parity for the loop shape is therefore not stated, even as a
  target. When A₃ is taken up, it gets a per-iteration statement: the cost of one `next` of E10's
  loop (one iteration of `iterOpen`, under `Rrec`) against a fixed hand-written iteration
  `ref E10step`, and likewise for E3's loops.

**Not in A, and why.**

| left out | why |
|---|---|
| multi-shot | decision 63: "TOTALLY IGNORE MULTISHOT AS A DESIGN GOAL". `OpClass` has no unrestricted class |
| higher-order operations | "out of scope" in decision 57, read as not now. `OpSig`'s arities are value types; scoped operations would extend `OpSig` |
| a row binder, a function type, a thunk type, continuation types, a loop type | each is a mechanism. The (E) programs and schemas fix what must be typed and leave how to the instance |
| a substitution operation | §1.4: the schemas need the let law and `CallsThrough`, and loops need `LoopLaws`; a substitution field would mean something only with its equations on every former |
| determinism of the machine | a property of a machine, not of an effect system: S4 states the handler laws as joins. Ours is deterministic up to the choice of a fresh location (Core's `head_det_eff`), which the Instance uses to compute runs (§6.1) |
| "no API returns a sum for failure" | a library convention (#168), outside a calculus. What A carries is that failure is expressible as an effect at an unchanged answer type (E1, E5, E7, E8). §7 Q6 |

### 1.8 Every decided feature: the property it meets

| decided feature (strength in the brief) | the property that needs it | why the property needs it | our mechanism (§4) | non-vacuity (§6.1) |
|---|---|---|---|---|
| rows are sums of signatures, with one signature object | S1 `RowSig`, `RowAlgebra`: an (S) well-formedness requirement, not an (E) property | it gives `has`, which effect safety (S3) reads, its meaning: Kammar, "annotation effects can be identified with the effect operations". No (E) program depends on a row admitting a whole signature rather than part of one | `orowAlg Ξ` over Core's `Row.ofEff` | — (an upper bound): `rowSig_ourInst` checks it at our instance, and condition (1) of Def. 5.1 follows from it (`c1_of_rowSig`) |
| **row variables in the kernel** (decision 62: "of course we have row variables in the kernel") | **E1, E2, E6, E10's schemas** | one typing of `f`, `twice`, `compose`, `retry`, `sumGen`, `fwrap`, `timeout` serves callbacks at every row (for `fwrap`, every row without its own label, the callback and the use at the same row), the pure row unhandled among them | a rank-1 row `∀` over open rows with tail variables, Curry-style (no term former), at values (a value restriction), at `U` and `!U` (§4.2). `RowVarKernel J₂` is a lemma recording that mechanism; it is not a conjunct of done | **abstract**: `not_noColouring_of_monoCallback`, and the same at E2a, E6 and E10: an instance in which a context type fixes one callback row fails each. Concrete: `monoCallback_tier1Open`, so today's kernel fails E1, E2, E6 and E10 (`not_noColouring_tier1Open` and its siblings) |
| **handlers are deep** (decision 62) | S4's deep-resume law; **E4**; E5 and E10 (resume reinstalls the forwarded handlers) | a handler written once must catch every operation of the computation, including those after a resume | SPEC §19's `kappa` reinstalls `hnd (n, H)` | a shallow handler fails S4's deep-resume law by definition, and its run of E4 would stop at the second `yield` under a bind frame, which S3 and `OpStuck` exclude at the type `{tick}` |
| **continuations are linear or affine; discard is an explicit cancel; no forget** | **S6 `ContUse`**; **E7, E9** (abandoning typable, cleanup runs) | no continuation is used more often than it was caught, a linear one is never cancelled, and on every complete run at a data answer each is used exactly as often as it was caught; timeouts, early exit and shutdown must be expressible | SPEC §19's `kTy`: `lin` `U((B ⊸ F_Σ R) & ⊤)`, `aff` `U((B ⊸ F_Σ R) & F_Σ 1)`; the `[let]` side condition (`Row.Weak → Γ₂.Drops`); drop glue in the elaborator | R1–R4 at our machine (`not_contUse_of_der_R1` … `_R4`): any typing system over our machine that types one fails S6 |
| **cancellation is what SPEC §19 builds** (decision 62: "Whatever they do is what we decided") | S5 `Cancellation`; **E7, E8, E9c** | the traces and answers fix the policy: the finalisers fired innermost first and each once, the first outside error re-raised, the region's own suppressed, no interception | `ccatch`, `cfin`, `raise ⊥` with the cancel state | the alternative traces and answers in E7's table; at our instance the runs are computed (§6.3) |
| **divergence is an effect (codata); totality not a goal** | **E3a–g**, with S2 and `DataDiv`; the loop vocabulary's `LoopLaws`, `DriveLaws` | a div function is defined once and called anywhere, its loops sequenced, handled, fuelled and driven; a pure-row loop that diverges has a type that is not data | `Loop_Σ` codata (`ν`, `unfold`, `next` = `π₁`, `close` = `π₂`), the delay bind and `div_fuel` as library code, the runtime's driver (`RStep`'s drive phase, a context of A's, `driveF`). A calculus with `fix` would define `unfold`, `next` and `close` another way; the driver is the runtime's primitive in either (§1.3) | `not_loops_of_total`, `divInTypes_of_loops` |
| **errors are abortive operations** (`raise`; "error is a control flow effect full stop") | **E1** (the failing callback has the pure one's answer type), E5, E7, E8 | failure must live in the row, since one `f` serves both callbacks at one answer type | `raise : 1 ↠^aff 0`, abortive; `[unwind]`, `[finalise]` | trivial: an instance with no abortive operation has no `sigExn` labels |
| **nested handlers "need to work, full stop"** (K4, U5) | **E5, E10** | two effects nested in both orders, and four in the reconciler | static names per site; structural forwarding | trivial |
| **effect handling is erased** (L1–L3) | A₃ `LoweringCorrect`, `ZeroCost`, over the fixed `Tgt` and the fixed references | cost parity with the hand-written equivalents on the corpus | the backend: abortive operations become branches, answering operations calls, control operations state machines | `not_zeroCost_of_heapRuntime` (to build with A₃) |
| **multi-shot is ignored** (decision 63) | nothing | — | `J₂` is unr-free | — |
| **higher-order operations: not now** | nothing | — | — | — |
| **binary laws are optional** (U22) | A₂, stated | — | — | — |
| **no step-indexing** (decision 7) | not an A property: a property of `W`'s definition | — | `audit_W` (§5.2) | the audit's negative tests |
| **nothing breaks the borrow calculus** | B's guarantees in `Combined` (§3.5) | — | — | `not_combined_of_leak`; `not_releasedOnceReuse_staleFree` (§6.2) |

---

## 2. System B: the borrow calculus, given

System B is BoLo ([CONF], [TR]) as transcribed in `Paper/` and, at Core's machine, in `Core/`. Its
guarantees are given. B states them as Props over a typing system `J : TypingJ` and a borrow world
`M : B.BWorld`, so that they can be asked of the composite, and proves each at BoLo by citation.
"Given" means at `coreB` and `tier1`, at the restrictions listed below.

### 2.1 B's world

```lean
namespace B
/-- **A borrow world**: BoLo's Kripke world as a parameter.  It has the lend stack `σ`; the
configurations the world reaches (`TW` at Core); the run-end relation `↭`, a field (FIX-RUN-END);
the Kripke order; the stack a cell's stored payload is read at (OQ-46); and the relation.  It has
nothing of effects: no stop condition, no continuation share, nothing held by suspensions.
`I.SemWorld` extends it with those. -/
structure BWorld where
  Stk    : Type
  nil    : Stk
  Fam    : WRes → List FrameRec → Idx Stk → Prop
  Upd    : Idx Stk → Idx Stk → WRes → WRes → WRes → Prop
  Ext    : Idx Stk → Idx Stk → WRes → Prop
  payStk : Life → Stk → Stk
  val    : Bool → VTy → Idx Stk → LSub → Val → WProp
  comp   : CTy → Idx Stk → LSub → Expr → WProp

/-- Core's relation as a borrow world, its lend stack one point. -/
@[reducible] def coreB : BWorld :=
  ⟨Unit, (), fun fρ ps i => TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1, fun _ _ ρ _ π => ResU.UpdV ρ π,
   fun i i' ρ => Ext i.1 i'.1 ρ, fun _ _ => (), fun b A i δ v => vCE none b A i.1 δ v,
   fun C i δ e => cC C i.1 δ e⟩
```

B owns the definitions that its guarantees and routes read, and each reads only these fields (or no
world): `ptoMutSW`, `ptoImmSW`, `gSepW`, `gDenW`, `SemWC`, `SemW₀`, `SemW`, `FL`, `AdequateRetAt`,
`AdequateDriveAt`, `Adequate`, `ContractsW`, the bounds, the run-end laws, and the conservativity
statements `WBCore`, `ConservativeWB` and `Conservative` (which `SoundnessContractsOfFL` reads,
§5.3). A few definitions that read only these fields live in I because only I uses them (`Mono`,
`AdequateEvery`, `EmbedsNil`, `HandleCompat`); I imports B, so that breaks no import rule.

### 2.2 The guarantees

| id | guarantee | Prop (B) | printed | proved at BoLo by | status at BoLo |
|---|---|---|---|---|---|
| B0 | BoLo's programs stay typed | `ExtendsB J`, the effect-free part of `ExtendsNU J`: `J` holds today's unr-free judgements and is closed under every rule of `CDerives` but its six effect rules (below). `ExtendsNU` itself, effect rules included, stays in `I.Pins` | — | `CDerives` transcribes BoLo's rules, one constant per borrow axiom | PROVED AT σ=[] (`extendsB_tier1`, a projection of `extendsNU_tier1`, checked) |
| B1 | the fundamental property, at the judgements `J` states over Core's types (in done: `⟦J₂⟧`'s, whose types have no row `∀`, §4.2) | `FL M J` | [TR] 6.151: "If ∆; Γ ⊢ e ∶ T then ∆; Γ ⊧ e ∶ T." | `fundamentalC` (`Core/Fundamental.lean:434`); `Paper/S6_8_FundamentalProperty/Lemmas.lean:164` | PROVED AT σ=[] (`fl_core_tier1`, `fl_core_tier1NU`, checked, restated at `coreB`, §4.6) |
| B2 | adequacy | `Adequate M` | [CONF] Thm 3.2: "If ⊨ wp (e) {⌜P̂⌝} then (∅, e) →∗ (∅, v) and P̂(v) for some v"; Cor. 3.3 | `theorem32D`, `adequacyD` (`Core/Demonic.lean:292,312`) | PROVED AT A RESTRICTION (the platform with no operation, data answers: `adequateRetAt_core_none`, checked); every platform and the drive: OPEN |
| B3 | no use after free, no double free: no run is stuck, under every allocator | `Sound J`'s `SafeRuns` (the library's `Soundness`) | [CONF] 415:18: adequacy "really does characterize executions that are safe, terminating, and reclaim memory" | `adequacyD_safe`, `wpTSD_safe`; `Core/Stale.lean` (why every allocator) | PROVED AT A RESTRICTION (`soundRetAt_tier1_none`, checked) |
| B4 | leak freedom: each complete run at a data answer ends with the memory empty | `Sound J`'s `Terminates` with `Final` | [CONF] 415:23: "the discarded fragment ρ⁺ must not contain any owned cells. This is essential for the memory reclamation component of adequacy (Theorem 3.2), which insists that owned cells are freed rather than forgotten" | `adequacyD`, `reclaim` (`Core/Fundamental.lean:534`), `NoOwn` (`Paper/S5_Model/Definitions.lean:1362`) | PROVED AT A RESTRICTION (`soundRetAt_tier1_none`, checked) |
| B4′ | B3 and B4 with externs meeting their contracts | `SoundContracts J M` (§5.3) | — | B1, B2 (`soundContractsOfFL`, to build) | at `coreB`, at the restriction B2 has (`soundContractsOfFL` from `fl_core_tier1`); Core's own end-to-end form, at the stdio contract `ExternsMeet`, is `externs_every_run` (`Core/Stdio.lean:622`) |
| B5 | release exactly once, location reuse included | `ReleasedOnceReuse J M` (§2.4) | not printed: B3 and B4 read per allocation | a corollary of B3 and B4 (B4′ with externs) at the bump allocator, given the step-for-step simulation `BumpSim` (TwoRun's `run_sim` extended to block, capture, `count`, `countTry`, `boundedFix` and platform steps: OQ-43 (b) or (c)), through `releasedOnceReuse_of_bumpSim` | OPEN |
| B6 | exclusive mutable borrows | `ExclusiveB M`: every configuration the world reaches is a valid resource | [CONF] 415:21: "Conceptually, in a valid resource, every pair of aliases map to the same object and each has an immutable ancestor" | `TW.valid` (`Core/Invariant.lean:1802`) | PROVED AT σ=[] (`exclusiveB_core`, to build in `B/BoLo.lean` from `TW.valid`, since `coreB.Fam` is `TW ∧ Tagged`; the same step as the validity half of `exclusive_core`, checked) |
| B7 | lifetimes respected, at `J`'s outlives judgements over Core's types (in done: `⟦J₂⟧.out`, no row `∀`) | `LifetimeSound M J.out` | [TR] 6.60: "If ∆ ⊢ T ⊐ @a and δ ∈ ⟦∆⟧, and ρ ∈ 𝒱⟦T⟧δ then @ρ ⊐ @aδ" | `vC_outlives`, `vC_outlivesLe` (`Core/RelationFacts.lean:479,575`); `vDen_outlives` (`Paper/S6_2_NonStandardLemmas/Lemmas.lean:3620`) | PROVED AT σ=[] (`lifetimeSound_core`, checked, restated at `coreB`) |
| — | the bounds: the relation has Core's shape at each type former, and the nil slice is Core's | `WBound M` | — | Core's clauses, by unfolding | PROVED AT σ=[] (projections of checked results) |

```lean
def ExclusiveB (M : BWorld) : Prop := ∀ fρ ps i, M.Fam fρ ps i → ResU.Valid fρ
/-- The nil slice has Core's structure: configurations, order, run-end relation and payload stack
(FIX-RUN-END §2.2, the borrow fields). -/
def SliceShapeB (M : BWorld) : Prop :=
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ls ls' ρ ρ' π, M.Upd (ls, M.nil) (ls', M.nil) ρ ρ' π ↔ ResU.UpdV ρ π) ∧ (∀ b, M.payStk b M.nil = M.nil)
def WBound (M : BWorld) : Prop := SliceShapeB M ∧ ExtPre M ∧ FamEmpty M ∧ DataVals M ∧ RelShape M ∧ RelElim M
/-- **B0**: `RulesClosed J Row.NU` without its six effect conjuncts (`RC_effSub`, `RC_effPerform`,
`RC_effRaise`, `RC_effLet`, `RC_effThen`, `RC_effHandle`), with `Tier1SubNU J`.  The borrow
constants with a callback row (`withbor1U` …) are kept: at a pure callback they are BoLo's. -/
def ExtendsB (J : TypingJ) : Prop := Tier1SubNU J ∧ BorrowRulesClosed J
-- `Sound J` is the library's `Soundness J` (T1), defined in the base layer: B3 and B4 at every respecting platform
def Guarantees (J : TypingJ) (M : BWorld) : Prop :=
  ExtendsB J ∧ FL M J ∧ Adequate M ∧ Sound J ∧ SoundContracts J M ∧ ReleasedOnceReuse J M ∧
  ExclusiveB M ∧ LifetimeSound M J.out ∧ WBound M
```

So "nothing breaks the borrow calculus" is carried by `B.Guarantees` alone, B0 included. `ExtendsNU
J → ExtendsB J` is a projection, so B0 costs done nothing beyond `Pins`.

`RelShape` and `RelElim` are the library's clauses, moved unchanged. None reads a row: they cover
the borrow calculus's type formers, and `RelElim` the eliminations of `U`, `→`, `&`, the lifetime
`∀`, `ν` and `μ`.

**At which judgements.** B is stated over Core's types, which have no row `∀`. So in done, B1
(`FL M ⟦J₂⟧`) and B7 (`LifetimeSound M ⟦J₂⟧.out`) are about the judgements whose context and type
have no row `∀`; row polymorphism enters only inside derivations, as a let-bound polymorphic
function does (§4.2). Every closed program is such a judgement, so the program-level guarantees
(B3, B4, B5, and B4′ at externs of `∀`-free type) cover the whole composite. An open judgement with
a row-polymorphic value in its context, and an extern of row-polymorphic type, are outside B1 and
B4′ by this choice; the relation at those types is I's `ovalW`, and FL at them is `FLOpen`, beside
done (§4.2, §3.7).

`Sound` mentions no world, so its definition sits in the base layer, where the Instance's bridge to
A's S2 also reads it as a hypothesis (§4.1). It is B's guarantee all the same.

### 2.3 What B mentions of effects

B's statements are about Core's machine and Core's types, and both have effects.

- `Sound`, `Adequate` and `SoundContracts` quantify over platforms and over the rows a platform
  answers.
- `RelElim` covers `ν`.
- `FL` covers every judgement of `J`, effect rules included.

These are B's because "nothing breaks the borrow calculus" is a statement about **every** program
of the composite, effectful programs included ("You can't add an effect system without changing
it. They interact."). B contains no `EffectSystem`, no stop condition, no share, nothing held, and
no statement of how a row is read in the world. Those are the interaction's (§3).

### 2.4 B5: exactly-once release with content (finding #2)

- **The tautology.** `ReleasedOnceAll J` (`Statements/Soundness.lean`) assumes its conclusion.
  `NoReuse` gives at-most-once, and `Final`'s empty memory gives at-least-once. It is proved at
  every typing system (`releasedOnceAll`, checked), and `ReleasedOnceOfSound` uses neither of its
  premises `SafeRuns` nor `Terminates`. It moves to `B/Release.lean` as a **lemma about runs**,
  with its docstring saying so. It is no longer in done, and no document presents it as a
  guarantee (§5.1 lists each correction).
- **At-least-once** is B4: a complete run at a data answer ends with the memory empty, so every
  cell allocated has been released.
- **At-most-once, on runs that reuse locations**, is the statement with content. It is in done.

A permutation cannot state it. A run that reuses a location may still name that location from its
first allocation, as a dangling pointer in its term: `VTy.immReborrow` sends `.thunk _` and `.opq _`
to `.unk` (`Core/Types.lean:1452,1461`), and `Unk` holds nothing and outlives everything, so a copy
read through an `Imm` view may keep a location after its cell is freed. TwoRun's README records the
case: "A may reuse a location it still names as a dangling pointer". So B5 is stated in
`fresh_run_image`'s direction: every run is the image of a run that reuses nothing, along a map that
may send two of that run's names to one location, and is injective only on its live heap.

```lean
-- base, `Machine.lean`, restated over this branch's Core from TwoRun (`Fresh.lean`, `Sim.lean`, `Rename.lean`):
-- `Named μ e ℓ`: the heap holds ℓ, the term mentions it, or a stored value mentions it;
-- `Expr.mapLoc g`, `Val.mapLoc g`: rename every location along `g : Loc → Loc`;
-- `Heap.push g μ`: μ's cells moved along `g`, their values renamed.
/-- A run that allocates only locations no earlier configuration of it names: a bump allocator's
run.  It is fresh, and it reuses nothing. -/
def Bump {P : Platform} (cs : List (Conf P)) : Prop :=
  ∀ k ℓ, Allocated cs k ℓ → ∀ j c, j ≤ k → cs[j]? = some c → ¬ Named c.μ c.e ℓ

/-- **B5**: every complete run of a typed program is, step for step, the image of a complete bump
run.  At step `k` a map `g k`, injective on the bump run's live heap, renames the bump run's term to
the run's and pushes its heap onto the run's.  The bump run releases each cell exactly once; so the
run releases each allocation once, and a release through a name of an earlier allocation (a stale
release) would be a release, in the bump run, of a cell already released, which has no step. -/
def ReleasedOnceReuse (J : TypingJ) (M : BWorld) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) → ContractsW M Γ γ →
    ∀ cs, PRun P (init P (substAll γ e) :: cs) →
      (∀ c, (init P (substAll γ e) :: cs).getLast? = some c → Final P A c) →
      ∃ (cs' : List (Conf P)) (g : ℕ → Loc → Loc),
        cs'.length = cs.length ∧ PRun P (init P (substAll γ e) :: cs') ∧
        Bump (init P (substAll γ e) :: cs') ∧ ReleasedOnce (init P (substAll γ e) :: cs') ∧
        (∀ c, (init P (substAll γ e) :: cs').getLast? = some c → Final P A c) ∧
        ∀ k (cA cB : Conf P), (init P (substAll γ e) :: cs)[k]? = some cA →
          (init P (substAll γ e) :: cs')[k]? = some cB →
          Set.InjOn (g k) {x | cB.μ x ≠ none} ∧ cA.e = cB.e.mapLoc (g k) ∧
          cA.μ = Heap.push (g k) cB.μ ∧ cA.s = cB.s
```

- **Its externs.** They meet W's contract `ContractsW` (§5.3), as B4′'s do.
- **The machine lemma, named.**

  ```lean
  /-- **The step-for-step simulation** (base, `Machine.lean`; a lemma about the machine alone, OPEN:
  OQ-43 (b), or (c) through a binary FP).  Where a run and a bump run from the same start are related
  at step `k` by a map injective on the bump run's live heap, and both take a step, the bump run's
  step is the run's step's preimage, along the map extended at an allocation. -/
  def BumpSim : Prop
  theorem releasedOnceReuse_of_bumpSim : BumpSim → SoundContracts J M → ReleasedOnceReuse J M   -- to build
  ```

- **B5 is a corollary of B3 and B4, given a machine lemma.** (With externs, read B4′ for B3 and
  B4: it is their form at `ContractsW`.) Take a complete run of a typed program. B3 holds under
  every allocator, the bump allocator included, so the bump run from the same start is never
  stuck: wherever the given run takes a step, the bump run can take one. The
  **step-for-step simulation**, a lemma about the machine alone, says that the bump run's step is
  the given step's preimage, and extends the map `g` at an allocation. So the bump run follows the
  given run to its end, with the same length. Its last configuration is `Final`: that transfers
  along the maps (or follows from B4), and `ReleasedOnce` of the bump run is
  `releasedOnce_of_ends` (checked). The existence half comes from B3's progress, not from TwoRun's
  `run_sim` (`TwoRun/Sim.lean:253`) or `fresh_run_image` (`:274`): both take the fresh run as given
  (`hB : FreshRun …`) and relate an arbitrary run to it. Their lockstep induction is the
  simulation's shape.
- **Done rests on an open machine lemma, and this design says so.** `run_sim` is proved for runs
  with no array step and no capture step, and TwoRun does not build on this branch: every result
  there is "stated for runs with no array step", and the extension to blocks is not derived
  (`experiments/TwoRun/README.md:29-31`). The simulation B5 needs is extended to the array steps
  (`tab`, `idx`, `drop`, `split`) under a renaming of blocks, the capture steps, `count`,
  `countTry`, `boundedFix`, and the platform's steps. That is OQ-43 (b), or (c) through a binary FP.
  So done, and tier 1, exclude OQ-43 (a) for B5. U22 allows a binary fact where it is "necessary
  for safety", and no stale release is safety. Given that lemma, B5 costs nothing more than B3 and
  B4; §7 Q4 asks the user to confirm. Nothing else in done rests on that lemma: the composite
  programs' answers are stated on one run (§3.4).
- **What B5 adds to B3 and B4.** B3 and B4 hold under every allocator, so they already exclude a
  program whose outcome depends on which free location is picked. B5 adds the statement itself: a
  run which does reuse a location is, step for step, the image of a run that does not, and so
  releases each allocation once. `not_releasedOnceReuse_staleFree` (§6.2) shows that B5, unlike
  `ReleasedOnceAll`, is not a tautology: no complete bump run of `staleFree` exists. It does not
  show that B5 excludes a program B3 admits: a typing that types `staleFree` already fails B3,
  since the bump run is stuck at the second `free x`. Given the machine lemma, B5 excludes no
  typing that B3 admits.

---

## 3. The interaction

### 3.1 I's world, and FIX-RUN-END carried over

```lean
namespace I
/-- **The interaction's world**: B's world, plus what suspensions hold (`held`, OQ-9), the stop
condition (R-T1 at Core), and what a stop at a resuming operation owes its continuation (`share`,
Core's `contShare`). -/
structure SemWorld extends B.BWorld where
  held  : Idx Stk → List FrameRec × List SRec
  Stop  : List FrameRec × Idx Stk → List FrameRec × Idx Stk → Expr → Prop
  share : OpTabI (Idx Stk) → OpEntI (Idx Stk) → UInt32 → Idx Stk → Kont → (Idx Stk → Expr → WProp) → WProp

@[reducible] def coreW : SemWorld :=
  { B.coreB with held := fun _ => ([], []), Stop := fun a b _ => (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1),
    share := fun T en n i K Φ => contShare (OpTabI.down T) (OpEntI.down en) n i.1 K (fun ls t => Φ (ls, ()) t) }
```

I owns the definitions that read `Stop`, `share` or `held`: `wpGW` (whose run end is
`M.Upd i i' ρ ρ' π`, FIX-RUN-END §2.1), `ewpW`, `opTabW`, `errOkW`, `cancelTabW`, `entW`,
`rowTabW` and the transports to `coreW`.

**FIX-RUN-END, carried over unchanged in content.**

- The run-end relation is the field `Upd` (now `BWorld.Upd`).
- It is pinned to Core's `↭` only on the nil slice: `SliceShapeB`'s `Upd` conjunct, plus
  `SliceShapeI`'s `held` and `Stop` conjuncts, together the library's `SliceShape`.
- Every result of `Targets/Restricted/RunEnd.lean` moves to `I/RunEnd.lean`, under the same names:
  - `wpGW_iff_runFrame` and AT02's runs;
  - `at02_held_end`, `at02_unfolded_end` and `at02_imm_end`;
  - the witness worlds `leakW` and `carryW` with their laws;
  - `not_sliceShape_of_updTop`, `not_adequate_of_leak` and `not_updOutlives_of_opened`.
- `not_endState_of_leak` is restated as `not_combined_of_leak`.
- The run-end laws stay beside done. `UpdSeq` and `UpdReclaim` are the hypotheses of the device's
  `AdequateOfLaws`. `UpdRefl`, `UpdOwn`, `UpdFrame`, `UpdOutlives` and `UpdLendBack` are what FL's
  printed route reads at W.
- The pin's `→` half reads σ = [] as "no lend carried open anywhere". That constrains OQ-44, not
  OQ-8 or OQ-9. It stays AGREE 10 (§7 Q7).

### 3.2 I1 to I5: what done holds, and what the device holds

| | statement | in done | in the device (§3.7) |
|---|---|---|---|
| **I1** a suspension is a value of the resource world | the share closed by its handler is a value of `kTy` | A's E9 (κ stored and used after its handler returned) and E1′; `I1Prog`, a corollary at `c = .any` (`storeCancel`, `at17` typed and sound) | `I1 M` |
| **I2** capture and resume preserve the invariant | **preservation of `TW` and `TW.inv` along runs**: every configuration a W-run reaches is a typed world over the visible and the held frames | `Arises M` (and so `TW.inv` at every run end); the programs whose lends span a suspension are accepted (`Tier2Programs`, §3.4) | `StopVisible`, `ShareResume`, `FramesW`, `SpanBorrows`; the freeze binder is beside done (`FreezeBinder`, `BinderMachine`); the spanning rules, `J₂`'s mechanism for `Tier2Programs`, recorded (`spanRules_J₂`, §3.5) |
| **I3** drop finalises exactly once | a cancel runs every frozen finaliser once, innermost first, uninterceptably; what the continuation held is released | A's S5 at our instance, and E7, E9c, whose traces show each fire and end; the continuation itself is used once on every complete run at a data answer (A's S6); what it held is released by the end of every complete run (B4), once (B5); AT12 | `ShareCancel`, including the release at the cancel point; `CancelCloses` named-only (OQ-57) |
| **I4** answering effects are borrows | the borrow form of an answering body is typed by the borrow rules | `I4a` in `Pins`: a rule of the interaction the brief names (I1–I5), which decision 57 decides ("Answering effects are capability arguments and add no copies") and the provisional decisions 51 and 55 spell out (an answering `with` is a `borrow mut` of the state's cell) | `I4Typing` beside done; `I4c` binary |
| **I5** the capture laws | β, η, hiding | A's S4 deep resume (β operationally); A₂ (binary) | `I5beta` (proved at every world, checked), `AntiFrameW`, `FrameW` |

**Freeze as a binder stays available.** I2's fields are exactly what the binder acts on
(`StkAct`, the location and lifetime actions). `FreezeBinder M a` is stated at the same `M`,
beside done, together with its first check `NotVDenNaturalArises`.

### 3.3 The side conditions

| side condition | in done | the device and beside |
|---|---|---|
| P9 lifetimes | B7 `LifetimeSound M J.out`, at the typing system's own outlives judgements (OQ-28 open in `J.out`) | — |
| P10 exclusivity across the handler | B6 `ExclusiveB M`; I's `Exclusive M`, counting what suspensions hold (`TI` over the visible and held frames) | — |
| P14 well-bracketing conservativity | no conjunct. `WBCore` (P14.a, Core's runs keep their lend records) is proved (checked), independent of `J` and `M`, and is a companion lemma | `EmbedsNil` (Core's relation embeds into W at row-abortive types at the nil index; not checked against every OQ-8 clause set, §3.6); `ConservativeWB` (every index reachable from σ = [], needs `Mono`); `Conservative` (every type, A7 in full) |

```lean
def Arises (M : SemWorld) : Prop :=
  ∀ fρ ps i, M.Fam fρ ps i → ∃ ps₀ ls₀, (∀ p, p ∈ ps₀ ↔ p ∈ ps ∨ p ∈ (M.held i).1) ∧
    (∀ x, x ∈ ls₀ ↔ x ∈ i.1 ∨ x ∈ (M.held i).2) ∧ TW fρ ps₀ (rsOf ls₀) ∧ Tagged fρ ps₀ ls₀
def EmbedsNil (M : SemWorld) : Prop :=
  ∀ b A ls δ v ρ, A.AbortRows → vCE none b A ls δ v ρ → M.val b A (ls, M.nil) δ v ρ
def SliceShapeI (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔ (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls))
/-- How effect rows are read in the borrow world: the rule of the interaction. -/
def Bounds (M : SemWorld) : Prop := SliceShapeI M ∧ EffInterp M ∧ ShareMono M ∧ AdequateEvery M
/-- The world-level interface: what the world reaches, and exclusivity counting what suspensions
hold.  It reads no typing system. -/
def Interface (M : SemWorld) : Prop := Arises M ∧ Exclusive M
```

`EmbedsNil` is defined here, in I, and sits in the device (§3.6, §3.7).

### 3.4 The interaction's expressiveness, and its rejections

**Accepted, with an answer.** Each composite program is accepted at a typing system with a computed
answer: typed at a data answer, every run under the platform with no operation safe and terminating
with the memory empty, and **some** complete run answering `v`.

```lean
def AcceptedAt (J : TypingJ) (e : Expr) (A : VTy) (v : Val) : Prop :=
  J.closed e (.ret A) ∧ SafeRuns Platform.none A e ∧ Terminates Platform.none A e ∧
  ∃ cs c, PRun Platform.none (init _ e :: cs) ∧ (init _ e :: cs).getLast? = some c ∧
    Final Platform.none A c ∧ c.e = .val v
```

- **It rests on no machine lemma.** The answer is stated on one run, which the builder exhibits:
  an interpreter proved to agree with `Step1`, or the run written out. Today `v` is the answer of
  `Support`'s interpreter (`Core/EffPrograms.lean`'s `*_eval`, checked by `decide`), which has no
  theorem tying it to `Step1`, so those checks are evidence only. That **every** run answers `v`
  would follow from the fresh-run simulation that B5 needs (§2.4); `AcceptedAt` does not ask it, so
  `Accepts` does not depend on OQ-43.
- `SafeRuns` and `Terminates` are the library's `AcceptedT1` at `J`; they follow from `Sound J`.

**(E) at every tier: `CompositeT1 J`.** The existing tier-1 programs that mix borrows and effects.
Each is `AcceptedAt J e A v`:

| program | what it exercises | `v` |
|---|---|---|
| `logOutside`, `failOutside` (`Core/EffPrograms.lean`) | the answering `Log` lent as a borrow; `Fail`; both orders | `(inj₂ (), inj₂ ())`; `inj₂ ()` |
| `logInBorrow` | logging inside `borrow mut b` | `(inj₂ (), inj₂ ())` |
| `reborrowRaise` | `raise` inside a reborrow inside a borrow; both lends end | `inj₂ ()` |
| `tickAnsProg n` | a loop whose state owns the log cell | `inj₂ ()` at `n = 3` |
| `takeProg n` | early exit cancels a producer that holds a cell | `inj₂ ()` at `n = 1`, `inj₁ ()` at `n = 5` |
| `storeCancel` | κ stored in a cell, taken back, cancelled; the captured cell freed | `()` |

`AcceptedT1` proves the first three conjuncts of all of them at `tier1` (checked). At `J`, each
follows from `ExtendsNU J` with its `CDerivesNU` derivation (`d_storeCancelNU` is checked; the
others are to build, without `unr`), and from `Sound J`.

**(E) at tier 2, when `c = .any`: `Tier2Programs J`.** The programs that need a lend spanning a
resuming or cancelled suspension.

| program | survey / source | shape | `v` (the interpreter's answer, memory empty) |
|---|---|---|---|
| `at02` | #2 (Yarrow's region example, one-shot) | a cell lent `Mut` across a resumed `Foo`, then read | `inj₁ ()` (checked by `at02_eval`) |
| `at04` | #4, `v.push(do choose())` one-shot. **A stand-in** for the async read into a local buffer, not that program: the buffer is lent `Mut` and the awaited answer is written through the lend **after** the resume, by the body. The lead-axis form passes the lend **to** the operation (`read(&mut buf)`), which is OQ-56's (below, §7 Q5) | `Choose`'s answer written through the lend | `(inj₁ (), inj₂ ())` (`at04_eval`) |
| `at12` | #12, `thread::scope` with the continuation dropped | a lend spans an affine `Susp`; the handler cancels `κ`; the lend's finaliser frees the cell during the cancel | `inj₂ ()` (`at12_eval`) |
| `at17` | #17, a borrow across a perform in a movable first-class continuation | the handler moves `κ` into a cell and back, then resumes it | `inj₁ ()` (`at17_eval`) |
| **`genSelf`** (to build) | `corpus/reject/gen-self-borrow.bc`, a **generator borrowing its own state** | `handle yield {…or…} (c ← alloc tt; borrow imm c (λb. yield (*b); yield (*b)); free c)`: an `Imm` lend (6.64) spans two resumed yields | `inj₂ ()` (`tt`) |
| **`reconB`** (to build) | the operator's `reconcile(cfg: &Config, …)` (`docs/operator/README.md` §4.1) | `cfg ← alloc tt; r₁ ← borrow imm cfg (λb. resumer wait (retry (λ_. *b; wait (); *b))); r₂ ← borrow imm cfg (λb. timeout (λ_. *b; wait (); *b)); free cfg; (r₁, r₂)` with A's `retryR`, `timeoutR` at Core's encoding: an `Imm` lend spans a resumed wait inside a row-polymorphic `retry`, and a cancelled wait inside `timeout` | `(inj₂ (), inj₁ ())`, that is `(tt, ff)`: `retry`'s first attempt answers `tt`; the timeout cancels and answers its default `ff` |

`genSelf` and `reconB` use `withbor` (1)'s term `withborUE` at `withbor1UTy` (an `Imm` lend of an
owned cell), typed at a resuming row by `SpanRule1`, and read through the lend by `withload`, as
`Core/Stdio.lean`'s `write_all` reads a byte. Each is `AcceptedAt J e A v`, as above. Their
interpreter runs are to be checked by `decide`, as `at02_eval` is.
Tier 1 rejects each of the six (`not_tier2_tier1`, to build, §6.1).

- **Pending OQ-56, so not in done.** `asyncRead` is the lead-axis async read, `read(&mut buf)`,
  with the lend passed **to** the operation, so that its argument type mentions the lend's variable
  (`Mut 'x Buf`). That is OQ-56 (b) or (c). When the user chooses, it joins `Tier2Programs` at the
  chosen `Adm` (§7 Q5). Until then `at04` stands in for it, and is labelled so.
- **No option is picked.** Every program in the table has operation types closed in lifetimes, so
  it is OQ-56-neutral (`admClosedOp`).

**The rejections (the REJECT side).** These apply to us: the survey's #5, #6, #7, #8 and #13, as
`DESIGN.md` §8 reads them, each a Core term to build. #11 applies too, and is impossible by
construction (below).

| program | shape | how it is refused | in done as |
|---|---|---|---|
| AT05 | two `Mut 'h S` taken from one handler's state cell: the borrow form of an answering handler whose body uses `m` twice | static: `Mut` has no copy rule (HandlersAsBorrows `twoBlocks_refused` [PAPER]) | `I.Rejects` (inversion; D21 cost stated) |
| AT06 | a clause that writes a cell the suspended body has lent: the clause captures `c`, which was moved into the borrow | static: clauses are `!U`, so they capture only persistent values, and `c` is linear | `I.Rejects` (inversion) |
| AT07 | a continuation capturing a lend of `x`, stored past `x`'s frame (`x` freed after the borrow ends), then resumed | semantic: the resumed read uses freed memory, a stuck run. The static bound on a stored continuation is OQ-28's (`J.out`) | `rejects_at07_of_sound : Sound J → ∀ P, P.Respects → ∀ S A, DivFree S A → RowLe S P.ops → ¬ J.closed at07 (CTy.effOf S A)` (derived, to build), at the types `Sound` covers |
| AT08 | a continuation in a shared cell, read twice (moving it out and using it once is allowed: `storeCancel`) | static: `kTy` at `lin` and `aff` is neither droppable nor persistent, and an `Imm` view of a thunk cannot be forced | `I.Rejects` (inversion) |
| AT13 | `forget(k)` where `k` holds an outside loan | static: a `lin` or `aff` continuation has no weakening, and the `forget` constants are at `Imm`, `Mut`, `!` and `Unk` | `I.Rejects` (inversion) |

- **Static rejections** (AT05, AT06, AT08, AT13) are conjuncts. Where κ holds nothing they run
  safely, so only the discipline excludes them. A's S6 is that discipline's universal form for
  continuations (§1.5); these four are the composite's concrete cases, with cells.
- **The semantic rejection** (AT07) is a lemma derived from `Sound J`. It shows that B's guarantees
  have teeth: the program would run badly, so done excludes it whatever OQ-28 decides, at the
  types `Sound` covers, a data answer on a row a respecting platform answers (AGREE 7's scope).
  AT07 handles its own operation and reaches no platform operation, so its run is stuck under every
  platform. At a type outside that scope (an answer that is not data, or a row with an operation no
  platform answers) `Sound` says nothing, and neither does the lemma.
- **Survey #11** (a resumption applied under a different handler, Xie et al.'s `opevil`: "Reject,
  or impossible by construction") is impossible by construction. S4's deep-resume law reinstalls
  κ's own handler wherever κ is resumed (`resume (capture l H K) w` joins
  `handle l H (plug K (ret w))`), so the resumed computation's operations of `l` reach `H`, never a
  handler around the resumer.

```lean
def Accepts (J : TypingJ) (c : RowClass) : Prop := CompositeT1 J ∧ (c = .any → Tier2Programs J)
def Rejects (J : TypingJ) : Prop :=
  (∀ C, ¬ J.closed at05 C) ∧ (∀ C, ¬ J.closed at06 C) ∧ (∀ C, ¬ J.closed at08 C) ∧ (∀ C, ¬ J.closed at13 C)
```

### 3.5 The combined theorem, done, and tier 1

```lean
/-- What the composite's typing must contain: today's rules and outlives judgements, and the
answering effects' borrow form.  The mechanisms of `J₂` are not pins: A's schemas require effect
polymorphism and `Accepts` requires the tier-2 programs, and `RowVarKernel J₂` and `SpanRulesAt ⟦J₂⟧`
record how our kernel meets them (§4.2, below). -/
def Pins {RF : Inst.RowForm} (J : Inst.OurTyping RF) (Adm : OpAdm) (c : RowClass) : Prop :=
  AdmExtends Adm ∧ ExtendsNU ⟦J⟧ ∧ OutExtends ⟦J⟧.out ∧ I4a ⟦J⟧ Adm c
/-- The spanning rules at a class: none beyond today's unwinding constants at `.abortive`, and
`Tier2Pinned` (the six spanning rules at `RowSpan Adm`) at `.any`.  Not a pin: `spanRules_J₂` is a
recorded lemma. -/
def SpanRulesAt (J : TypingJ) (Adm : OpAdm) : RowClass → Prop
  | .abortive => True
  | .resumeOnce => SpanRules J (fun Δ x o => Adm Δ x o ∧ (o.abort = true ∨ o.q = .lin))
  | .any => SpanRules J Adm

def Combined (RF : Inst.RowForm) (J : Inst.OurTyping RF) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  (∀ Ξ, Inst.AdmEff Ξ → A.Props (Inst.ourInst RF Ξ J)) ∧ B.Guarantees ⟦J⟧ M.toBWorld ∧ Bounds M ∧
  Interface M ∧ Pins J Adm c ∧ Accepts ⟦J⟧ c ∧ Rejects ⟦J⟧

theorem done : Combined orowRF J₂ W admClosedOp .any      -- with `audit_W` passing (§5.2)

theorem spanRules_J₂ : SpanRulesAt ⟦J₂⟧ admClosedOp .any  -- recorded: `J₂`'s mechanism, by construction
```

- **Done** is fixed at `admClosedOp`, R-CLOSEDOP, until OQ-56 is chosen. `AdmExtends` bounds every
  admissibility below by it, and a wider `Adm` makes `Combined` stronger, so when the user chooses
  OQ-56's option, done is restated at that `Adm` (§7 Q5).
- **Done is fixed at `orowRF`**, the minimal tail-variable row form, until OQ-13's remaining
  question (the row form) is answered, in the same way: `J₁` and `J₂` are built over it, and done
  is restated at the chosen form.
- **Done holds A at every admissible effect context** (`∀ Ξ, AdmEff Ξ → …`), so the effect algebra
  holds for whatever effects a program declares; a fixed Ξ would say it only of the test labels.
- **Tier 1** is `Combined orowRF J₁ coreW admClosedOp .abortive`.
- **The spanning rules are a mechanism, recorded.** No decision names tier 2's six rules: the
  decision record's concurrency entry T4 (`04-decisions.md` §8) says only "T1 (no lend spans a
  suspension) is kept at tier 1", and that "self-referential suspension is tier 2". What done requires is the property: `Tier2Programs` accepted at `c = .any`,
  with `ExtendsNU` (today's programs stay typed), and `not_tier2_tier1` (§6.1) shows that tier 1
  fails it. So a tier-2 kernel that types the same programs by other rules meets done, and
  `spanRules_J₂` records how `J₂` does it, as `rowVarKernel_J₂` records the row `∀`.
- **`I4a` stays a pin**, because it is not a mechanism for another property: it is I4, one of the
  interaction's rules (I1–I5) that the brief names, in the form decision 57 decides ("Answering
  effects are capability arguments and add no copies"; §3.2).

**Corollaries** (to build, generic):

- `soundnessContractsAR_of_combined : Combined RF J M Adm c → EmbedsNil M → SoundnessContractsAR ⟦J⟧`.
  The SPEC's externs, at Core's fixed contract: from `SoundContracts` and
  `contractsW_of_meets : EmbedsNil M → (∀ s ∈ Γ, s.ty.AbortRows) → ExternsMeet Γ γ → ContractsW M Γ γ`
  (the `→` direction only; review [14]). `EmbedsNil` is beside done (§3.6), so this is a corollary
  of done together with the device's `EmbedsNil`, not of done alone.
- `i1Prog_of_combined`, `i2Prog_of_combined : Combined RF J M Adm .any → …`, which hold at
  `c = .any` only (review [16]).
- `effSafe_core_of_combined : Combined RF J M Adm c → EffSafe ⟦J⟧`. This is Core's form of P2,
  through `effSafeOfFL` restated over `FamEmpty ∧ AdequateEvery` (review [17]).
- `combined_prog : Combined RF J M Adm c → (∀ Ξ, AdmEff Ξ → A.Props (ourInst RF Ξ J)) ∧
  Sound ⟦J⟧ ∧ ReleasedOnceReuse₀ ⟦J⟧ ∧ ExtendsB ⟦J⟧ ∧ Pins J Adm c ∧ Accepts ⟦J⟧ c ∧ Rejects ⟦J⟧`,
  where `ReleasedOnceReuse₀` is B5 at closed programs (`Γ = []`, and `ContractsW M [] []` holds at
  every world). Every conjunct of it reads no world.

**Where the library's end state went.**

| `DESIGN.md` `EndStateAt`/`Guarantees` conjunct | new home |
|---|---|
| the parameter `RF` of `EndStateAt` | a parameter of `Combined`, fixed at `orowRF` in done until OQ-13's remaining question is answered; the effect context Ξ, which `EndStateAt` left implicit in `RowAlgSafe`'s "at every effect context", is quantified over `AdmEff` in the A conjunct |
| `RowAlgSafe RF`, `RowLink RF` | A's S1 (`RowAlgebra`) at `ourInst RF Ξ J`; `RowLink` is the Instance's lemma that proves `RowSig` and `SubClosed` there |
| `AdmExtends`, `I4a`, `ExtendsNU`, `OutExtends` | `I.Pins`; B0, the effect-free part of `ExtendsNU`, also in `B.Guarantees` (`ExtendsB`) |
| `Tier2Pinned` | **out of done**: `J₂`'s mechanism for `Tier2Programs`, recorded as `spanRules_J₂` (`SpanRulesAt … .any`) |
| `AcceptsTier2` | `I.Accepts` at `.any`, with answers on one run, extended by `genSelf` and `reconB` |
| `Soundness J`, `SoundnessContracts J` | B3/B4 (`Sound`); B4′ (`SoundContracts`, externs as an explicit hypothesis, #7); `SoundnessContractsAR` a corollary of done with the device's `EmbedsNil` |
| `ReleasedOnceAll J` | **out of done**: a lemma about runs (#2); done holds B5 `ReleasedOnceReuse`, restated in the fresh-run direction |
| `EffSafe J` | A's S3 at `ourInst` (Core's form a corollary) |
| `NoInterception J`, `FinaliserOrder J` | A's S5 at `ourInst`; Core's syntactic `NoInterception` and run shapes are the Instance's route to it (§4.1) |
| `WLaws M` | B's `WBound` (`SliceShapeB`, `ExtPre`, `FamEmpty`, `DataVals`, `RelShape`, `RelElim`) and I's `Bounds` (`SliceShapeI`, `EffInterp`, `ShareMono`, `AdequateEvery`) in done; **`Mono` to the device** (#5) |
| `FL M J`, `Adequate M` | B1, B2 |
| `I1 M` | the device; done holds E9, E1′ and `I1Prog` (a corollary) |
| `I2 M J.out Adm c` | `Arises` in done; `StopVisible`, `ShareResume`, `FramesW`, `SpanBorrows` to the device (#5) |
| `I3 M` (`ShareCancel`) | the device (#5), with the release at the cancel point; done holds A's S5 and S6, E7, E9c, and B4/B5 by the end of every complete run |
| `I5 M` | the device; done holds S4's deep resume |
| `LifetimeSound M J.out` | B7 |
| `Exclusive M` | B6 (`ExclusiveB`) and I's `Exclusive`, both in done |
| `P11 M` | the device (`HandleCompat`, `RedLaws`); done holds S4 |
| `ConservativeWB M` | **changed**: `ConservativeWB`, at future indices, needs `Mono`, so it moves to the device (review [18]); `EmbedsNil`, at the nil index, also moves there, since it has not been checked against every OQ-8 clause set (§3.6). Done holds no conservativity statement; `WBCore` is a proved companion lemma (§7 Q7) |

**What tier 1 needs beyond what is checked** (review [15]):

- `J₁` itself, with the relation at its open types (`ovalW`, whose clause at `U(∀ρ:k. C)` is the
  intersection over the admissible instances) and `FLOpen M J₁`, through which `FL M ⟦J₁⟧` is
  proved (§4.2);
- A's (S) at `ourInst orowRF Ξ J₁`, at every `AdmEff Ξ`: the Instance's bridges (§4.1), each
  hypothesis discharged in I (§4.5):
  - `MachShape` (with Core's contexts marked with the driver's phase, the named frames and the
    driver frame among them, `AppLaw`, `LoopLaws` and `DriveLaws` at our encodings) and `LetLaw`
    (`CDerives.bind` after `CDerives.ret`);
  - `HandlerSem` from `Head`'s effect steps (`Paper/S3_Dynamics/Definitions.lean`) in both phases,
    with `Kp` the `seq` frame at `[finalise]`;
  - `EffSafe` from `effSafe_tier1` (in I) for programs in the main phase, and from Core's
    `EffSafeDrive` for driven ones (§4.1; to build, through `effSafeDriveOfFL`);
  - `Safety` from `Sound` with `platformOf`, `runs_platformOf` and `runs_platformOf_drive` (in I);
  - `NoIntercept` and `UnwindOrder` from `noInterception_tier1`, `CancelRun` and `UnwindRun`, with
    the finaliser's context under a cancel ending in `cfin` (§4.1), in both phases;
  - `ContUse`, by subject reduction at Core's typing of configurations, or by the logical relation
    with a ghost token per continuation (OPEN; §1.5, §7 Q9);
- A's (E) at `ourInst J₁`: each program typed and its run computed (by an interpreter proved to
  agree with `Step1`, or written out, and Core's determinism up to allocation; §6.1); each schema
  by `[allR-E]` at the row in question, and each `CallsThrough` by the β-steps of `hof`, `twice`,
  `timeoutR` and `fwrap`;
- `Adequate coreB` at platforms with operations and for the drive (the library's second wave);
- B5 at tier 1, through `releasedOnceReuse_of_bumpSim`, which needs `BumpSim` (OQ-43, §2.4);
- `I4a ⟦J₁⟧`, re-derived at `J₁` from `i4a_tier1`;
- `CompositeT1` with NU derivations, and its answers on one run;
- `Rejects` at `⟦J₁⟧`.

**The tier-1 reduction, kept.** The library proved that its tier-1 end state follows from two open
statements (`status_tier1End_of`: `Adequate coreW` and `FinaliserOrder tier1`). That reduction is
kept as a restricted result at today's kernel and Core's world, `status_tier1Core_of` (to build,
§4.6). Every conjunct of `Combined orowRF tier1Open coreW admClosedOp .abortive`, except A's (E)
properties (which today's kernel fails at E1, E2, E6 and E10, §4.3), `ContUse` (OPEN), and
`Accepts` and `Rejects` (whose derivations and inversions are to build), together with the device at
`coreW`, follows from three open statements: `Adequate coreB`, the cancellation bridge
(`FinaliserOrder tier1`, through which the Instance's bridges give A's S5), and, for B5, `BumpSim`.
The rest is proved, or is a to-build lemma with no open hypothesis (the bridges of §4.1,
`EffSafeDrive` through `effSafeDriveOfFL`).

### 3.6 OQ-8 and OQ-9 stay unpicked (finding #5)

A conjunct of done may read the world only where every option of OQ-8 (where the future-world
quantifier sits) and of OQ-9 (open frames handed to a continuation: carried (a), ghost-ended (b),
or R-T1 (c)) can meet it. Each conjunct the library had in done that constrains an option moves to
the device. Done then keeps only statements that no world can make true by choosing an option.

| conjunct | the option it constrains | where it goes |
|---|---|---|
| `Mono` (Kripke monotonicity of `val` along `M.Ext`) | excludes OQ-8's binder-clause placement unless `EwpMono` holds, and nothing proves that | device |
| `ShareResume`, `ShareCancel` (the share's resume and cancel at every `M.Ext`-future) | fix Core's placement of the future-world quantifier (OQ-8); the argument that the binder-clause option also has them was circular through `Mono` | device |
| `StopVisible` | forces every lend that spans a stop into `held`, a representation choice (AGREE minor finding; OQ-9) | device |
| `FramesW` (6.64 and 6.65 at W in the printed shape, at resuming tables) | decides OQ-9 for (a) if (b) cannot give that shape | device |
| `SpanBorrows` (the spanning rules' semantic cases) | follows from `FL` once `J` holds the spanning rules; as a stand-alone conjunct it fixes how each case is proved | device |
| `I1`, `I5`, `P11`'s `HandleCompat` | rule-shaped at W, with the share and `ewpW` on both sides | device |
| `ConservativeWB` (future indices) | needs `Mono` | device |
| `EmbedsNil` (Core's relation into W at row-abortive types, at the nil index) | not checked: under any clause set that puts a future-world quantifier in a value clause (at `U`, with `contShare` and `KapRel`, as Core's `vCE` does at `U`; or at `∀` and `⊸`, the binder clauses), `M.val` at a thunk or arrow type at the nil index already ranges over every W-future of nil, so `EmbedsNil` there asks Core's value to be valid at indices whose stack is not nil, which is `ConservativeWB`'s content at that type | device |

**Why `EmbedsNil` left done.** It replaced `ConservativeWB` on the ground that it reads only the nil
index. That holds of `M.val`'s clauses only where they carry no future-world quantifier of their
own. The SPEC's externs, which `EmbedsNil` serves (`contractsW_of_meets`), are functions, at exactly
the types where a clause may carry one. Whether each of OQ-8's six clause sets can meet it at
row-abortive types has not been checked, so it moves beside done with `ConservativeWB`, and
`SoundnessContractsAR` (the SPEC's externs at Core's contract) becomes a corollary of done together
with `EmbedsNil` (§3.5). Done's externs are at W's contract (`ContractsW`, #7), which needs no
embedding. The difference from the conjuncts kept below is the direction: `LifetimeSound`,
`Exclusive` and `Arises` read `val` and `Fam` as upper bounds (what a related value or a reached
configuration holds), which a quantifier inside a clause can only make easier to meet; `EmbedsNil`
is a lower bound (Core's values must be related), which such a quantifier makes harder.

**Neutral, so kept in done.**

- `Arises`, `Exclusive`, `ExclusiveB` and `LifetimeSound` read `Fam`, `held` and `val`, and no
  `Upd` (FIX-RUN-END §3, Layer 1b).
- `EffInterp` reads `M.comp` through the fixed `ewpW` and the field `share`, and any placement
  defines `share`.
- `RelShape` and `RelElim` are at the same index, with no `M.Ext` quantifier.
- `ShareMono` holds at either placement, because the share is monotone in what it owes.
- `AdequateEvery`, `FL` and `Adequate` are statements every option can meet.
- `SliceShapeB` and `SliceShapeI` pin only the nil slice. Their `→` halves constrain OQ-44, and
  that stays AGREE 10.

No conjunct of done states `↭`'s borrow content off the nil slice. So OQ-9 (a) with the cell kept,
(a) with the cell unfolded, and (b) all remain possible worlds (FIX-RUN-END §4).

### 3.7 The proof device, beside done

```lean
/-- A route to the world conjuncts of done.  W meets it when its proof follows the printed route at
Core's placement.  Not done. -/
def Device (M : SemWorld) (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  Mono M ∧ ShareResume M ∧ ShareCancel M ∧ StopVisible M ∧ FramesW M c ∧ SpanBorrows M J.out Adm c ∧
  I1 M ∧ I5 M ∧ P11 M ∧ ConservativeWB M ∧ EmbedsNil M
```

(`ConservativeWB M` gives `EmbedsNil M` wherever `Ext` is reflexive, which `ExtPre`, in done, says;
that is how `embedsNil_core` is derived from `conservativeWB_core`. The device names both, since
done holds neither.)

- Beside it: the run-end laws (§3.1); `FreezeBinder`, `BinderMachine` and `CombinedBinder`;
  `Conservative`; `I4Typing`; `CancelCloses` (named-only, OQ-57); `FLOpen M J`, FL at the open
  judgements through `ovalW`, the route to B1 at `⟦J⟧` (§4.2).
- **The routes, generic:**
  - `soundnessOfFL` (checked, in B);
  - `soundContractsOfFL` (to build, in B: `FL → Adequate → SoundContracts`, with no
    `Conservative`, #7);
  - `soundnessContractsOfFL` (checked, in B, since `Conservative` is B's; kept as an alternative
    route);
  - `effSafeOfFL` (restated over `FamEmpty ∧ AdequateEvery`, in I);
  - `AdequateOfLaws` (stated, OPEN; its hypotheses `WLaws`, `ShareResume`, `UpdSeq`,
    `UpdReclaim`).

---

## 4. The Instance: our calculus as one instance of A

### 4.1 `ourInst`: A's fields from Core

`ourInst (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : A.EffectSystem` is parametric in the row
form `RF` (OQ-13's remaining question; `orowRF` is the minimal tail-variable form, over which `J₁`
and `J₂` are built) and in an effect context `Ξ` that gives each name its signature (review [19]).
Done asks A's properties at every admissible Ξ (§3.5):

```lean
/-- The effect contexts done ranges over: no resuming `unr` operation (`Row.NU`, decision 63),
operation types closed in lifetimes (as SPEC §19 says operation types are), and at least two names
at each signature the (E) programs use, so that each `ForLabels` has its labels. -/
def AdmEff (Ξ : EffCtx) : Prop := Ξ.NU ∧ Ξ.ClosedLife ∧ Rich Ξ
```

Where `RF` and Ξ are fixed by the context, `ourInst J` abbreviates `ourInst RF Ξ J`: in the bridges
and `platformOf` below, and in §6.1's lemmas, which are stated at every `AdmEff Ξ` (and the bridges
at every `RF`).

| A field | ours |
|---|---|
| `EA` | `RF.alg Ξ` (`orowAlg Ξ` at `orowRF`); `Lab` is the names `n ≠ 0` that Ξ declares |
| `sig n` | `Ξ n`, with `(q, A, B) ↦ ⟨A, B, cls⟩`: `abortive` when `B = 0 ∧ q ≠ lin` (Core's `OpSig.abort`), else `linear` or `affine` by `q` |
| `has ε n i` | `Row.Has (RF.den Ξ ε η) n i` at every environment, through `RowLink`: the operations of ε's closed prefix |
| `Ty`, `CTy`, `F`, data formers | the open types `OVTy`, `OCTy` (§4.2), `F := OCTy.effOf`; `UnitT := unit`, `ZeroT := zero`, `Tensor`, `Sum` |
| `DivFree (F_S A)` | `A` is closed data: Core's reading (decision 35), stronger than `DataDiv` |
| `Val`, `Term` | Core's `Val`, and `Expr × Phase`, with the library's `Phase.main` or `Phase.drive` (`Targets/Defs/Runs.lean`). Every former but `drive` builds a `main` term from its arguments' expressions; `drive` sets the phase to `drive`. A drive is a property of the whole configuration, as `RStep`'s phase is: a drive under another former is dropped, and no typed program has one there |
| formers | Core's: `lam` is `.lam`, `force V` is `V` itself (every A-thunk is a function, and Core's `forceE` at an arrow type is the value), `app M V` is `bindE (.val V) (.app M↑ (.var 0))` (A-normal, as Core's `[app]` asks), `bind` is `bindE`, `split` is `.letpair`, `case` is `.case`; `perform` and `raise` are `performE`/`raiseE (opArgE n i V)`; `handle n (hnd r cs) M` is the run-time frame `hndE (hndVal n r (clausesV cs)) M`; `resume k w` is `κ (inj₁ ()) w` (A-normal); `cancel k` is `κ (inj₂ ())`; `thenT M N D` is `thenE N D↑ M` (`D` shifted under the finaliser's unit binder) |
| `unfold f g s`, `next l`, `close l` | `unfoldV (loopEffBody S A 1)` at the coalgebra `λs. ⟨f s, g s⟩` and the state `s`, the loop value of `Loop_S A 1`; `next l` is `nextE l`, `π₁`; `close l` is `l (inj₂ ())`, `π₂` |
| `drive M` | `(M.1, drive)`. Its steps are `RStep`'s: `run` (the machine's steps, in the drive phase), `again` at `inj₂ l` (a `top` step to `nextE l`), and, at `inj₁ a`, a `top` step back to the main phase answering `a` (where the library stops, at `FinalDrive`). SPEC §11, §14 |
| `Kont`, `plug`, `kcomp`, the frames | **Core's `Kont`, every frame of it, marked with a phase**: `(K, ph)`. `plug (K, ph) (M, p)` is `(K[M], ph)` when `K` is not `□` (a frame builds a `main` term, as the formers do, unless it is marked `drive`), and `(M, ph ⊔ p)` at `□`, with `main ⊔ p = p` and `drive ⊔ p = drive`. `hole` is `(□, main)` and `driveF` is `(□, drive)`. `kcomp (K₁, p₁) (K₂, p₂)` is `(K₁ ∘ K₂, p₁ ⊔ p₂)` when `K₁` is `□`, and `(K₁ ∘ K₂, p₁)` otherwise, with Core's composition (`plug_cmp`). The four other named frames are Core frames marked `main`: `bindF N` is `appR (.lam N) □` (so `plug (bindF N) M = bindE M N`), `appF V` is `appL □ V`, `handleF n H` is `appR (hnd (n, H)) □` (Core's `hndE`), and `thenF N D` is `appR (ubind (λx.N, λ_.D↑)) □` (Core's `thenE`). The others include `seq` (where `[finalise]` runs a finaliser), `cfin` (where a cancel runs one) and `ccatch` (the canceller's) |
| `catches K n`, `unwindClear K`, `fins K` | read off the Core part: `K.HasHnd n`; `K` has no `ubind` and no `cfin` frame (`ccatch` stops only the reserved name `0`, which no label is); the finalisers of `K`'s `ubind` frames, innermost first (`Kont.fins`), each read as an A-term (the frame's `λ_. D↑` at `()` is `D`). So `catches K n = false ∧ unwindClear K` is Core's `K.Catches n = false` at every label `n ≠ 0` |
| `capture n H K`, `cancelOf n H K` | `⟨kappa n H K, _⟩` and `cancelOf` (`Targets/Defs/Effects.lean`) at `K`'s Core part |
| `Conf`, `step` | memory, term and phase; `Step1` under every allocator, labelled `fire D` at `ufin`/`ufinC` (with `D` the A-level finaliser: the frame's `λ_. D` at `()`), `finEnd` at `cfret`/`cferr`, and `tau` otherwise; and the driver's `top` steps |
| `derV Γ V A`, `der Γ e C` | `J` at the empty lifetime context and the row context that declares the free row variables of `Γ` and `C` at `RowCon.any`, `Γ`'s slots all live. A drive-phase term is typed only at `Γ = []` and at a loop sum `F_S (A ⊕ U(Loop_S A 1))`, the type of its current step |
| `Runner` ↔ `Platform` | `runnerOf : Platform → A.Runner (ourInst J)`, and `platformOf R ε : Platform`, restricted to ε (below) |

**The instance's contexts are Core's, marked with the driver's phase.** Every context a run builds
is a Core `Kont`, those Core's finaliser rules build included, marked `drive` exactly when the
program is driven. `KontLaws` holds by computation: the hole law and composition by cases on
whether `K₁` and `K₂` are `□` (in each case both sides are `K₁[K₂[M]]` at the same phase), the named
frames by `rfl`, and `catches`, `unwindClear` and `fins` on the Core part. `Congr` is `Step1`'s
closure under `Kont.plug` in either phase: a non-`top` step keeps the phase, and `RStep.run` lifts
every machine step into the drive phase.

**The driver's mark is where the laws rebuild.** A frame other than `□` drops the phase of what it
holds, so every term A's laws put under a former (`handle l H (plug K …)`, `thenT (plug K …) N D`,
`resume κ w`, `perform …`) is a `main` term whatever `K` is. A driven configuration therefore matches
a law's left-hand side only with the driver's mark in the outer context that the right-hand side
reuses: `K` itself in `RStep.io` (whose answer is `plug K (ret w)`), `K₀` in S4 and S5's cancel,
and in an unwind trace `K₀` or the part `K₂` outside the stopping frame, which the trace carries
into the finaliser's context `kcomp (kcomp K₀ K₂) Kp`. So
the laws relate driven configurations to driven ones, as the machine does. A continuation captured
inside a driven program is the Core continuation of its Core part (`capture` reads `K`'s Core
part).

The finaliser laws then have their contexts; re-checked against the step rules, in either phase:

- **S4's finaliser law.** `[finalise]` (`ufin`, labelled `fire D`) steps
  `K₀[ubind (λx.N, λ_.D↑) K[raise p]]` to `K₀[(λ_.D↑) (); raise p]`, and one β-step reaches
  `K₀[D; raise p]`, which is `plug (kcomp K₀ Kp) D` at `Kp := seq □ (raise p)`. `Kp` has no
  handler, `ubind` or `cfin` frame, and at `()` Core's `seq` rule steps `K₀[(); raise p]` to
  `K₀[raise p]`.
- **`NoIntercept`, from the cancel run's shape (`CancelRun`).** From `K₀[cancelOf n H K]` the cancel
  raise passes `K`'s handlers (no handler is named `0`) to `K`'s innermost `ubind`. `ufinC`
  (`fire D`) and one β-step put `D` under `Kf := K₀ ∘ ccatch □ ∘ handleF n H ∘ K_out ∘ cfin s □`,
  where `K_out` is what is left of `K` outside that frame. `D` runs alone there (unique
  decomposition, `plug_decomp`) until `cfret` (`finEnd none`) or `cferr` (`finEnd (some …)`, the
  error kept by `errNext`, which is `keep (Region n K)`); then the cancel raise goes on to the next
  `ubind`. The last step is `cancel` or `creraise`, which is `Answered K₀`. Core's `CancelOrder`
  states this shape on complete runs; `NoIntercept` asks it on every prefix, by the same
  induction. `NoInterception ⟦J⟧` (typed terms hold no `ccatch`, `cfin` or handler named `0`) makes
  the cancel's own frames the only such frames.
- **`UnwindOrder`, from `UnwindRun`.** `Kp` is the `seq` frame again. A raise escaping `D` stands
  under `K₀ ∘ K₂ ∘ Kp ∘ K'`, which `PendTrace.superseded` follows; `UnwindRun`'s `Kd` is
  `Kp ∘ K'`.

**`AppLaw`.** `app M V` is `bindE (.val V) (.app M↑ (.var 0))`, whose first step is the β-step of the
let, to `.app M (.val V)`, which is `plug (appF V) M`. That step changes no store.

**`LoopLaws`, `DriveLaws`.** `next (unfold f g s)` reaches `f s` by `unfold`'s administrative steps
(`hN_steps`, `etaN_obs`, `Core/Nu.lean`), under the `[let]` frame that maps `inr s'` to the loop value
at `s'` (`node_ok`, SPEC §19 *As built*). That frame catches nothing and holds no finaliser. `close`
is the same at `π₂`. `DriveLaws` are `RStep.again` and the final `top` step at `inj₁ a`, each the
only step of its configuration; the driver's non-`top` steps are `Congr` at `driveF`, which is
`RStep.run`. These are to build.

**`platformOf R ε`, restricted to ε.** `A.Runner.answers` is an arbitrary predicate, and
`Platform.ops` is a finite row with `uniq`, `nz` and `total`, so a runner is mapped to a platform only
at a row:

```lean
/-- The platform that answers the operations of ε's closed prefix that `R` answers, through `R`'s
co-operations.  `R.Respects` and `Answers R ε` give `Platform.Respects`. -/
def platformOf (R : A.Runner (ourInst J)) (ε : (ourInst J).EA.Eff) : Platform
theorem platformOf_respects : R.Respects → (ourInst J).Answers R ε → (platformOf R ε).Respects
/-- Runs coincide on a program the platform runs safely: a run under `R` is a run under
`platformOf R ε` while its io events are at ε's operations, and `SafeRuns` under `platformOf R ε` rules
out an io event at any other operation (that configuration would be stuck there). -/
theorem runs_platformOf : SafeRuns (platformOf R ε) A e →
    ((ourInst J).RPath R ((ourInst J).rinit R (e, .main)) q ↔ PRunOf (platformOf R ε) e q)
/-- The same at the drive phase, against the library's drive from the drive phase: `RStep.run` (a
`PStep`, the platform's answers included) for our machine and io steps, `RStep.again` for our `top`
step at `inj₂ l`, and our last `top` step at `inj₁ a` added where the library stops (`FinalDrive`).
`SafeDriveFrom P A M` is `SafeDrive` from `(init P M, .drive)`. -/
theorem runs_platformOf_drive : SafeDriveFrom (platformOf R ε) A M →
    ((ourInst J).RPath R ((ourInst J).rinit R (M, .drive)) q ↔ DRunOf (platformOf R ε) M q)
```

`safety_of_sound` uses them at each row: `Sound ⟦J⟧` at `platformOf R ε` gives `SafeRuns` there, and
`runs_platformOf` carries it to `R`.

**The drive phase, re-checked.** A's io step at a driven configuration `plug (kcomp driveF K)
(perform l i v)` is `RStep.run` of `PStep.plat` at `K`'s Core part, so a driven loop's platform
operations are answered under the driver in both semantics, and `runs_platformOf_drive` holds by
the same induction as `runs_platformOf`. `Safety`'s driven clause then comes from `Sound ⟦J⟧`'s
`SoundDriveAt` by a stuttering simulation. A typed driven program `drive M` has `M` at
`F_S (A ⊕ U(Loop_S A 1))` (§4.1's typing of a drive-phase term). The library's program
`e := M to x. case x of inl a ⇒ return (doneL a) | inr l ⇒ return l`, where `doneL a` is a loop
whose first observation answers `inj₁ a`, returns a loop, so `SoundDriveAt` gives
`SafeDrive P A e`. Its drive runs `M`'s steps in the main phase where ours runs them in the drive
phase, and takes the `case`, the return and `RStep.start` (and, at `inl a`, `doneL a`'s first
observation) where our driver takes one `top` step. Every configuration our run reaches is so
matched by one the library's run reaches, and a stuck one would be matched by a stuck one, which
`SafeDrive` excludes; `FinalDrive`'s `DataVal A a` gives the answer clause. To build, with
`safety_of_sound`.

**Effect safety in the drive phase.** Core's `EffSafe` covers main-phase runs from the empty memory.
A driven run reaches `nextE l` at a loop value the run produced, which `EffSafe` does not cover, so
the bridge also reads Core's drive form, stated in base and proved by the semantic route:

```lean
/-- **P2 for driven programs**: every configuration the drive of a typed driven program reaches is
a finished drive, takes a step, or stops at an operation of the row. -/
def EffSafeDrive (J : TypingJ) : Prop :=
  ∀ M (S : Row) A, Row.NU S → J.closed M (CTy.effOf S (.sum A (.thunk (CTy.loopEff S A .unit)))) →
    ∀ rc, Relation.ReflTransGen (RStep Platform.none) (init _ M, .drive) rc →
      FinalDrive Platform.none A rc ∨ (∃ rc', RStep Platform.none rc rc') ∨ StopsIn S rc.1.e
-- `effSafeDriveOfFL` (I, to build): FL M J → FamEmpty M → AdequateEvery M → EffSafeDrive J,
-- `effSafeOfFL`'s proof with the relation at `U(Loop_S A 1)` (`RelElim` at `ν`) for each `nextE l`
```

Two to-build items carry the D21 cost:

- **`handle` at run-time form.** `handle` uses the run-time form so that `KontLaws` holds by `rfl`.
  Its typing then needs the value-clause form of `[handle]`, derived from `effHandle` by
  substituting the clause values, which are persistent (clauses are `!U`, so a clause captures
  only persistent variables, as `retryP`'s captures its policy). Its cost is the substitution
  lemma for `CDerives` at persistent values.
- **The drive phase.** A drive-phase term is typed only at `[]` and a loop sum, and a drive under
  another former is dropped (the former builds a `main` term), so the only driven programs are
  `drive M` at the top, as in the library. Its safety is the library's `SoundDriveAt`, through the
  stuttering simulation above, and its effect safety is `EffSafeDrive`.

**Bridges** from Core's statements to A's (to build, in `Instance/Bridges.lean`). Each takes a base
statement as a hypothesis, so none needs B:

- `machShape_ourInst`, `letLaw_ourInst J` (the latter from `CDerives.bind` after `CDerives.ret`:
  the closed value is typed in the all-dead split of `Γ` by `CDerives.insert_dead`, and a returned
  value's row is not weak, so `[let]`'s side condition is void);
- `rowAlgebra_ourInst` (from `orowAlg_laws`, `orowAlg_safe`, `rowLink_orowRF`);
- `safety_of_sound : Sound ⟦J⟧ → A.Safety (ourInst RF Ξ J)` (through `platformOf`,
  `runs_platformOf`, `runs_platformOf_drive` and the stuttering simulation to `SoundDriveAt`);
- `effSafe_of_core : EffSafe ⟦J⟧ → EffSafeDrive ⟦J⟧ → A.EffSafe (ourInst RF Ξ J)`;
- `handlerSem_ourInst` (from `Head`'s `hret`, `hop`, `hunwind`, `uthen`, `ufin`, Core's `seq` rule
  and `kappa`'s administrative steps, in either phase);
- `noIntercept_of_core : NoInterception ⟦J⟧ → A.NoIntercept (ourInst RF Ξ J)` (with the cancel run's
  shape above, in either phase);
- `unwindOrder_of_core` (from `UnwindRun`, in either phase).

Beside them, `det_ourInst` (from `plug_decomp` and `head_det_eff`): a step that allocates nothing is
the only step its configuration has. It is a lemma of our instance, not an A property; §6.1 uses it
to compute runs.

`I/Restricted/InstanceProps.lean` discharges their hypotheses with B's theorems (§4.5).

### 4.2 Types and typing systems

- **What the library already has.** `TypingJ`'s judgement carries a row context
  (`Judgment := RowCtx → LifeCtx → (RowEnv → Ctx VTy) → Expr → (RowEnv → Jdg) → Prop`). Core's
  `VTy` and `CTy` have no row-variable former, so a type that mentions row variables is the family
  of its closed instances, and `SemW` reads a judgement at a row context as every admissible
  instance on the same erased term. A derivation may therefore be polymorphic in the row context's
  variables (`tier1` and `tier1NU` hold at every admissible instance). Within one derivation,
  though, a variable of the context has one type at each environment: one let-bound function is not
  used at two rows in one body. E1, E2, E6 and E10 need exactly that.
- **`OVTy`, `OCTy`: the open types.** These are Core's formers over the row form's effects, with a
  row variable as a row's tail, and a computation former `OCTy.allR (ρ : RVar) (k : RowCon) (C)`
  for the row `∀`, which the family representation cannot express.
  - `den η : OVTy → VTy` instantiates the row variables. It is defined at `∀`-free types, where it
    gives the library's families.
  - The relation at `U(∀ρ:k. C)` is the intersection over admissible instances on the same term:
    `SemW`'s reading of a row context, moved into a type. It is sound because rows are erased, so
    the term is the same at every instance. Affect has such types ("type and row polymorphic types
    ∀𝛼 . 𝜏 and ∀𝜃 . 𝜏", §3.3). It is I's, since it reads the Instance's types and B's world:

    ```lean
    /-- The relation at an open value type, in a borrow world: at a `∀`-free type, `M.val` at its
    instance under `η`; at `U(∀ρ:k. C)`, related at `U(C[ε/ρ])` for every row `ε` admissible at `k`,
    on the same value. -/
    def I.ovalW (M : B.BWorld) (b : Bool) : Inst.OVTy → Idx M.Stk → RowEnv → LSub → Val → WProp
    /-- FL at the open judgements of `J`, through `ovalW` and its computation counterpart.  Beside
    done: the route by which `FL M ⟦J⟧` is proved, since a derivation may use `∀` inside. -/
    def I.FLOpen (M : B.BWorld) (J : Inst.OurTyping) : Prop
    theorem I.fl_of_flOpen : FLOpen M J → FL M ⟦J⟧          -- to build
    ```
- **`OurTyping RF`** is a judgement `Θ; Δ; Γ ⊢ e : j` over the open types of the row form `RF`,
  with its outlives judgements `out`. `tier1Open`, `J₁` and `J₂` are at `orowRF`.
- **`⟦J⟧ : TypingJ`**, the reading that B and `Pins` see: `⟦J⟧ Θ Δ Γ e j` holds when `J` has a
  derivation of `Θ; Δ; Γ' ⊢ e : j'` whose conclusion's types `Γ'` and `j'` are `∀`-free and denote
  `Γ` and `j` (at every `η ⊨ Θ`, `den η Γ' = Γ η` and `den η j' = j η`). The derivation may use `∀`
  inside: a let-bound polymorphic function is internal to it. So `⟦J₂⟧` holds of every closed
  program of the composite, E1, E2, E6 and E10 included, and B's `Sound ⟦J₂⟧` and `FL M ⟦J₂⟧` cover
  them. What `⟦J⟧` leaves out, by choice, is an open judgement whose context or type has a row
  `∀`: B1 and B7 in done are at `∀`-free judgements, and B4′ takes externs at `∀`-free types
  (§2.2). `FLOpen` states FL at the rest, beside done.
- **`tier1Open`** is the library's `tier1NU` lifted to the open types: a judgement holds only at
  `∀`-free types, where it is `tier1NU` at their families. It is today's kernel, unr-free. Its row
  variables are those of the row context only.
- **`J₁`**, the tier-1 instance (to design and build), is `CDerivesNU`'s rules over open rows plus
  the row-`∀` rules, at `U` and at `!U`:
  - `[allR-I]`: `Θ, ρ:k; Γ ⊢ V : U C`, `ρ` not free in `Θ` or `Γ`, and `V` a λ-value (the value
    restriction), give `Θ; Γ ⊢ V : U(∀ρ:k. C)`; and the same with `!U` on both sides;
  - `[allR-E]`: `Θ; Γ ⊢ V : U(∀ρ:k. C)` and `Θ ⊢ ε : k` give `Θ; Γ ⊢ V : U(C[ε/ρ])`; and the same
    with `!U` on both sides.

  Both are Curry-style: no term former, since rows have no run-time content. It has no spanning
  rules beyond today's unwinding constants.
- **The linear context, checked at E1 and E2a.** `hof` is closed, so `bangThunkV` (promotion over
  the empty, persistent context) gives `[] ⊢ hof : !U(U(1 → F ρ bool) → F ρ bool)` at `Θ = ρ:any`,
  and `[allR-I]` at `!U` gives `!U(∀ρ. U(1 → F ρ bool) → F ρ bool)`. That type is persistent, so
  `Ctx.SplitP.dup` gives each of `uses`' three occurrences of `f` its own copy. Each use is `var`,
  then `[allR-E]` at `!U` at its row (`0`, `{exn}`, `{wait}`), then `bangE`, `force` and `[app]`.
  E1′ is the same at `{wait}` and `0`. In E2a, `twice` uses `h` and `g` twice each, so its type is
  `!U(∀ρ. !U(U(1 → F ρ bool) → F ρ bool) → !U(1 → F ρ bool) → F ρ (bool ⊗ bool))`: both arguments are
  `!U`, which `f` (after `[allR-E]`) and the closed callbacks (by `bangThunkV`) are. `compose`,
  `retryP`, `sumGen`, `fwrap`, `timeoutR` and `retryR` are closed and promoted the same way. Those
  that handle a label of their own (`retry`, `sumGen`, `fwrap`, `timeout`) bind `ρ` at a kind whose
  `adm` excludes it, as `[handle]`'s "`n` not in `Σ`" asks; that is why their schemas are
  `PolyUseLacks` and `PolyUseOpen`. `fwrap` is at `!U(∀ρ ∌ li. U(1 → F ρ bool) → F ρ bool)`: its
  callback and its use are at the same `ρ` (`PolyUseLacks`), and its handler's label appears in
  neither, as in Zhang–Myers' `∀α. (N → [N]α) → [N]α`. E10's `timeoutR` is at
  `!U(∀ρ ∌ wait. U(1 → F (wait ⊙ ρ) bool) → F ρ bool)` and `retryR` at
  `!U(∀ρ ∌ exn. !U(1 → F (exn ⊙ ρ) bool) → F ρ bool)`: `retry` calls its body twice, once from its
  clause, which captures only persistent values, so the body is `!U`, as `twice`'s arguments are.
  Each of their four uses instantiates `ρ` only, and every callback is a thunk over persistent
  variables (the let-bound functions) and closed code, so it is promoted (§1.6).
- **`J₂`**, the tier-2 instance (to design and build), is `J₁` plus `SpanRules` at `Adm`.
- **`RowVarKernel J`, a recorded lemma.** Decision 62's mechanism is that `J` is closed under
  `[allR-I]` and `[allR-E]`. It is not a conjunct of done: done requires effect polymorphism through
  A's schemas, and `rowVarKernel_J₂ : RowVarKernel J₂` (by construction) records how our instance
  meets it.

  ```lean
  def RowVarKernel (J : OurTyping RF) : Prop := RC_allRI J ∧ RC_allRE J
  ```

  `spanRules_J₂ : SpanRulesAt ⟦J₂⟧ admClosedOp .any` records `J₂`'s spanning rules the same way
  (§3.5).

- **Rank.** The (E) programs and schemas need rank 1: let-bound functions, used at several rows,
  with open rows `l ⊙ ρ`, each function at one answer type. No (E) program needs polymorphism over
  value types: E10's bodies all answer `bool` (§1.6), and E3f types `hof` at a div callback by a
  typing of its own (decision 35's specialization). Rank-n stays OQ-13's question (§7 Q2).

### 4.3 Core is the tier-1 instance without the row `∀`

`ourInst orowRF Ξ tier1Open` is Core today, at each `AdmEff Ξ`. The Instance supplies the bridges,
and I discharges them with B (§4.5), so the statements below are I's, and are not proved in the
Instance. Once the bridges and discharges are built, `ourInst orowRF Ξ tier1Open` meets:

- every (S) property of A, with S2 at the restriction B2 has (the platform with no operation) until
  adequacy is proved at every platform and for the drive (§2.2), S3 in the drive phase once
  `EffSafeDrive tier1` is proved (§4.1), and S6 OPEN (§1.5);
- the (E) properties that need no polymorphism: E3 (E3c's `divF` and E3f's `hof` are each used at
  one type), E4, E5, E7, E8 and E9;
- every B guarantee that the library proves at `coreB`, at the restrictions of §2.2.

It fails E1, E2, E6 and E10, which is why done needs `J₁`'s row variables:
`monoCallback_tier1Open` (Instance) and `not_noColouring_of_monoCallback` (A) give
`not_noColouring_tier1Open` (I, with `EffSafe` discharged), and the same at E2, E6 and E10 (§6.1). It
also fails the tier-2 programs (`not_tier2_tier1`), which is why tier 2 needs more rules; `J₂`'s
spanning rules are how ours meets them (`spanRules_J₂`, recorded).

So **tier 1 is `J₁`**: today's rules with row variables, and no spanning. Tier 1 and tier 2 are
`Combined` at `J₁` and `J₂`. Today's results are restricted instances of tier 1, at `∀`-free types.
This is a consequence of putting polymorphism in A's (E). §7 Q1 asks the user to confirm it.

### 4.4 Optional borrow-derived routes (never requirements)

"There might be a way to get some effect properties we want by leaning on borrow properties but
it's not necessary." Recorded here as possible realisations:

| A property | borrow route | evidence |
|---|---|---|
| S3 effect safety, E6 no accidental handling | handlers as lends: an answering handler lends a capability for its body's extent, so effect safety becomes an outlives check (survey A2: "effect safety *is* a lifetime theorem") | `HandlersAsBorrows`: `translate_typed`, `handle_is_shift`, `effect_safety` [PAPER]; `SecondClass`: `handleAt_compatC` [Core σ=[]] |
| S5 finalisation, and S6 where κ holds resources | linearity: B4's empty final memory and B5 count every cell a cancelled continuation held | `reclaim`, `adequacyD`; `storeCancel`, `takeProg` |
| zero cost of answering operations | I4: an answering effect is a borrow, so a direct call | `i4a_tier1` (checked) |

### 4.5 Every proved result, and its new home

The library at `938d280` has 464 theorems: 459 in `Restricted/*` and `Status.lean`, and 5 in
`Defs/*`. Every one keeps its statement and proof unless §4.6 lists it. A result whose proof uses a
B theorem to establish an A property, or a property of the composite, lives in I.

| file (count) | theorems | new home | note |
|---|---|---|---|
| `Restricted/Acceptance.lean` (4) | `at02_eval`, `at04_eval`, `at12_eval`, `at17_eval` | `I/Programs.lean` | `Tier2Programs`' runs (evidence until the runs are exhibited) |
| `Restricted/AcceptedT1.lean` (14) | `flag_data`, `err_data` | `Base/Data.lean` | data facts, no B |
| | `acceptedT1_prog`, `acceptedT1_progC`, `acceptedT1_logOutside`, `acceptedT1_failOutside`, `acceptedT1_reborrowRaise`, `acceptedT1_nLogOutside`, `acceptedT1_nFailOutside`, `acceptedT1_logInBorrow`, `acceptedT1_tickProg`, `acceptedT1_takeProg`, `acceptedT1_storeCancel`, `acceptedT1_tickAnsProg` | `I/Restricted/CompositeT1.lean` | every one is `acceptedT1_of_derives`, which rests on `soundRetAt_tier1_none` (B). `CompositeT1` at `tier1`; `prog`, `progC`, `nLogOutside`, `nFailOutside`, `tickProg` are Core's encodings of A-level programs, evidence for E7, E5 and E3 |
| `Restricted/Answering.lean` (21) | `sIdx_zero_succ`, `sIdx_succ`, `sIdx_at_zero`, `var_shift`, `shift_closed0`, `forceE_var_shift`, `absurdE_shift`, `withPair_shift`, `hndTerm_shift`, `deadP_prepend`, `deadP_insert`, `splitP_prepend`, `splitP_insert`, `soloP_prepend`, `soloP_insert`, `live_insert`, `CDerives.insert_dead`, `deadP_selfSplit`, `deadP_splitKill`, `meetOfDomL_not_mentions`, `i4a_tier1` | `Base/Support.lean` (the shift, context and `insert_dead` lemmas); `I/Restricted/Answering.lean` (`i4a_tier1`) | `I4a` at `tier1`, abortive rows |
| `Restricted/Composition.lean` (11) | `models_nil`, `gDenW_nil`, `semWC_of_FL`, `comp_of_FL`, `soundRetAt_of_FL`, `soundDriveAt_of_FL`, `soundnessOfFL`, `gDenW_of_meets`, `soundnessContractsOfFL`, `soundnessContractsOfFLWB`, `effSafeOfFL` | `B/Routes.lean` (the first eight, and `soundnessContractsOfFL` as an alternative route, which reads `Conservative`, now B's); `I/Routes.lean` (`soundnessContractsOfFLWB`, `effSafeOfFL`) | the first nine are restated at `BWorld`, and `soundnessContractsOfFLWB` (over `EmbedsNil`, I's) and `effSafeOfFL` (over `FamEmpty ∧ AdequateEvery`) over their new hypotheses (§4.6) |
| `Restricted/CoreLaws.lean` (49) | `dataB_rename`, `dataB_subst`, `data_inst`, `dataB_cl`, `dataB_noMut`, `vC_data_mp`, `vC_of_dataVal`, `vC_data` | `Base/Data.lean` | — |
| | `sliceShape_core` | split: `sliceShapeB_core` (B), `sliceShapeI_core` (I) | the conjunction is kept as `sliceShape_core` in `I/RunEnd.lean` |
| | `extPre_core`, `famEmpty_core`, `dataVals_core`, `relElim_core`, `relShape_core`, `relLaws_core`, `fl_core_tier1`, `fl_core_tier1NU`, `lifetimeSound_core` | `B/BoLo.lean` | B1, B7, `WBound` at `coreB` (restated from `coreW`, §4.6) |
| | `effInterp_core`, `shareMono_core`, `arises_core`, `exclusive_core` | `I/Restricted/Core.lean` | `Bounds`, `Interface` at `coreW`. `exclusiveB_core` (B6) is not derived from `exclusive_core`: it is B's, proved in `B/BoLo.lean` from `TW.valid`, the same step |
| | `mono_core`, `stopVisible_core`, `shareResume_core`, `handleCompat_core` | `I/Device.lean` | device at `coreW` |
| | `conservative_core`, `conservativeWB_core`, `wbCore` | `B/BoLo.lean` | their definitions are B's (`B/Conservativity.lean`); the first two restated at `coreB`, same proof (`vC_local`); `wbCore` reads Core alone, a companion lemma of tier 1 (P14.a), not a conjunct. `embedsNil_core` (I, `I/Device.lean`, the device at `coreW`) is derived from `conservativeWB_core` and `extPre_core` |
| | `admExtends_closedOp`, `rowSpan_abortive_iff_unwind` | `I/Pins.lean` | — |
| | `coreW_upd`, `wpGW_of_wpG_nil`, `updRefl_of_core`, `updOwn_of_core`, `updSeq_of_core`, `updReclaim_of_core`, `updFrame_of_core`, `updOutlives_of_core`, `updMutBack_of_core`, `updImmBack_of_core`, `updLendBack_of_core`, `updRefl_core`, `updOwn_core`, `updSeq_core`, `updReclaim_core`, `updFrame_core`, `updOutlives_core`, `updLendBack_core` | `B/RunEnd.lean` (the `upd*` laws are B's: `Upd` is a `BWorld` field; `coreW_upd` is stated at `coreB`); `wpGW_of_wpG_nil` in `I/RunEnd.lean` (it reads `Stop`) | beside done; restated at `BWorld`/`coreB` (§4.6) |
| `Restricted/Corollaries.lean` (10) | `typedSound_of_soundness` | `B/Routes.lean` | — |
| | `nu_susp`, `d_performerNU`, `d_hrSNU`, `d_clSNU`, `d_storeCancelNU` | `Instance/Restricted/Programs.lean` | `CompositeT1`'s `storeCancel` at `CDerivesNU`: typing only |
| | `i2Prog_of_endState`, `i1Prog_of_endState`, `p8a_of_endState`, `endState_prog` | §4.6 | restated for `Combined`, or retired |
| `Restricted/EffectSafety.lean` (6) | `opPlug_no_step`, `stop_irreducible`, `arun_rest_irr` | `Base/Machine.lean` | used by `OpStuck` at our instance |
| | `adequateEvery_core` | `I/Restricted/Core.lean` | `Bounds` at `coreW` |
| | `wlaws_core` | `I/Device.lean` | `WLaws` is the device's bundle; §4.6 |
| | `effSafe_tier1` | `I/Restricted/InstanceProps.lean` | statement unchanged; **proof re-written**: `effSafeOfFL` is restated over `FamEmpty ∧ AdequateEvery` (§4.6), so the proof becomes `effSafeOfFL _ _ fl_core_tier1 ⟨famEmpty_core, adequateEvery_core⟩` (`I/Routes`, `B/BoLo`, `I/Restricted/Core`), in place of `… wlaws_core`. With `EffSafeDrive tier1` (to build) and `effSafe_of_core` (Instance) it gives `A.EffSafe (ourInst orowRF Ξ tier1Open)` |
| `Restricted/Handlers.lean` (7) | `arun_first`, `wpGW_strip`, `plug_not_post`, `redLaws_of_mono`, `opTabW_mono_core`, `redLaws_core`, `p11_core` | `I/Device.lean` | P11 is the device's |
| `Restricted/Interface.lean` (23) | `wpGW_mono`, `wpGW_step`, `ewpW_fold`, `ewpW_unfold`, `ewpW_step`, `tableI_down_mono`, `tableI_down_abortive`, `opTabW_core_empty`, `resuming_abortive_empty` | `I/World.lean` | — |
| | `i5beta`, `mutView_core`, `i1_core`, `mutFrameUW_core`, `immFrameUW_core`, `mutFrameW_core_abortive`, `immFrameW_core_abortive`, `framesW_core_abortive`, `spanBorrows_core_abortive`, `i2_core_abortive`, `i3_core`, `antiFrameW_core`, `frameW_core`, `i5_core` | `I/Device.lean` | `I2` is the device's bundle; its `Arises` part is in done (`arises_core`) |
| `Restricted/NoInterception.lean` (19) | `okE_sound`, `okE_app`, `okE_lam`, `okE_travK`, `okE_travO`, `okE_travR`, `okE_selfV`, `okE_foldImmV`, `okE_foldOwnV`, `okE_foldReuseV`, `okE_mapV`, `okE_nodeV`, `okE_unfoldV`, `okE_forceE_var`, `okE_withPair`, `okE_withborUE`, `okE_of_derives`, `models_empty`, `noInterception_tier1` | `Instance/Restricted/NoInterception.lean` | the syntactic route to A's `NoIntercept`; it reads Core's `NoInterception` (base) and no B |
| `Restricted/NonVacuity.lean` (10) | `platformNone_respects`, `platformPing_respects`, `rowSpan_failSig`, `rowSpan_fooSig`, `rowSpan_suspSig`, `resuming_fooSig`, `resuming_suspSig`, `d_forgetBody`, `i4a_witness`, `d_ansRun_witness` | `I/NonVacuity.lean` | witnesses for the hypotheses of `I4a`, `Pins` and the device |
| `Restricted/Release.lean` (9) | `not_occ_vac`, `getElem?_pred`, `rise_between`, `fall_between`, `releasedOnce_of_ends`, `init_vacant`, `final_vacant`, `releasedOnceOfSound`, `releasedOnceAll` | `B/Release.lean` | lemmas about runs; their docstrings say that `ReleasedOnceAll` is a tautology (#2). `releasedOnce_of_ends` gives B5's `ReleasedOnce` of the bump run |
| `Restricted/RowAlg.lean` (22) | `rowEq_refl`, `rowEq_symm`, `rowEq_trans`, `rowEq_equiv`, `rowEq_append`, `rowEq_of_eq`, `find_nil`, `find_ofEff_zero`, `ofEff_wf`, `find_ofEff_other`, `rowEq_lift_absorb`, `closedRowAlg_laws`, `closedRowAlg_safe`, `orow_comp_none`, `orow_comp_some`, `orow_ext`, `orowAlg_laws`, `orowAlg_safe`, `rowAlgSafe_orowRF`, `closedRowAlg_lawsSafe`, `orowRF_den`, `rowLink_orowRF` | `Instance/Rows.lean` | `rowAlgebra_ourInst` uses them |
| `Restricted/RunEnd.lean` (73) | all 73: `wpGW_iff_runFrame` … `not_stop_imm_of_stopVisible` | `I/RunEnd.lean` | FIX-RUN-END's checks and witness worlds; `not_endState_of_leak` restated (§4.6) |
| `Restricted/Soundness.lean` (9) | `every_alloc_of_wpTS`, `no_infinite_of_wpTS`, `row_nil_of_le`, `pstep_none`, `psteps_none`, `psteps_of_steps`, `adequateRetAt_core_none`, `soundRetAt_tier1_none` | `B/BoLo.lean` | B2, B3, B4 at the restriction (`adequateRetAt_core_none` restated at `coreB`) |
| | `acceptedT1_of_derives` (with the definition `AcceptedT1`) | `I/Restricted/CompositeT1.lean` | rests on `soundRetAt_tier1_none` |
| `Restricted/Transport.lean` (18) | `idx_unit`, `wpGW_core`, `ewpW_core`, `opTabI_down_some`, `opTabW_core`, `opTabW_core_down`, `errOkW_core`, `cancelTabW_core`, `rowTabW_core`, `ptoMutSW_core`, `ptoImmSW_core`, `gSepW_core`, `gDenW_core`, `semWC_core`, `semW₀_core`, `wpGW_core_eq`, `ewpW_core_eq`, `ptoMutSW_core_eq` | `B/World.lean` (`ptoMutSW_core`, `ptoImmSW_core`, `ptoMutSW_core_eq`, `gSepW_core`, `gDenW_core`, `semWC_core`, `semW₀_core`, `idx_unit`, restated at `coreB`); `I/World.lean` (the rest) | — |
| `Restricted/Typing.lean` (104) | the 48 `rc_*_tier1`, the 48 `rc_*_tier1NU`, `rulesClosed_tier1`, `rulesClosed_tier1NU`, `tier1Sub_tier1`, `tier1SubNU_tier1`, `extends_tier1`, `extendsNU_tier1`, `extendsNU_tier1NU`, `outExtends_core` | `Base/Typing.lean` | `Pins` at tier 1; `extendsB_tier1` (B0, `B/BoLo.lean`) is a projection of `extendsNU_tier1` |
| `Restricted/Unwind.lean` (7) | `twoFrames_fins`, `raiseE_subst`, `raiseFin_steps`, `unitFin_steps`, `two_frame_steps`, `two_frame`, `one_frame` | `Instance/Restricted/Unwind.lean` | Core's two-frame unwind; evidence for `unwindOrder_of_core` and for E8b |
| `Status.lean` (43) | `status_*` | the new `Status.lean`, each re-pointed to its re-homed theorem | the nine about restated or retired statements are re-pointed, and the rows whose statement types change under the `coreW → coreB` and `SemWorld → BWorld` restatements are listed, in §4.6 |
| `Defs/*` (5) | `isVal_renameLoc` (`Binder`); `size_shift` (`Programs`); `ctxOutlivesJ_core`, `unwindJ_core`, `CDerivesNU.toCDerives` (`Typing`) | `B/Binder.lean` (the machine half); `Base/Programs.lean` (with `Expr.size` and `capPass`, which use it); `Base/Typing.lean` | — |

**The import check, file by file.** Each B and Instance file, what it holds, and what it imports.
None imports an I file. The three places where the previous draft broke that rule are marked.

| file | holds (from) | imports |
|---|---|---|
| `B/World.lean` | `BWorld`, `coreB`, `Idx`, `ptoMutSW` … `SemW`, the transports at `coreB` (`Defs/World.lean`, `Restricted/Transport.lean`) | base, `Core` |
| `B/Guarantees.lean` | `BorrowRulesClosed`, `ExtendsB`, `FL`, `Adequate*`, the bounds, the `Upd*` laws, `LifetimeSound`, `ExclusiveB`, `SliceShapeB`, `WBound`, `ContractsW`, `SoundContracts`, `ReleasedOnceReuse`, `releasedOnceReuse_of_bumpSim`, `Guarantees` | `B/World`, base |
| `B/Conservativity.lean` | `WBCore`, `ConservativeWB`, `Conservative` (`Statements/Conservativity.lean`; **moved from I**, since `SoundnessContractsOfFL` reads `Conservative`) | `B/World`, base, `Core` |
| `B/Routes.lean` | `SoundnessOfFL`, `SoundnessContractsOfFL`, `SoundnessContractsAR`, `soundContractsOfFL`, the B routes of `Restricted/Composition.lean`, `typedSound_of_soundness` | `B/Guarantees`, `B/Conservativity`, base |
| `B/Release.lean` | `ReleasedOnceOfSound`, `ReleasedOnceAll`, `Restricted/Release.lean` | base |
| `B/RunEnd.lean` | `coreW_upd` (at `coreB`), the `upd*` lemmas | `B/Guarantees` |
| `B/BoLo.lean` | B's guarantees and bounds at `coreB`, `conservative_core`, `conservativeWB_core`, `wbCore`, `soundRetAt_tier1_none`, and `exclusiveB_core` from `TW.valid` (**not from I's `exclusive_core`**) | `B/Routes`, `B/RunEnd`, `B/Conservativity`, base, `Core`, `Paper` |
| `B/Binder.lean` | `BinderMachine`, the machine half of `Defs/Binder.lean` | base |
| `Instance/Rows.lean` | the row forms and `Restricted/RowAlg.lean` | A, base |
| `Instance/Types.lean`, `Instance/Typing.lean` | `OVTy`, `OCTy`, `OurTyping`, `tier1Open`, `J₁`, `J₂`, `⟦·⟧`, `RowVarKernel` | `Instance/Rows`, base |
| `Instance/Core.lean` | `AdmEff`, `ourInst`, the phase-marked contexts, the encodings, `runnerOf`, `platformOf`, `runs_platformOf`, `runs_platformOf_drive`, `det_ourInst` | A, `Instance/Typing`, base |
| `Instance/Bridges.lean` | the hypothesis-taking bridges of §4.1 | `Instance/Core`, base |
| `Instance/Restricted/NoInterception.lean` | `Restricted/NoInterception.lean` (it reads base's `NoInterception` and Core's typing only) | base |
| `Instance/Restricted/Unwind.lean` | `Restricted/Unwind.lean` (base's `UnwindRun`, `Kont.fins`) | base |
| `Instance/Restricted/Programs.lean` | `nu_susp`, `d_performerNU`, `d_hrSNU`, `d_clSNU`, `d_storeCancelNU` (typing derivations only) | base, `Core` |
| `Instance/Binary.lean` | the binary laws and abstraction over Core (`Statements/Handlers.lean`'s T2 half, `Statements/Abstraction.lean`); the `CtxEquiv`, `thunkF`, `Obs`, `AnsImpl`, `ctlForm` and `clausesV` they read are base's (**moved from I**) | base |
| `Instance/ZeroCost.lean` | `LowClass`, `Statements/ZeroCost.lean` | base |
| `Instance/NonVacuity.lean` | the inversions, `monoCallback_tier1Open`, the witnesses R1–R4, the positive (E) runs | `Instance/Core`, A |

**New, in I** (to build): `I/Restricted/InstanceProps.lean` holds every A property discharged at
our instance through B: `effSafe_tier1` (moved), `effSafeDrive_tier1` (from `effSafeDriveOfFL`),
`effSafe_ourInst_tier1Open`, `safety_ourInst_tier1Open_none` (S2 at the platform with no operation,
from `soundRetAt_tier1_none`), `not_noColouring_tier1Open`, `not_higherOrderPoly_tier1Open`,
`not_tunnel_tier1Open`, `not_reconciler_tier1Open` (each from `monoCallback_tier1Open` and
`effSafe_ourInst_tier1Open`), and, when `J₁` is built, the same at `J₁`. `I/Restricted/Tier1Core.lean`
holds the kept tier-1 reduction, `Tier1Core` and `status_tier1Core_of` (§4.6).

`Targets/Checks/RunEnd.lean` is **untracked and not imported**, so it is not part of the library.
Its 17 theorems are the pre-fix check against a fixed `↭`. Each has a same-named successor in
`Restricted/RunEnd.lean`, restated against the field (FIX-RUN-END §0, §8). This design neither
moves nor deletes it. Removing it is the builder's choice, when told.

### 4.6 Retired and restated statements, and every definition's home

**Restated with the same content at the new structure** (to build):

| old | new | reason |
|---|---|---|
| `EndStateAt`, `EndState`, `Guarantees`, `EndStateBinder` | `Combined`, `done`, `B.Guarantees`, `CombinedBinder` | the architecture |
| `EndStateAt J M Adm RF` (its `RF` explicit, Ξ implicit in `RowAlgSafe RF`'s "at every effect context") | `Combined RF J M Adm c`: `RF` a parameter, fixed at `orowRF` in done until OQ-13's remaining question is answered, as `Adm` is fixed at `admClosedOp`; A's properties at every `AdmEff Ξ` | so that `A.Props (ourInst RF Ξ J)` elaborates, and says the effect algebra holds for whatever effects a program declares (§3.5); `Tier1`, `combined_prog` and every corollary take the same binding |
| `Tier1End` (`RowAlgSafe orowRF ∧ RowLink orowRF ∧ WBCore ∧ I4a tier1 … ∧ Guarantees tier1 coreW …`) | `Tier1 := Combined orowRF J₁ coreW admClosedOp .abortive` | the architecture. **`WBCore` is dropped from the conjunction**: it is proved (`wbCore`), independent of `J`, and kept as a companion lemma; `RowAlgSafe`/`RowLink` become S1 at `ourInst` |
| `endState_prog` | `combined_prog` | — |
| `i1Prog_of_endState`, `i2Prog_of_endState` | `i1Prog_of_combined`, `i2Prog_of_combined` at `c = .any` | review [16] |
| `not_endState_of_leak` | `not_combined_of_leak` | — |
| `status_tier1End_of` (`Adequate coreW → FinaliserOrder tier1 → Tier1End`, proved) | **kept as a restricted reduction**, `status_tier1Core_of : Adequate coreB → FinaliserOrder tier1 → BumpSim → Tier1Core` (to build, below); beside it `status_tier1_of`, whose hypotheses are the tier-1 list of §3.5 | `Tier1` needs `J₁` and more, so the full reduction has a long list; the restricted one keeps the library's result in the new vocabulary, with B5's machine lemma added since B5 now has content |
| `effSafeOfFL` | `EffSafeOfFL` over `FamEmpty ∧ AdequateEvery` in place of `WLaws` | done no longer holds `Mono` (review [17]); the old proof uses only those two. `effSafe_tier1`'s proof changes with it (§4.5) |
| `soundnessContractsOfFLWB` | `EmbedsNil` in place of `ConservativeWB` | its proof reads only the nil index |
| `I2` as a conjunct of done | `Arises` in done; `I2` (unchanged) in the device | #5 |
| `ConservativeWB` in done | `ConservativeWB` and `EmbedsNil` in the device; done holds no conservativity statement | `ConservativeWB` needs `Mono` (review [18]); `EmbedsNil` is not checked against OQ-8's clause sets (§3.6) |
| `Tier2Pinned` in done | `spanRules_J₂`, a recorded lemma | a mechanism for `Tier2Programs`, which done requires (§3.5) |
| B0 (in `ExtendsNU`, in the pins) | `ExtendsB` in `B.Guarantees` as well | so that B's guarantees carry B0 (§2.2) |
| `ReleasedOnceReuse J` (a statement, not proved; per-step permutations of a no-reuse sibling) | `ReleasedOnceReuse J M` (§2.4): every complete run the image of a complete bump run, along per-step maps injective on the bump run's live heap | externs at `ContractsW` (#7); a permutation cannot send one bump-run name to a reused location while a dangling copy keeps it, so the direction is `fresh_run_image`'s; the route is B3's progress with the step-for-step simulation (`run_sim`'s shape), not `BinderMachine` |
| `SoundnessContracts J` in done | `SoundContracts J M` in done; `SoundnessContracts` kept, with its route through `Conservative` | #7 |
| `AcceptsTier2 J` (typing only) | `Tier2Programs J`, each `AcceptedAt` with its answer on one run | an expressiveness property states the run |

**Restated at `BWorld` or `coreB`, with the same proof** (`coreW.toBWorld` is `coreB` by `rfl`, and
every `BWorld` definition reads only the fields `toBWorld` keeps):

- at `coreB` in place of `coreW`: `extPre_core`, `famEmpty_core`, `dataVals_core`, `relElim_core`,
  `relShape_core`, `relLaws_core`, `fl_core_tier1`, `fl_core_tier1NU`, `lifetimeSound_core`,
  `conservative_core`, `conservativeWB_core`, `adequateRetAt_core_none`, `coreW_upd`,
  `updRefl_core`, `updOwn_core`, `updSeq_core`, `updReclaim_core`, `updFrame_core`,
  `updOutlives_core`, `updLendBack_core`, `ptoMutSW_core`, `ptoImmSW_core`, `ptoMutSW_core_eq`,
  `gSepW_core`, `gDenW_core`, `semWC_core`, `semW₀_core`;
- at `M : BWorld` in place of `M : SemWorld`: the definitions `ConservativeWB` and `Conservative`
  (they read only `val`, `Ext` and `nil`); `gDenW_nil`, `semWC_of_FL`, `comp_of_FL`,
  `soundRetAt_of_FL`, `soundDriveAt_of_FL`, `soundnessOfFL` (with `SoundnessOfFL`), `gDenW_of_meets`,
  `soundnessContractsOfFL` (with `SoundnessContractsOfFL`), and the `upd*_of_core` lemmas;
- `sliceShape_core` is split into `sliceShapeB_core` and `sliceShapeI_core`, its conjunction kept.

**`Status.lean` rows whose statement types change** with these restatements and with §4.6's first
table. The rows down to `status_carryW_printed` keep their proof terms, re-pointed to the re-homed
theorems; the rest are re-pointed to restated theorems:

| row | old type | new type |
|---|---|---|
| `status_fl_core_tier1` | `FL coreW tier1` | `FL coreB tier1` |
| `status_lifetimeSound_core` | `LifetimeSound coreW OutJ.core` | `LifetimeSound coreB OutJ.core` |
| `status_conservativeWB_core`, `status_conservative_core` | at `coreW` | at `coreB` (the definitions at `BWorld`) |
| `status_adequateRet_core_none` | `AdequateRetAt coreW Platform.none` | `AdequateRetAt coreB Platform.none` |
| `status_updLaws_core` | the `Upd*` laws at `coreW` | at `coreB` |
| `status_updLaws_of_core` | `{M : SemWorld}` | `{M : BWorld}` |
| `status_soundnessOfFL`, `status_soundnessContractsOfFL` | `SoundnessOfFL`, `SoundnessContractsOfFL` quantifying `M : SemWorld` | quantifying `M : BWorld` |
| `status_leakW`, `status_carryW_laws`, `status_carryW_printed` | B's predicates (`DataVals`, `Adequate`, the `Upd*` laws) applied to I's witness worlds | the same through `toBWorld` |
| `status_effSafeOfFL`, `status_soundnessContractsOfFLWB` | over `WLaws`, `ConservativeWB` | over `FamEmpty ∧ AdequateEvery`, `EmbedsNil` |
| `status_tier1End_of`, `status_endState_prog`, `status_i1Prog_of_endState`, `status_i2Prog_of_endState`, `status_not_endState_of_leak` | about `Tier1End`, `EndStateAt` | about `Tier1Core`, `Combined` (below) |
| `status_releasedOnceAll`, `status_p8a_of_endState` | `ReleasedOnceAll` presented as a guarantee; `P8a` | `releasedOnceAll`, a lemma about runs (below) |

**The tier-1 reduction, kept** (to build, `I/Restricted/Tier1Core.lean`):

```lean
/-- The tier-1 end state at today's kernel and Core's world, without what today's kernel cannot
meet (A's (E) properties need effect polymorphism, §4.3) or what is OPEN or to build regardless
(`ContUse`; `Accepts`' derivations and `Rejects`' inversions); with the device at `coreW`, as the
library's `Tier1End` held I1, I2, I3, I5, P11 and `ConservativeWB` there. -/
def Tier1Core : Prop :=
  (∀ Ξ, AdmEff Ξ → A.SPropsNoUse (ourInst orowRF Ξ tier1Open)) ∧    -- `SProps` without `ContUse`
  B.Guarantees ⟦tier1Open⟧ coreB ∧ Bounds coreW ∧ Interface coreW ∧
  Pins tier1Open admClosedOp .abortive ∧ Device coreW ⟦tier1Open⟧ admClosedOp .abortive ∧ WBCore
theorem status_tier1Core_of (hA : Adequate coreB) (hF : FinaliserOrder tier1) (hS : BumpSim) :
    Tier1Core
```

Its proof is the library's `status_tier1End_of` re-pointed (`soundnessOfFL`, `soundContractsOfFL`,
`effSafe_tier1`, `noInterception_tier1`, `i1_core`, `i2_core_abortive`, `i3_core`, `i5_core`,
`p11_core`, `conservativeWB_core`, `embedsNil_core`, `lifetimeSound_core`, `exclusive_core`,
`exclusiveB_core`, `extendsB_tier1`, …), with the Instance's bridges for A's (S) properties,
`effSafeDrive_tier1` for S3 in the drive phase, and `releasedOnceReuse_of_bumpSim` for B5.

**Retired, with the reason:**

- **`P8a` and `p8a_of_endState`.** `P8a` was `ReleasedOnceAll` read at the runs that capture a
  continuation, a tautology about runs (#2). The run lemma `releasedOnceAll` stays, with a
  docstring saying so. Its role as P8.a, the resource half, is taken by B4 and B5 at the runs that
  cancel; the use count, P8.b, is A's S6 `ContUse`, in done. `Statements/Linearity.lean`'s
  "`ContUse` is a placeholder name, not a target" is superseded by S6.
- **`status_releasedOnceAll`, `status_p8a_of_endState`.** These are re-pointed to
  `releasedOnceAll`, with a docstring saying it is a lemma about runs and not a guarantee.
- **`status_tier1End_of`, `status_endState_prog`, `status_i1Prog_of_endState`,
  `status_i2Prog_of_endState`, `status_not_endState_of_leak`, `status_effSafeOfFL`,
  `status_soundnessContractsOfFLWB`.** Re-pointed to the restated theorems: `status_tier1End_of`
  to `status_tier1Core_of`, the reduction kept above, with `status_tier1_of` beside it.

**The library's definitions, by home.**

| home | definitions |
|---|---|
| A | `EffAlg`, `EffAlg.Laws`, `EffAlg.Sub`, `EffAlg.SubstOK` (`Defs/Effects.lean`) and `EffAlg.Safe` (`Statements/EffectSafety.lean`), unchanged; none mentions Core |
| base | `RVar`, `Row.NU`, `RowClass`, `RowClass.Admits`, `RowCon`, `RowCtx`, `RowEnv`, `RowCtx.Models`, `EffCtx`, `RowEq`, `Row.Has`, `Kont.fins`, `cancelOf` (`Defs/Effects.lean`); all of `Defs/Runs.lean`; all of `Defs/Typing.lean`; the statements about runs that mention no world: Core's `EffSafe` (`Statements/EffectSafety.lean`) and `Soundness` (as `Sound`), `SoundRetAt`, `SoundDriveAt`, `SoundnessAt`, `SoundnessContracts`, `TypedSound` (`Statements/Soundness.lean`), which B's guarantees and the Instance's bridges both read; Core's I3 shapes from `Statements/Interface.lean` (`CancelRun`, `UnwindRun`, `CancelOrder`, `UnwindOrder`, `FinaliserOrder`, `NoInterception`, `Kont.NoCtl`, `Expr.HasPrim`, `Expr.HndNamesNZ`, `cancelAnswer`); new, for B5: `Named`, `Expr.mapLoc`, `Heap.push`, `Bump`, `BumpSim`; new, for the drive phase: `SafeDriveFrom`, `DRunOf`, `EffSafeDrive`; all of `Defs/Ctx.lean` (`Obs`, `thunkF`, `CtxApprox`, `CtxEquiv`), which the Instance's binary laws read; the answering implementations of `Defs/Programs.lean` (D13: `AnsImpl`, `ansCall`, `ansRun`, `ctlClause`, `ctlRet`, `clausesV`, `ctlForm`, `Expr.OpFree`, `Expr.performOf`, `Expr.size`, `capPass`), which the Instance's `Hiding` and I's `I4a` read |
| B | `Idx`, `ptoMutSW`, `ptoImmSW`, `gSepW`, `gDenW`, `SemWC`, `SemW₀`, `SemW` (`Defs/World.lean`); `FL`, `AdequateRetAt`, `AdequateDriveAt`, `AdequateAt`, `Adequate`, `ExtPre`, `FamEmpty`, `DataVals`, `RelElim`, `RelShape`, `RelLaws`, `VTy.AbortRows`, `CTy.AbortRows`, the `Upd*` laws (`Statements/Device.lean`); `ReleasedOnceOfSound`, `ReleasedOnceAll` (`Statements/Soundness.lean`); `LifetimeSound` (`Statements/Lifetimes.lean`); `SoundnessOfFL`, `SoundnessContractsOfFL`, `SoundnessContractsAR` (`Statements/Composition.lean`); `ReleasedOnceReuse` (restated, §2.4) and `BinderMachine` (`Statements/Binder.lean`); the machine half of `Defs/Binder.lean` (`Ranges`, `BlockAffine`, the `arrRanges`, `RangesIn`, `StepsIn`); `WBCore`, `ConservativeWB`, `Conservative` (`Statements/Conservativity.lean`, as `B/Conservativity.lean`), since `SoundnessContractsOfFL` reads `Conservative`; new: `BWorld`, `coreB`, `BorrowRulesClosed`, `ExtendsB`, `ExclusiveB`, `SliceShapeB`, `WBound`, `ContractsW`, `SoundContracts`, `Guarantees` |
| I | `TableI`, `TableI.Mono`, `TableI.Abortive`, `OpEntI`, `OpTabI`, `wpGW`, `valPostI`, `ewpW`, `ewpPostW`, `opTabW`, `errOkW`, `cancelTabW`, `entW`, `rowTabW`, `coreW`, `OpEntI.down`, `OpTabI.down`, `TableI.down` (`Defs/World.lean`); `SliceShape` (split), `Mono`, `EffInterp`, `ShareMono`, `AdequateEvery`, `WLaws`, `EwpMono` (`Statements/Device.lean`); everything else in `Statements/Interface.lean`; `Exclusive` (`Statements/Exclusivity.lean`); `HandleCompat`, `RedLaws`, `P11` (`Statements/Handlers.lean`'s P11 half); `FreezeBinderLoc`, `FreezeBinderLife`, `FreezeBinder`, `NotVDenNaturalArises` (`Statements/Binder.lean`) and the world half of `Defs/Binder.lean` (the location and lifetime actions on resources, records, indices and tables); `I1Prog`, `I2Prog` (`Statements/EndState.lean`); `AcceptedT1` (`Restricted/Soundness.lean`); the acceptance terms of `Defs/Programs.lean` (D14: `fooSig`, `fooE`, `chooseSig`, `chooseE`, `suspE`, `handleWith`, `resumeArg`, `resumeLeft`, `cancelAns`, `storeResume`, `dupFlag`, `readThrough`, `writeThrough`, `cb`, `lendCell`, `at02`, `at04`, `at12`, `at17`); `EffSafeOfFL`, `SoundnessContractsOfFLWB`, `AdequateOfLaws` (`Statements/Composition.lean`); new: `SemWorld`, `SliceShapeI`, `Bounds`, `Interface`, `EmbedsNil`, `Pins`, `SpanRulesAt`, `Accepts`, `AcceptedAt`, `Rejects`, `Device`, `Combined`, `Tier1Core`, `ovalW`, `FLOpen` |
| Instance | `orowAlg`, `closedRowAlg`, `ORow`, `RowForm`, `RowLink`, `orowRF` (`Defs/Effects.lean`); `RowAlgSafe` (`Statements/EffectSafety.lean`); new: `AdmEff`; the binary laws over Core, as A₂ at our instance, stated, in `Instance/Binary.lean`, which imports base's `Ctx.lean` and `Programs.lean` and nothing of I's (`Statements/Handlers.lean`'s T2 half: `tailClause`, `Expr.renameOp`, `LawRet`, `LawOp`, `LawFwd`, `LawTail`, `LawAlg`, `CapBeta`, `fwdClause`, `fwdH`, `CapEta`, `AnsSim`, `ctlObs`, `Hiding`, `LawFusion`, `LawNuOp`, `Laws`; `Statements/Abstraction.lean`: `hofTy`, `Expr.HndFree`, `Tunnel`, `RepInd`, `Encap`, `Abstraction`); `LowClass` and `Statements/ZeroCost.lean`, as A₃ at the backend (named-only) |
| restated | `Guarantees`, `EndStateAt`, `EndState`, `Tier1End`, `EndStateBinder` (`Statements/EndState.lean`) become `B.Guarantees`, `I.Combined`, `done`, `Tier1` (with the restricted `Tier1Core`) and `CombinedBinder` (§4.6's first table) |
| retired | `P8a` (`Statements/Linearity.lean`) |
| meta | `Audit.lean` (extended, §5.2), `AxiomCheck.lean` (extended to definitions), `Status.lean` (re-pointed) |

---

## 5. Findings #2, #6, #7, and the earlier findings that still apply

### 5.1 #2: exactly-once release had no content

Resolved in §2.4: done holds B5, `ReleasedOnceReuse`, at-most-once on runs that reuse locations,
and B4 gives at-least-once. `ReleasedOnceAll` is a lemma about runs. B5's dependence on OQ-43 is
stated, and the user is asked (§7 Q4).

**The rule for the corrections.** When the Lean is written, every occurrence of `ReleasedOnceAll`,
`releasedOnceAll`, `P8a`, `p8a_of_endState`, or a sentence presenting release "exactly once" as a
consequence of either, in `experiments/Targets` (Markdown and Lean) and `research/effects`, is
corrected: `ReleasedOnceAll` is a tautology about runs; the guarantee is B4 with B5. Two greps make
the list reproducible (both case-insensitive, over `*.md` and `*.lean`, `RESTRUCTURE*.md` left out):

- **Grep 1**, every hit of which is listed below, to correct or with the reason it stays:
  `grep -rni "ReleasedOnceAll\|releasedOnceAll\|P8a\b\|P8\.a\|releas[a-z]* [a-z ]*exactly once\|exactly-once release\|finalis[a-z]* exactly once"`.
- **Grep 2**, `grep -rni "exactly.once"` minus grep 1's hits, which finds the sentences grep 1
  misses (a phrase broken across a line, or "exactly once" alone). Each hit is read: those that
  present release as carried by `ReleasedOnceAll` or D9 are corrected, and the rest (a
  continuation's qualifier, a finaliser firing once, the literature) stay.

Run at `938d280`:

| document | correct (grep 1) | correct (grep 2) | stays, and why |
|---|---|---|---|
| `DESIGN.md` | 12, 195 (beside-done list and table: B5 is now in done); 138, 664, 725 (`Guarantees`, its table, P8.a among the corollaries); 1128, 1133, 1151, 1164–1168, 1176, 1193–1194 (D9, its definitions and docstrings: on no-reuse runs an event-level fact, a tautology given `NoReuse` and `Final`; the content is `ReleasedOnceReuse` in the fresh-run direction, §2.4); 1571, 1579–1580 (T1: B4 frees every cell, B5 each allocation once); 2887 (I3 (a): "B4 frees it; B5 frees it once"); 3388–3390, 3398, 3419–3420, 3425 (P8.a: B4 with B5; P8.b is A's S6, in done); 3682, 3688, 3690, 3782, 3822, 3828 (A6, T4, T6, the build list, OQ-50's rows: B4 and B5; done states the use count); 3957, 3961 (Builder's notes: "a tautology about runs") | 79, 94 (exactly-once release among the guarantees, "a target (T1, D9, I3)"); 1015, 1179, 1206 (D9); 3024 (A6's second half, the first half now A's S6) | 2866 (I3's heading, "drop finalises exactly once": each finaliser fires once, A's S5); grep 2's 3380–3381, 3404 (a continuation's qualifier; Tang's "consumed exactly once") and 3723 (AT12's finaliser fires once) |
| `README.md` | 64–65, 90, 110, 123, 147, 153, 155 (`ReleasedOnceReuse` in done; P8.a no corollary) | — | — |
| `AGREE.md` | 139, 192, 193, 245–246 (AGREE 5 answered by B5 in done, §7 Q7) | — | 67, 73 (they quote the finding); grep 2's 113 (the qualifier `lin`) |
| `FIX-RUN-END.md` | 540, 681, 1067 (B4, the non-empty final memory, and B5) | — | — |
| `Targets/Statements/Soundness.lean` | 5, 20–21 (module docstring); 73 (`ReleasedOnceAll`'s docstring, "a conjunct of done") | 67 (`ReleasedOnceOfSound`'s docstring: its premises are unused), 75 | 76 (the declaration; its name stays) |
| `Targets/Statements/EndState.lean` | 25, 41 (retired with `P8a`; `Guarantees` restated) | — | — |
| `Targets/Statements/Linearity.lean` | 14–16, 34–35 (P8.a is B4 with B5, P8.b is A's S6) | 8–9 | — |
| `Targets/Statements/Binder.lean` | 96, 98 (the restated B5, §2.4) | — | — |
| `Targets/Statements/Interface.lean` | — | — | 20, 294 (I3's name: each finaliser fires once) |
| `Targets/Defs/Runs.lean` | 15, 168, 188 (`ReleasedOnce` is an event-level property of a run; on no-reuse runs it follows from `Final`) | — | — |
| `Targets/Restricted/Release.lean` | 4, 14, 139 ("a tautology about runs") | — | 85 (`releasedOnce_of_ends`' docstring, a true event-level lemma); 140 (the declaration) |
| `Targets/Restricted/Corollaries.lean` | 12, 113, 115, 124 (`p8a_of_endState` retired; `endState_prog` restated) | — | — |
| `Targets/Status.lean` | 44, 53, 89, 207, 272, 279, 395, 433 (`status_releasedOnceAll`: a lemma about runs; the end-state rows restated) | — | — |
| `Targets/AxiomCheck.lean` | — | — | 373, 448 (`#print axioms` lines: only the rename, if the declarations change namespace) |
| `research/effects/src/properties/i3-drop.md` | 7 ("`ReleasedOnceAll` releases its memory once": B4 releases it, B5 once) | — | 1 (I3's title); grep 2's 5 (each finaliser fires once) |
| `research/effects/src/properties/continuation-linearity.md` | 7 ("on runs that reuse no location, a tautology; B5 for every run; the use count is A's S6") | — | grep 2's 5 (the qualifiers) |
| `research/effects/src/properties/soundness.md` | 8, 14 | — | — |
| `research/effects/src/register.md` | 7 (P1), 14 (P8) | — | 11 (P5's title, I3) |
| `research/effects/src/interaction.md`, `SUMMARY.md` | — | — | 10; 40 (I3's title) |
| `research/effects/src/system-a.md` | — | — | 24 ("finalisation exactly once, from linearity", a borrow-derived route to S5, §4.4) |
| `research/effects/src/tracks/log.md` | — | — | 10, 11 (dated log entries of 2026-10-05, true of that date) |
| `research/effects/src/foundations/linearity.md` | — | — | grep 2's 6, 11 (the literature's state, and I3 as a theorem shape) |
| `research/effects/survey.md` | — | — | grep 2's 97, 100–101, 215, 237, 507, 544, 645, 717, 802, 1091 (the literature's statements and the survey's design notes; none cites `ReleasedOnceAll`) |

### 5.2 #6: the step-index audit, extended

**The choice: extend the audit, and keep review.** No-step-indexing is a property of `W`'s
definition, not of its laws, for two reasons.

- A step-indexed relation can meet every conjunct of done, with its index hidden in `Stk` and
  decremented by `Upd` or at the `U` and `ν` clauses. So no Prop over `W` excludes it.
- The lifetime stratification the model already uses (`Life = ℕᵒᵈ`, `Cell`'s `WellFounded.fix`),
  which decision 7 does not exclude, is itself recursion on a natural number. So a structural
  requirement, well-founded recursion on lifetimes only, cannot be told apart from a counter
  (review [13] (4)).

So the enforcement is a definitional audit with negative tests, plus review of `W`'s definition.
The audit (`Targets/Audit.lean`) runs on `W` (as `audit_W`) and on `coreW`, over the closure of the
world's definition within `Paper`, `Support`, `Core` and `Targets` (today's `closure`). It reports
five kinds of thing. "A count-like type" is `ℕ`, `Fin n`, `UInt8`–`UInt64`, `Life` or `ℕᵒᵈ`, read
**after unfolding reducible definitions and instantiating `Stk`**, so `Idx Stk` at `Stk := ℕ` is
count-like, as is any abbreviation of these. A type reaches ℕ only through `Loc` (locations, heaps,
resources) is reported in a bucket of its own.

1. **Recursor and case shapes** in the values of definitions: `Nat.rec`, `Nat.recOn`, `Nat.brecOn`,
   `Nat.below`, `Nat.casesOn`, `Nat.casesAuxOn`, `Nat.iterate`, `WellFounded.fix`,
   `WellFounded.fixF`, `Nat.strongRecOn`, `Nat.repeat`, `Nat.fold`, `Fin.induction`, `Fin.cases`,
   `Fin.casesOn`, `UInt*.casesOn`. A `match` on a count-like value compiles to an auxiliary
   matcher that uses `Nat.casesOn`, so matchers are covered.
2. **Indexed predicate families.** Every inductive type in the closure whose sort is `Prop` and
   which has an index of a count-like type (the finding's `SafeN : ℕ → …`, and a family indexed by
   `Idx Stk`). It is restricted to predicates, so the report does not cascade through every syntax
   type that holds a location or a lifetime (review [13] (1)).
3. **Impredicative indexed fixed points.** Every definition whose value binds `∀ P : … → Prop` with
   an argument of a count-like type: an `ewpW`-shaped least fixed point over a count (review [13]
   (3)).
4. **Bounded iteration.** Every use of `List.range`, `List.range'`, `List.replicate`, `Nat.fold`,
   `Nat.iterate`, `Nat.repeat` or `Fin.foldl` (review [13] (2)).
5. **Arithmetic on an index.** (a) Every constructor of a reported family whose result index uses
   `Nat.succ` or `+` (an `n + 1` constructor); (b) in `W`'s own modules, every `Nat.sub`,
   `Nat.pred`, `Nat.succ`, `HSub.hSub` or `HAdd.hAdd` at a count-like type.

Each report is pinned, and the build fails when it changes. Every entry is justified as recursion
on data, on a lifetime, or on an allocation count, never on a count of machine steps.

**`coreW`'s extended report, computed.** The five checks were run on `coreW` at `938d280` in a
scratch file (not committed), over its closure of 825 constants:

| item | entries | justification |
|---|---|---|
| 1 | `BoCa.Fig16.Cell` (`WellFounded.fix`) | the stratification by lifetime, which decision 7 keeps ([CONF] 415:20) |
| 1 | `BoCa.Fig16.BoLo.sepRange`, `sepRange._f`, `sepRange.match_1`; `BoCa.tabFill`, `tabFill._f`, `tabFill.match_1`; `BoCa.dropFill`, `dropFill._f` | recursion on an array's length: the separating conjunction over its cells, and the machine's `tab` and `drop` |
| 1 | `BoCa.BoLo.clauseAt.match_1` (`Nat.casesOn`) | the index of a clause in a handler's right-nested clause tuple: data |
| 1 | `BoCa.Fig16.LogRel.Core.VTy.upR.match_1` (`Nat.casesOn`) | a de Bruijn index: data |
| 2 | `BoCa.BoLo.AHead`, `BoCa.BoLo.ARun` (index of type ℕ) | **the allocator's allocation count** `k` (`Core/Alloc.lean:70,88`): each allocation increments it, and it selects the allocator's location (`A.pick k μ n`). It is never decremented, no relation is defined by recursion on it, and it counts allocations, not steps. `wpGW` uses `ARun` to quantify over every allocator (`Alloc.replay`) |
| 2, via `Loc` only | `BoCa.BoLo.Head`, `Chain`, `GPos`, `LinPath`, `MutPos`, `RefPos`, `TW` | indexed by heaps, resources or locations: names, not counts |
| 3 | `Table`, `ewpTS`, `vCE._f` | their predicates range over `List SRec`, the lend records, whose `Life` is a lifetime |
| 4 | none | — |
| 5 (a) | `AHead.alloc`, `AHead.tab` (`k + 1`) | the allocation count, as item 2 |
| 5 (b) | none in `coreW`'s own module | — |

The library's audit pins item 1's first four rows only; `audit_W` pins all of them at `W`.

**Negative tests.** Eight toy step-indexed worlds that the audit must reject. A `run_meta` asserts
that each report is non-empty:

- `stepW₁`: `val` by `Nat.rec` on an index;
- `stepW₂`: a `Prop` family `SafeN : ℕ → …`, with `Stk := ℕ`;
- `stepW₃`: the relation as a `List.range n` fold;
- `stepW₄`: an impredicative `ℕ`-indexed least fixed point;
- `stepW₅`: `Stk := Life`, decremented as a counter by `Upd`;
- `stepW₆`: `Stk := ℕ`, decremented by `Upd` with `Nat.sub`;
- `stepW₇`: `Upd` decrements by a match, `True` at `0`: `match i.2 with | 0 => True | n+1 => i'.2 = n`;
- `stepW₈`: a family indexed by `Idx Stk` at `Stk := ℕ`, with an `n + 1` constructor.

`stepW₇` and `stepW₈` were run in the same scratch file: item 1 reports `stepW₇`'s matcher
(`Nat.casesOn`), and items 2 and 5 (a) report `stepW₈`'s family and its `succ` constructor.

**The residual, stated.** The audit is syntactic: it reports the forms step-indexing takes in Lean,
and a counter in a type it does not list would pass it. `W` is ours and built in good faith, so the
audit is a check against accidental step-indexing, and decision 7's enforcement also includes a
review of `W`'s definition before done is claimed.

### 5.3 #7: externs carry their contracts as an explicit hypothesis

Externs and unsafe code are outside the proofs by design ("Externs and unsafe are outside the
proofs by design", the brief §6). So done's soundness with externs takes the contract as an
explicit hypothesis, at the composite's world, and is proved from B1 and B2 alone. It does not go
through `Conservative`.

```lean
/-- The externs' values are in W's relation at their types, at the nil index, holding nothing. -/
def ContractsW (M : BWorld) (Γ : Ctx VTy) (γ : List Val) : Prop :=
  gDenW M ([], M.nil) LSub.empty Γ γ (PMap.empty : WRes)
/-- **B4′**: with externs meeting their contracts, every run of a typed program is safe and
terminates with the memory empty. -/
def SoundContracts (J : TypingJ) (M : BWorld) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) → ContractsW M Γ γ →
    SafeRuns P A (substAll γ e) ∧ Terminates P A (substAll γ e)
theorem soundContractsOfFL : FL M J → Adequate M → SoundContracts J M      -- to build: `soundnessContractsOfFL`'s proof minus `Conservative`
```

- **At the SPEC's externs**, which are row-abortive, Core's fixed contract `ExternsMeet` gives
  `ContractsW` through `EmbedsNil` (`contractsW_of_meets`). `EmbedsNil` is beside done (§3.6), so
  `SoundnessContractsAR`, at Core's contract and independent of `W`, is a corollary of `Combined`
  together with `EmbedsNil` (§3.5).
- **At other extern types**, resuming rows among them, the contract is W's. Whoever provides such
  an extern proves it meets W's contract. That is "outside the proofs by design", made a stated
  hypothesis. `W` is named and audited, not chosen by the prover of each extern (§7 Q8).
- **B4′ and B5 read the world, through the contract.** `ContractsW M Γ γ` is the only place either
  reads `M`. At `Γ = []` it holds at every world, so B4′ there is `Sound` and B5 is
  `ReleasedOnceReuse₀`, which read no world (§6.2). **Done does not claim that the contract is
  inhabited at a non-empty `Γ`.** Beside done it is, at row-abortive types: `EmbedsNil` (device)
  carries every value meeting Core's `ExternsMeet` into it. At other types no route is claimed.
  `FL M J` gives a closed value `v` only as a computation, `M.comp (.ret A) ([], M.nil) … (.val v)`,
  and reaching `M.val` at the nil index from there needs `EffInterp` at the empty row together with
  a zero-step run that ends at its own index (`UpdRefl`'s shape, beside done); `wpGW`'s zero-step run
  otherwise picks its end index existentially, possibly off the nil slice.
- `SoundnessContractsOfFL`, which goes through `Conservative`, is kept as an alternative route.

### 5.4 #3, #4, #5, and the earlier review findings

- **#3, row variables required by nothing.** Resolved by the schemas of E1, E2, E6 and E10 (§1.6),
  which need effect polymorphism, and by the abstract lemma `not_noColouring_of_monoCallback`
  (§6.1), which shows that an instance without it fails E1. `RowVarKernel` records decision 62's
  mechanism at `J₂` (§4.2); it is not a pin.
- **#4, T4 unstated.** Resolved by A₃ (§1.7), over a target and reference programs fixed in A.
- **#5, OQ-8 and OQ-9 constrained by done.** Resolved by §3.6.

The orchestrator listed v1's findings that still apply:

| v1 finding | resolution here |
|---|---|
| handler semantics only at whole terms | S4 holds in every context `K₀`, binds and applications included, up to `PureJoin` |
| cancellation as built left as shapes | S5's traces are written out (§1.5); E7, E8 and E9c observe each fire and end |
| non-vacuity in prose only | §6 gives a Lean statement per (E) property, abstract where the missing feature is a Prop |
| B imported I's world | `BWorld` has borrow fields only; `SemWorld extends BWorld`; B imports no I, checked file by file (§4.5): `Conservativity.lean` is B's, `exclusiveB_core` is proved from `TW.valid`, and the definitions the Instance's binary laws read are base's |
| done rests on an open machine lemma unstated | B5's dependence on OQ-43 is stated, and the lemma is named (`BumpSim`, §2.4, §7 Q4); `Accepts` rests on none (§3.4) |
| the audit extension's remaining holes | §5.2: case shapes, index types unfolded, `n + 1` constructors, eight negative tests, `coreW`'s report computed, the residual stated |
| [15] the tier-1 list | §3.5 |
| [16] `i1Prog`/`i2Prog` | at `c = .any` |
| [17] `EffSafeOfFL` | restated over `FamEmpty ∧ AdequateEvery` |
| [18] `ConservativeWB → EmbedsNil` | listed (§4.6), and §7 Q7; the third review then moved `EmbedsNil` beside done too (§3.6) |
| [19] `Ξ`, the runner–platform map, `SpanRulesAt`, `WBCore` | §4.1 (`AdmEff`, `platformOf R ε`), §3.5 (Ξ quantified in done since the third review; `SpanRulesAt` a recorded lemma since then); `WBCore` is a companion lemma, dropped from `Tier1`'s conjunction (§4.6) |

---

## 6. Non-vacuity, and the programs concretely

### 6.1 Per (E) property: the lemmas

Every (E) property has a **trivial** lemma. Where the decided feature is genuinely needed, it also
has a **feature-less** lemma. That lemma is abstract, in `A/NonVacuity.lean`, wherever the absence of
the feature is a Prop over the instance and the proof needs only A's laws; otherwise it is concrete,
at our machine.

```lean
-- trivial instances: every (E) property fails
theorem not_eProps_of_emptyTyping (h : ∀ Γ e C, ¬ S.der Γ e C) : ¬ A.EProps S
theorem not_eProps_of_noLabels (h : ∀ l, S.sig l ≠ sigExn S) : ¬ A.EProps S          -- E1's `∃ labels` fails

-- effect polymorphism
/-- **A context type fixes one callback row** (no effect polymorphism).  At a use that applies a
context variable to a callback with a data answer, a callback accepted at one type of the use is
accepted at every type at which the use accepts some callback with that answer. -/
def MonoCallback (S) : Prop :=
  ∀ Γ i pre post B, S.DataTy B → ∀ M₁ M₂ ε₁ ε₂ C₁ C₂,
    S.der [] M₁ (S.F ε₁ B) → S.der [] M₂ (S.F ε₂ B) →
    S.der Γ (S.apps (S.var i) (pre ++ S.lam M₁ :: post)) C₁ →
    S.der Γ (S.apps (S.var i) (pre ++ S.lam M₂ :: post)) C₂ →
    S.der Γ (S.apps (S.var i) (pre ++ S.lam M₂ :: post)) C₁
theorem not_noColouring_of_monoCallback (hm : A.MachShape S) (hr : A.RowAlgebra S) (he : A.EffSafe S)
    (hl : A.LetLaw S) (hmono : MonoCallback S) : ¬ A.NoColouring S
theorem not_higherOrderPoly_of_monoCallback (…the same…) : ¬ A.HigherOrderPoly S    -- at E2a's `twice f`
theorem not_tunnel_of_monoCallback (…the same…) : ¬ A.Tunnel S                      -- at `fwrap`, the raise of `lo`
theorem not_reconciler_of_monoCallback (…the same…) : ¬ A.Reconciler S              -- at `timeout`, the raise of `le`

-- divergence: a total instance fails E3; a pure-row loop that diverges has a type that is not data
def Total (S) : Prop := ∀ R e ε A, R.Respects → S.Answers R ε → S.der [] e (S.F ε A) → S.Terminates R e
theorem not_loops_of_total (h : Total S) : ¬ A.Loops S
theorem divInTypes_of_loops (hs : A.Safety S) (hd : A.DataDiv S) (hl : A.Loops S) :
    ∀ L, S.der [] (A.runL S A.spinL) (S.F S.EA.unit (S.Sum S.UnitT L)) → ¬ S.DataTy L

-- effect safety has teeth: an unhandled operation is untypable at the pure row
theorem not_der_unhandled (hm : A.MachShape S) (hr : A.RowAlgebra S) (he : A.EffSafe S)
    (l i v) (A' : S.Ty) : ¬ S.der [] (S.perform l i v) (S.F S.EA.unit A')
```

**The proof of `not_noColouring_of_monoCallback`.** Take the labels E1 provides, and its `A`. Put
`M₁ := ret tt` at the pure row and `M₂ := raise le 0 ()` at `(le)↑`, both typed by E1's callback
clause. `PolyUse` types `f (λ_. M₁)` at `F 0 bool` and `f (λ_. M₂)` at `F (le)↑ bool`.
`MonoCallback`, at `Γ = [A]`, `i = 0` and no other argument, types `f (λ_. M₂)` at `F 0 bool`.
`LetLaw` types the closed program `P := let f = hof in f (λ_. M₂)` at `F 0 bool`. E1's
`CallsThrough` makes `P` reach `plug K (raise le 0 ())`, with `K` catching nothing and holding no
finaliser, by steps that change no store. That configuration is not `IsVal` (`DataInj`), takes no
step (`OpStuck`), and is not `StopsIn 0`, since the pure row admits nothing (`RowSig`). So `EffSafe`
fails at `P`. The other three are the same proof at `twice f`, at `fwrap` (labels other than `li`;
its schema is `PolyUseLacks`, and both callbacks lack `li` since `li ≠ lo`) and at `timeout` (labels
other than `lw`), with `SubClosed` putting the callbacks at `l ⊙ ε` for `timeout`'s `PolyUseOpen`
schema.

**Concrete lemmas, at our instance** (to build):

| (E) property | feature | the lemma | proof route and cost |
|---|---|---|---|
| E1, E2, E6, E10 | effect polymorphism | `monoCallback_tier1Open : MonoCallback (ourInst tier1Open)` (Instance); then `not_noColouring_tier1Open`, `not_higherOrderPoly_tier1Open`, `not_tunnel_tier1Open` and `not_reconciler_tier1Open` (I, with `EffSafe` discharged) | inversion. A use `apps (var i) args` typed at `C` gives `Γ[i]`'s closed type `(!)U(A₁ → … → Aₙ → C')` with `C'` below `C` (`effSub`), and each argument at its `Aₖ`; the callback's `Aₖ = U(X → C₀)` with `X` droppable, so `M` is at `C₀`; and a second `M₂` at `C₀` gives the same derivation with its callback replaced. A lifetime instantiation on the way (`allE` at a literal `()`, `allEV` at a value) may change `Γ[i]`'s type, but not the callback's row or data answer: Ξ's operation types are closed in lifetimes (§4.1), so no row mentions a lifetime variable. So `C₀` is fixed by `Γ[i]`. D21: one inversion lemma per spine constructor |
| `Tier2Programs` | spanning lends | `not_tier2_tier1 : ¬ tier1.closed at02 (.ret Flag)`, and likewise for `at04`, `at12`, `at17`, `genSelf`, `reconB` | the expected route, by inversion: the rules that give `withborUE d` a lending type are the unwinding constants, which ask `Row.Unwind`, abortive operations only, while the callback performs a resuming or affine operation; the generic rules would hand the callback the owned `Ref` and also return it, which linearity forbids. This settles the AGREE minor finding "`AcceptsTier2` has no tier-1 rejection proved" |
| S6 `ContUse` | linear and affine κ, explicit cancel | `not_contUse_of_der_R1` … `_R4 : (ourInst J).der [] Rₖ (F 0 bool) → ¬ A.ContUse (ourInst J)`, for every `J` | Rₖ's run at our machine, computed (it does not depend on `J`): the catch, then the clause; R1 completes with κ caught once and used never; R2 resumes it twice; R3 cancels a κ caught at a linear operation; R4 resumes after the cancel. With `refuses_R_tier1Open` (today's kernel refuses all four, by inversion: `kTy` at `lin`/`aff` is a thunk, neither droppable nor persistent, and a linear κ's cancel branch is at `⊤`) |
| E3–E9 | — | `eN_tier1Open` (positive, to build): each program typed by today's rules, and its run computed | Core's encodings. The run is computed by an interpreter proved to agree with `ourInst`'s steps, or written out: `Support/Dynamics/Interpreter.lean`'s `eval` has no such theorem today, so the library's `*_eval` checks are evidence only. The programs allocate nothing, so every machine step keeps the store, and `det_ourInst` (Core's determinism up to allocation, §4.1) makes every run the one computed; E3's runs use `LoopLaws` and `DriveLaws` at Core's `ν` |

- **The positive lemmas show the (E) properties are satisfiable.** They are not tautologies, and
  our instance meets every one that needs no polymorphism.
- **The feature-less lemmas show the features are needed.** At effect polymorphism the lemma is
  abstract: every instance in which a context type fixes one callback row fails E1, E2, E6 and E10,
  whatever its typing rules. Today's kernel is one such instance (`monoCallback_tier1Open`).
- **Deep handlers and the cancel policy** are needed through S4's deep-resume law and S5's traces,
  and E4, E7, E8 and E9c observe them in their traces. Their alternatives give different traces
  and answers, which E7's table records. An abstract lemma that a shallow instance fails E4 would
  need A to compute E4's run through `deepGen`'s clause, which A cannot do without a substitution
  algebra; I have not derived one, and have not verified that any obstruction to one is real.
- **The runners respect their protocol.** `rtick_respects`, `rtl_respects` and `rrec_respects`
  (each operation linear, data to data, total) are to build, as `platformPing_respects` is checked.

### 6.2 Done as a whole

1. **The program level is asserted of `J₂`** (`combined_prog`). A's properties at every admissible
   Ξ, `Sound`, `ReleasedOnceReuse₀`, `ExtendsB`, `Pins`, `Accepts` and `Rejects` read no world, so
   no choice of world makes them easier. B4′ (`SoundContracts`) and B5 (`ReleasedOnceReuse`) at a
   non-empty `Γ` read the world through the externs' contract `ContractsW M` (§5.3). Done does not
   claim that contract inhabited at a non-empty `Γ`; beside done it is at row-abortive types, through
   `EmbedsNil` and Core's `ExternsMeet`, and at other types no route is claimed (§5.3).
2. **A typing that types nothing fails `A.EProps` and `Accepts`.** One that types an unsafe program
   fails `Sound`. One that types R1–R4 fails S6 (`not_contUse_of_der_R*`), and one that types AT05,
   AT06, AT08 or AT13 fails `Rejects`. One that types every callback use at one row fails E1, E2,
   E6 and E10 (`not_noColouring_of_monoCallback` and the others).
3. **B5 is not a tautology** (to build):

   ```lean
   /-- `staleFree := x ← alloc (); free x; y ← alloc (); free x`.  Under an allocator that gives
   `y` the location `x` had, the run ends at `()` with the memory empty.  No complete bump run of it
   exists: the bump run gives `y` a fresh location, and its second `free x` has no step. -/
   theorem not_releasedOnceReuse_staleFree (J M) (h : J.closed staleFree (.ret .unit)) : ¬ ReleasedOnceReuse J M
   ```

   That is all it shows. A typing that types `staleFree` already fails B3, whose bump run is
   stuck at the second `free x`; and given the step-for-step simulation, B5 follows from B3 and B4
   (B4′ with externs, §2.4). So B5 in done excludes no typing that B3 admits, and costs only that
   machine lemma.

4. **B's guarantees at W mean what they mean at Core.**
   - `WBound` and `Bounds` give the relation Core's shape at every type former, and pin the nil
     slice to Core's (FIX-RUN-END).
   - `Adequate`, with `EffInterp` and `DataVals`, ties the relation to W's runs; a world whose
     `Upd` admits a reachable leak fails it (`not_combined_of_leak`; the witness `leakW`, checked).
   - `Arises`, `Exclusive`, `ExclusiveB` and `LifetimeSound` do not read `Upd`.
5. **The audit reads `W`'s definition.** It rejects eight step-indexed toy worlds, with the
   residual of §5.2 left to review.

### 6.3 The programs, and what each must show

These are A-level programs. Their terms are in §1.6. Every one is run under `R₀` unless the table
says otherwise. The trace is the observable one: io events and finaliser events.

| id | labels (signatures) | type (row, answer) | answer | trace | decided feature it forces | at `tier1Open` |
|---|---|---|---|---|---|---|
| E1 `noColour`; schema | exn, wait | `0`, `bool ⊗ ((bool ⊕ 1) ⊗ bool)` | `(tt, (inr (), tt))` | `[]` | row variables; errors as raise | **fails** (`not_noColouring_tier1Open`) |
| E1′ `noColourS` | exn, wait | `0`, `bool ⊗ bool` | `(tt, tt)` | `[]` | row variables; a real suspension, resumed after its handler returned | fails |
| E2a `prog2a`; schema | exn | `0`, `(bool ⊗ bool) ⊗ ((bool ⊗ bool) ⊕ 1)` | `((tt, tt), inr ())` | `[]` | row variables (callbacks of callbacks) | fails |
| E2b `prog2b`; schema | wait | `0`, `bool ⊗ bool` | `(tt, tt)` | `[]` | row variables (returned and stored callbacks) | fails |
| E2c `prog2c`; schemas | exn, log | `0`, `bool ⊗ bool` | `(ff, tt)` | `[]` | row variables with open rows (policies) | fails |
| E2d `prog2d`; schema | yield, exn | `0`, `bool ⊗ (bool ⊕ 1)` | `(tt, inr ())` | `[]` | row variables (effectful codata); deep forwarding | fails |
| E3a | tick | `{tick}`, `1 ⊕ L` | — | `tick`ⁿ, never complete (under `Rtick`) | divergence as codata, the driver | holds (to build) |
| E3b | tick | `{tick}`, `bool ⊕ L` | `tt` | `[tick]` (under `Rtick`) | loops that end | holds |
| E3c | tick | `{tick}`, `bool ⊕ L` | `tt` | `[tick, tick]` (under `Rtick`) | a div function called inside a program; the delay bind | holds |
| E3d | tick, log | `{tick}`, `1 ⊕ L` | — | `tick`ⁿ, never complete (under `Rtick`) | a loop under a user handler | holds |
| E3e | tick, log | `{tick, log}`, `1 ⊕ L` | — | `tick` then `log`ⁿ, never complete (under `Rtl`) | two loops sequenced | holds |
| E3f | tick | `{tick}`, `1 ⊕ L` | — | `tick`ⁿ, never complete (under `Rtick`) | a div callback to a higher-order function | holds |
| E3g, E3g′ | — | `0`, `bool`; `0`, `1 ⊕ L` | `inr ()`; — | `[]`; `[]` forever | fuel makes div code total; divergence in types at the pure row | holds |
| E4 `deepGen` | yield, tick | `{tick}`, `1` | `()` | `[tick, tick]` (under `Rtick`) | deep handlers | holds |
| E5 `logOutside'` | log, exn | `0`, `(1 ⊕ 1) ⊗ bool` | `(inr (), tt)` | `[]` | nesting, forwarding a resuming op, deep | holds (Core's `nLogOutside`) |
| E5 `failOutside'` | log, exn | `0`, `(1 ⊗ bool) ⊕ 1` | `inr ()` | `[]` | nesting, forwarding a raise | holds (`nFailOutside`) |
| E6 `tunnel`; schema | exn, exn | `0`, `bool ⊕ 1` | `inr ()` | `[]` | row variables (`fwrap` at every row without its own label, callback and use at the same row); static names | **fails** (the schema) |
| E7a | wait | `0`, `bool ⊕ 1` | `inr ()` | `[fire (), finEnd none]` | abandon by cancel; the finaliser runs once | holds (`takeProg` shape) |
| E7b | wait, exn | `0`, `(bool ⊕ 1) ⊕ 1` | `inr ()` | `[fire (raise exn ()), finEnd exn]` | cancel re-raises the first outside error | holds (`prog₃` shape) |
| E7c | wait, exn | `0`, `(bool ⊕ 1) ⊕ 1` | `inr ()` | `[fire (raise exn ()), finEnd exn]` | the region's own error suppressed; no interception | holds (`prog` shape) |
| E7d | wait, exn, exn | `0`, `((bool ⊕ 1) ⊕ 1) ⊕ 1` | `inr ()` | `[fire (raise exn_a ()), finEnd exn_a, fire (raise exn_b ()), finEnd exn_b]` | innermost first, first kept | holds |
| E8a | exn | `0`, `1 ⊕ 1` | `inr ()` | `[fire ()]` | unwind runs the finaliser | holds (`two_frame` shape) |
| E8b | exn, exn | `0`, `(1 ⊕ 1) ⊕ 1` | `inl (inr ())` | `[fire (raise exn_b ())]` | supersession | holds |
| E9a | yield | `0`, `bool` | `ff` | `[]` | κ stored and resumed after its handler returned | holds (`takeProg` shape) |
| E9b | yield | `0`, `bool` | `tt` | `[]` | κ stored and cancelled | holds |
| E9c | yield, exn | `0`, `bool ⊕ 1` | `inr ()` | `[fire (raise exn ()), finEnd exn]` | a stored κ's cancel finalises | holds |
| E10 `recon`; schemas | wait, exn, kube, log | some `F ε (1 ⊕ L)`, ε answered by `Rrec` | — | `iterTrace`ⁿ, never complete (under `Rrec`) | row variables, nesting, cancel, loops, platform | **fails** |
| R1–R4 | wait, lin | — | — | — | the witnesses of S6 (§6.1) | refused (to prove) |

The composite programs (`CompositeT1`, `Tier2Programs`, and the rejected AT05, AT06, AT07, AT08 and
AT13) are in §3.4.

---

## 7. Questions for the user

1. **Tier 1 now needs row variables.** E1, E2, E6 and E10 are A properties, so tier 1's typing is
   `J₁`: Core's unr-free rules over open rows with a rank-1 row `∀`, and no spanning. It is not
   today's kernel, which is its `∀`-free restriction (§4.3). Is `J₁` the intended tier-1 milestone?
   Or should tier 1 hold the (E) properties that need no polymorphism, leaving E1, E2, E6 and E10
   to tier 2?
2. **Rank.** Done requires rank 1: let-bound functions used at several rows, with open rows, each
   function at one answer type. No (E) program passes a polymorphic value as an argument and uses
   it at two rows, and none needs polymorphism over value types (E10 was restated so that every
   body answers `bool`, §1.6). Should done add a rank-2 program (for example
   `apply2 = λh. (h pure, h fail)` with `h` polymorphic as an argument)? Or does rank n stay with
   OQ-13? Answer-type polymorphism is not asked by any decision, and done does not ask it.
3. **Loops.** In A's loop vocabulary a loop (`unfold`, observed by `next` and `close`) is something
   any computation may build, sequence (the delay bind), handle per observation and fuel; the
   driver runs one without bound at the top. Two questions follow, and done takes no side on
   either:
   - Is "a loop runs without bound only at the top, under the runtime's driver" the intended
     reading? A does not require it: an instance with `fix` meets A and may diverge inside a
     computation at a type that is not div-free.
   - E3f types the higher-order function at a div callback's type by a typing of its own, which is
     decision 35's specialization. Should divergence instead be a row effect, so that E1's one
     typing also serves div callbacks?

   Keeping this open costs something, and done says so (§1.5 S2): `DataDiv` requires termination
   only of data answers at the pure row, so an instance that may diverge silently at a data answer
   on a non-empty row, as ML does, meets S2 and E3. If the answer is "codata", as decision 35 is
   built, `DataDiv` becomes `∀ ε A, DataTy A → DivFree (F ε A)`, which our instance already claims.
4. **B5 and OQ-43.** B5 is in done as the task asks, stated in `fresh_run_image`'s direction (§2.4).
   Given the step-for-step simulation (TwoRun's, extended to block renamings and the remaining
   steps: OQ-43 (b), or a binary FP, (c)), B5 is a corollary of B3 and B4 (B4′ with externs), and
   it excludes no typing that they admit. So B5 in done costs only that machine lemma, and it
   excludes OQ-43 (a) for done. Confirm?
5. **OQ-56.** Done is fixed at `admClosedOp` until OQ-56 is chosen. `asyncRead` (`read(&mut buf)`,
   with the lend passed to the operation) is pending OQ-56 and is not in done; `at04` stands in for
   it. When OQ-56 is chosen, should done move to that `Adm`, and `asyncRead` join `Tier2Programs`?
6. **"No sum for failure."** A carries failure as an effect at an unchanged answer type (E1, E5, E7,
   E8). It does not carry "no API returns a sum for failure", which is a library rule. Is #168
   outside A?
7. **`AGREE.md`'s decisions.** This design takes positions on AGREE 4 (externs: W's contract as
   a stated hypothesis, §5.3), AGREE 5 (B5 in done, §2.4) and AGREE 6 (done split from the proof
   device, §3.7); the user's confirmation is still asked. Unchanged and still open:
   - AGREE 1 (the σ = [] reading);
   - AGREE 2 (conservativity's scope: done now holds no conservativity statement; `EmbedsNil` and
     `ConservativeWB` are beside done, since neither has been checked against every OQ-8 clause
     set, and `WBCore` is a proved companion lemma, §3.6);
   - AGREE 3 (the freeze binder beside done);
   - AGREE 7 (T1's scope: data answers, main's row the platform's);
   - AGREE 9 (`UpdReclaim` in done?);
   - AGREE 10 (the `→` half of the `Upd` pin, which constrains OQ-44).
8. **Externs at resuming rows.** Their contract is W's, as a stated hypothesis (§5.3). Is that the
   intended reading of "outside the proofs by design"? With `EmbedsNil` beside done, the SPEC's
   row-abortive externs at Core's own contract (`SoundnessContractsAR`) are a corollary of done
   together with `EmbedsNil`, not of done alone. Is that acceptable, or should checking `EmbedsNil`
   against OQ-8's clause sets be done first, so that it can return to done?
9. **OQ-50.** Done now states the continuation's use count (S6, `ContUse`): never more uses than
   catches on any run, and exactly as many on a complete run at a data answer. So done no longer
   settles for OQ-50 (c), the resource half alone. S4, and `capture` as a value, exclude OQ-50 (b),
   the one-shot-cell machine (§1.5). That leaves (a), or the logical relation with a ghost token, as
   S6's proof route. Confirm both? If (b) should stay open, A would carry the continuation's cell:
   `capture` as a relation on configurations, and S4's catch, resume and cancel laws up to steps
   that touch only that cell.

---

## 8. Build order (when told)

1. **`Targets/A/*`, with no import of ours:** `EffAlg` (moved); `EffectSystem`; the derived
   notions and the schemas' vocabulary; `MachShape` (with the named frames' laws, the driver frame
   `driveF`, `AppLaw`, `LoopLaws`, `DriveLaws`) and `LetLaw`; S1–S6; the (E) programs, schemas and properties; `Props`;
   A₂ and A₃ stated, with `Tgt` and its reference programs; `A/NonVacuity.lean` with the abstract
   lemmas of §6.1 (`not_noColouring_of_monoCallback` and its three siblings, `not_loops_of_total`,
   `divInTypes_of_loops`, `not_der_unhandled`). `lake build Targets` stays green.
2. **The moves**, with the restatements of §4.6 (`coreW` → `coreB`, `SemWorld` → `BWorld`, each by
   the same proof): `Base/`, `B/` (with `BWorld`), `I/` (with `SemWorld extends BWorld`),
   `Instance/`, with `Defs/Ctx.lean` and `Defs/Programs.lean`'s answering implementations in base,
   `Statements/Conservativity.lean` in B, and `Statements/Handlers.lean` split (P11 to I, T2 to
   `Instance/Binary.lean`). Check the import discipline against §4.5's table: base imports no A; B
   imports no A, no I and no Instance; the Instance imports no B and no I. `ExtendsB` and
   `extendsB_tier1` in B.
3. **`ourInst orowRF Ξ` at `tier1Open`:** `AdmEff`; Core's `Kont` marked with the driver's phase,
   with the named frames and `driveF`; the encodings, `AppLaw`, the loop interface and the drive
   phase; `runnerOf`, `platformOf`, `runs_platformOf` and `runs_platformOf_drive`; `det_ourInst`;
   and the hypothesis-taking bridges of §4.1; an interpreter for `ourInst`'s steps, proved to agree
   with them, to compute the (E) runs.
   Then the positive (E) lemmas E3–E9 at `tier1Open`, `monoCallback_tier1Open`, and the S6 witnesses
   `not_contUse_of_der_R*`, with their inversion lemmas (D21 cost: one lemma per constructor on each
   spine).
4. **I:** `I/Restricted/InstanceProps.lean` (the discharges: `effSafe_tier1` moved and re-proved,
   `effSafeDriveOfFL` and `effSafeDrive_tier1`, `effSafe_ourInst_tier1Open`,
   `safety_ourInst_tier1Open_none` with the stuttering simulation to `SoundDriveAt`,
   `not_noColouring_tier1Open` and its siblings); `Combined`, `Pins`, `spanRules_J₂` (when `J₂`
   exists), `Accepts` (with `AcceptedAt`), `Rejects`, `Device` (with `EmbedsNil`); the restated
   corollaries of §4.6, and the kept reduction `Tier1Core`, `status_tier1Core_of`; `genSelf` and `reconB` as Core terms, with their runs exhibited; AT05, AT06,
   AT07, AT08 and AT13 as Core terms, with AT07's stuck run.
5. **B5:** `Named`, `Expr.mapLoc`, `Heap.push`, `Bump`, `BumpSim` (stated), the restated
   `ReleasedOnceReuse`, `releasedOnceReuse_of_bumpSim`, and `staleFree`. Proving `BumpSim`, TwoRun's
   `run_sim` extended, waits on §7 Q4.
6. **The extended audit** with `stepW₁` to `stepW₈`, and `coreW`'s report pinned as computed in
   §5.2.
7. **`J₁`**, when the user confirms §7 Q1–Q2: the open types, the row `∀` rules at `U` and `!U`,
   `ovalW` and `FLOpen` at `J₁` (and so `FL M ⟦J₁⟧`), `rowVarKernel_J₂`, and A's (E) at
   `ourInst J₁`.
8. **`Status.lean`, `AxiomCheck.lean`** (definitions included, the AGREE minor finding), and
   `README.md`; the corrections of §5.1; the notebook's `system-a.md`, `system-b.md`,
   `interaction.md`, `register.md` and property pages.

Use targeted builds only (`lake build Targets`). No Core edits, and no commits until told.

---

## 9. The reviews' findings, and where each is resolved

### 9.0 The third review

| finding | severity | resolved in |
|---|---|---|
| A's matchers (`RStep.io`, `StopsIn`, `OpStuck`, S4–S6) never match a driven configuration at our instance, since `plug K (perform …)` is a `main` term: io never fires under the driver, E3a's `EffSafe`, `Loops` and `Reconciler` fail, `runs_platformOf` and `safety_of_sound` break for driven programs, and S4–S6 say nothing inside a driven loop | blocker | **the driver is a context**: a named frame `driveF` with `plug driveF M = drive M`, catching nothing, stopping nothing, holding nothing, so every law stated in every context holds inside a driven program with no matcher changed (§1.3, §1.4). `DriveLaws`' first clause is now `Congr` at `driveF`, and its last reads `∃ v, term c = drive (ret v)`. At our instance `Kont` is Core's `Kont` marked with the phase, a frame other than `□` builds a `main` term, the hole passes the phase, `driveF` is `(□, drive)` (§4.1); the laws relate driven configurations to driven ones, since the mark sits in the outer context they rebuild. Plugging is no longer asked to be injective: no property reads it, and the driver frame is idempotent at our instance. Re-checked: `runs_platformOf_drive` against the library's drive, a stuttering simulation from `Safety`'s driven clause to `SoundDriveAt`, and `EffSafeDrive` with `effSafeDriveOfFL` for S3 in the drive phase (§4.1, §3.5) |
| E6's schema `PolyUseOpen` types `fwrap`'s callback at `li ⊙ ε` and the use at `ε`, which is the accidental handling E6 excludes | major | `PolyUseLacks [Af] li …`: every callback row without `li`, callback and use at the same row, Zhang–Myers' `∀α. (N → [N]α) → [N]α`; `CallsThrough (· ≠ li)` kept; `not_tunnel_of_monoCallback` unchanged; `fwrap`'s type at `J₁` stated (§1.6, §4.2, §6.1) |
| done does not say what Ξ and `RF` are, so `A.Props (ourInst J₂)` does not elaborate, and the choice changes what done means | major (and a minor) | `Combined RF J M Adm c` with `∀ Ξ, AdmEff Ξ → A.Props (ourInst RF Ξ J)`: the effect algebra at every admissible effect context; done and tier 1 at `orowRF`, fixed until OQ-13's remaining question as `admClosedOp` is until OQ-56; `AdmEff` defined (§0, §3.5, §4.1); the change in §4.6's table; `Tier1`, `combined_prog` and the corollaries take the binding |
| `DataDiv` claims termination only at the pure row, unsaid | minor | stated in S2 and §7 Q3, with the strengthening to every row if Q3 is answered "codata" (§1.5, §7) |
| "any calculus with general recursion defines" the loop formers, overstated for `drive` | minor | `unfold`, `next`, `close` definable from general recursion; `drive` the runtime's primitive driver (decision 35), each transition one `top` step (introduction, §1.1, §1.3, §1.6, §1.8) |
| survey #11 (a resumption under a different handler) not listed | minor | impossible by construction: S4's deep resume reinstalls κ's own handler (§3.4) |
| the zero-cost corpus leaves out every driven program, E10 included | minor | the omission noted, and a per-iteration statement planned for when A₃ is taken up (§1.7) |
| A₂'s `CtxApprox` needs a context typing A lacks | minor | a closing context is a term with a hole variable of a type at which both thunks are typed, which the let law binds; no new judgement (§1.7) |
| `ContractsW`'s non-vacuity argued from `FL`, which gives a computation, not `M.val` at the nil index | minor | restated: done does not claim the contract inhabited at a non-empty `Γ`; beside done it is at row-abortive types through `EmbedsNil` and `ExternsMeet`; at other types no route is claimed, and what one would need (`EffInterp` with an `UpdRefl`-shaped zero-step law) is said (§5.3, §6.2) |
| `EmbedsNil`'s neutrality asserted, not checked against OQ-8's clause sets | minor | checked as far as it goes: any clause set with a future-world quantifier in a value clause makes `EmbedsNil` at a thunk or arrow type read every W-future of nil, `ConservativeWB`'s content there; so it moves beside done, into the device, and `SoundnessContractsAR` becomes a corollary of done together with `EmbedsNil` (§3.3, §3.5, §3.6, §3.7, §5.3, §7 Q7, Q8) |
| B0 in B's table, but its Prop only in `I.Pins` | minor | `ExtendsB` (the effect-free part of `ExtendsNU`) in `B.Guarantees`; `ExtendsNU` stays in `Pins` (§2.2) |
| the re-homing bookkeeping incomplete: the tier-1 reduction retired, status rows whose types change unlisted, `effSafe_tier1`'s changed proof unsaid | minor | `status_tier1Core_of`, the reduction kept at `tier1Open`/`coreW` from `Adequate coreB`, the cancellation bridge and `BumpSim`, beside `status_tier1_of`; the status rows whose statement types change, listed; `effSafe_tier1` re-proved with `⟨famEmpty_core, adequateEvery_core⟩` (§3.5, §4.5, §4.6) |
| `SpanRulesAt` and `I4a` kept in done while `RowVarKernel` was demoted, with no reason | minor | `SpanRulesAt` demoted to the recorded lemma `spanRules_J₂` (no decision names the six rules; done keeps `Tier2Programs` with `ExtendsNU`); `I4a` kept, with its references: I4 is a rule of the interaction the brief names, in decision 57's form (§3.2, §3.5) |
| §5.1's grep and table disagree | minor | two case-insensitive greps, the first widened with `finalis[a-z]* exactly once`; every hit listed, to correct or with the reason it stays (`tracks/log.md`: dated log entries; `AxiomCheck.lean`: the rename only; I3's title "drop finalises exactly once" stays) (§5.1) |

No finding of this review was of the kind the good-faith rule excludes, and nothing further was
removed as hardening. The machine lemma B5 rests on is now named (`BumpSim`, §2.4), which the kept
tier-1 reduction takes as a hypothesis.

### 9.1 The second review

| finding | severity | resolved in |
|---|---|---|
| E10 untypable at rank 1: `timeout` and `retry` used at two answer types, so done forced value-type polymorphism | blocker | E10 restated: `timeout` answers its default `ff` when it cancels (the clause `cancelCl`), `retry` answers `ff` when the second attempt fails, so every body and use is at `bool` and only rows vary; the schemas at `bool`; `iterOpen`, `iterTrace` (`log ff`) and `reconB`'s answer `(tt, ff)` recomputed (§1.6, §3.4); §4.2's rank bullet and §7 Q2 say that no (E) program needs answer-type polymorphism |
| S6's exactly-once clause false at a complete run ending in a closure over κ | blocker | the clause restricted to data answers, S2's scope (`S.DataTy A → …`); the prose says why, with Tang Thm 3.6's preservation shape; R1–R4 are at `F 0 bool`, so they still bite (§1.5, §1.8, §3.2, §7 Q9) |
| the contexts where finalisers run (`Kp`, `Kf`) had to be named A-frames, which Core's `seq`, `cfin` and `ccatch` are not | major | our instance's `Kont` is Core's whole `Kont` (marked with the driver's phase since the third review); A names four frames (five since the third review, with `driveF`) and states their laws, and the decomposition laws that forbade other frames are removed (good faith, §9.2); `Kp`/`Kf` range over the instance's contexts; the finaliser law, `NoIntercept` and `UnwindOrder` re-checked against `ufin`, `ufinC`, `cfret`, `cferr`, `cancel`, `creraise`, `CancelRun` and `UnwindRun` (§1.3, §1.4, §1.5, §4.1) |
| the loop formers listed as v1's decreed mechanism, yet kept as fields | minor | the introduction says what changed (no `Loop` type, no typing rule, laws that say only what the formers do); §1.3 says once that they are vocabulary which any calculus with general recursion defines |
| rows as sums of signatures justified by decree | minor | stated as an (S) well-formedness requirement that gives `has` its meaning (Kammar), not as something (E) forces (§1.2, §1.8) |
| the home table broke the import rule three times | minor | `Conservativity.lean` in B; `Defs/Ctx.lean` and the answering implementations of `Defs/Programs.lean` in base, so `Instance/Binary.lean` imports no I; `exclusiveB_core` proved in `B/BoLo.lean` from `TW.valid`; the import check, file by file (§0, §2.1, §4.5, §4.6) |
| B1 and B7 read at `⟦J⟧`, which drops open judgements with a row `∀` | minor | said in §2.2 and §4.2: B1 and B7 in done are at `∀`-free judgements by choice; the relation at the open types is I's `ovalW`, and `FLOpen` (beside done) is the route to `FL M ⟦J⟧` (§3.5, §3.7) |
| AT07's rejection stated at every type | minor | stated at the types `Sound` covers: a data answer on a row a respecting platform answers (§3.4) |
| "A and B meet only in I, in definitions and in proofs" overstated | minor | §0 reworded: in proofs, only in I; in statements, the Instance's bridges take the base's run statements as hypotheses, which B also reads |
| B5's dependence on B3, B4 and the machine lemma unsaid | minor | §2.4: B5 is a corollary of B3 and B4 given the step-for-step simulation; its existence half is B3's progress, not `run_sim`, which takes the fresh run as given; `staleFree` shows B5 is not a tautology, not that it excludes more than B3 (§6.2, §7 Q4) |

### 9.2 Hardening removed (good faith)

These were in the previous draft only to block contrived instances. Each is removed, and the
property is stated as its plain reading allows.

| removed | where | what stands instead |
|---|---|---|
| `KontLaws`' decomposition laws ("what catches is a handler frame of the label; what stops a raise is a finaliser frame") | §1.4 | the named frames' laws and the frame-by-frame computation of `catches`, `unwindClear`, `fins`; the instance's other frames are its own |
| `HandlerRed` (a store-preserving step is its configuration's only step) | §1.5, `SProps` | S4's laws as joins; Core's determinism up to allocation as the Instance's lemma `det_ourInst`, used to compute runs (§4.1, §6.1) |
| `LetLaw`'s elimination half ("typed once" made exact) | §1.4 | the let rule at a closed value; E1 already asks one type `A` for `hof` |
| the argument that S6's observation "is not cheated" | §1.5 | — |
| the claim that a schema "is not met by listing chosen judgements" | introduction | the schema stated as effect polymorphism, in Zhang–Myers' shape |
| "so the programs below cannot be met by special-casing them" | E3 | `LoopLaws` and `DriveLaws` say what the formers do |
| "a lowering that pads its handler-free programs" | A₃ | the baseline is the hand-written equivalents |
| "a world cannot make its guarantees vacuous" | §6.2 | B's guarantees at W mean what they mean at Core |

### 9.3 The first review

| finding | severity | resolved in |
|---|---|---|
| A's properties met without row variables or effect polymorphism | blocker | the schemas `PolyUse`, `PolyUseLacks`, `PolyUseOpen`, `CallsThrough` (§1.3) in E1, E2, E6, E10 (§1.6); `LetLaw` (§1.4), with value substitution considered and not added (§1.4); `MonoCallback` and `not_noColouring_of_monoCallback` with its siblings (§6.1); E1's justification and §1.8's row rest on them; `RowVarKernel` out of `Pins`, a recorded lemma (§3.5, §4.2) |
| no bind or application frame; instance frames unconstrained | major | `bindF`, `appF` and `AppLaw` (§1.3–§1.4); S3 and S4 under binds (§1.5). The instance's own frames are its own (good faith): the decomposition laws that constrained them are removed (§9.2) |
| the discipline a blacklist of four terms | major | S6 `ContUse`, universal, observed from the run's terms (§1.5); R1–R4 its witnesses (§6.1) |
| loops only as whole programs | major | the loop vocabulary `unfold`/`next`/`close` and the driver, with `LoopLaws`, `DriveLaws` (§1.3–§1.4); E3a–g (§1.6); §7 Q3 |
| answers not typed by S2 | major | S2's answer clauses (§1.5) |
| S4 excludes OQ-50 (b) silently | major | said in §1.5; §7 Q9; §1.7 no longer claims OQ-50 open |
| traces drop fire and finEnd | major | `obs` keeps them (§1.3); E7, E8, E9c state them (§1.6) |
| `ZeroCost`'s baseline supplied by the instance | major | `Tgt.ref` and `Tgt.refCost`, fixed in A (§1.7) |
| E6 a corollary of the frame laws | minor | E6 restated with `fwrap`'s schema, the corollary parts said, T3 the substantive form (§1.6) |
| multi-shot mentioned in a Lean docstring | minor | `OpClass`'s docstring (§1.3); the rationale in prose only (§1.7) |
| `[allR-I]`/`[allR-E]` cannot type E1 or E2 | minor | the rules at `U` and `!U`, and E1's and E2a's derivations checked against the linear context (§4.2) |
| no real suspension in E1; `at04` called the async read | minor | E1′ (§1.6); `at04` labelled a stand-in (§3.4, §7 Q5) |
| proofs of A properties homed in the Instance using B | major | §0's rule for proofs; the Instance's bridges take hypotheses (§4.1); the discharges in `I/Restricted/InstanceProps.lean` and `I/Restricted/CompositeT1.lean` (§4.3, §4.5) |
| B5's permutation cannot split a name | major | B5 in `fresh_run_image`'s direction, with bump runs and per-step maps injective on the live heap (§2.4) |
| the audit misses `Nat.casesOn`, unfolded index types, `n + 1` constructors; `ARun`/`AHead` unjustified | major | §5.2: items 1, 2 and 5 extended, `stepW₇` and `stepW₈`, `coreW`'s report computed and justified |
| `AcceptedAt` undefined, and its dependence on OQ-43 unsaid | minor | `AcceptedAt` defined on one run, resting on no machine lemma (§3.4) |
| §6.2.1 overstated what reads no world | minor | §6.2 item 1, §5.3 |
| I3's done column said "releases what the continuation held" | minor | §3.2 |
| the correction list incomplete | minor | §5.1's rule and table |
| `coreW` → `coreB` restatements and `WBCore`'s removal unlisted | minor | §4.6 |
| `Interface` ignored `J`; `Adm` free in done; `⟦J⟧` undefined | minor | §3.3, §3.5, §4.2 |
| `platformOf R` undefinable in general | minor | `platformOf R ε` and `runs_platformOf` (§4.1) |

---

## Unresolved, and the build

The build of this design is the commit on `targets` that adds this section. It follows §8 through
step 6, and step 8. Step 7 (`J₁`) waits on §7 Q1–Q2, and `W` is not built in this pass. This section
records what the build leaves open: the third review's findings, answered in the text and not
reviewed again (U.1); every place the Lean departs from this text (U.2); everything §8 asks for that
is not built (U.3); and what was proved beyond the moves (U.4). `Targets/Status.lean` is the record
of status.

### U.1 The third review's findings, answered and not reviewed again

The third review (§9.0) ended with one blocker and two major findings. The text was revised in
answer to each, and the revision was not reviewed again. The build implements each revision as
below. Whether a revision answers its finding has not been checked.

1. **Blocker: A's matchers never match a driven configuration at our instance.** Revision: the
   driver is a context. Built:
   - `EffectSystem.driveF : Kont` (`Targets/A/System.lean`).
   - `KontLaws` asks `plug driveF M = drive M`, and that `driveF` catches nothing, is unwind-clear and
     holds no finaliser (`Targets/A/Machine.lean`).
   - `Congr` holds in every context, `driveF` included, at every step but a `top` step.
   - `DriveLaws` asks that each of the driver's two transitions be the only step of its
     configuration, and that every `top` step start at `drive (ret v)`.
   - `DataInj` adds `drive M ≠ ret w`.

   At our instance the driver is a Core frame around the program, `driveK = appR driveMark □`, and
   not a phase mark (U.2, item 19). **Unchecked:** the bridges that would prove these laws at our
   instance (`Congr`, `DriveLaws`), `runs_platformOf_drive`, the stuttering simulation to
   `SoundDriveAt` and `effSafeDriveOfFL` are not built (U.3). So it is not verified that a driven
   configuration of our instance meets A's matchers.
2. **Major: E6 used `PolyUseOpen`.** Revision: `PolyUseLacks`. Built: `Tunnel`
   (`Targets/A/Expressiveness.lean`) states `PolyUseLacks [Af] li (fun g => call (var 0) g) bool bool`
   with `CallsThrough (· ≠ li)`, and `not_tunnel_of_monoCallback` is proved against it.
   **Unchecked:** `fwrap`'s type at `J₁`, which is not built.
3. **Major: done did not bind Ξ and `RF`.** Revision: `Combined RF J M Adm c`, with A's properties
   at every admissible effect context. Built:
   - `I.Combined (RF) (J : OurTyping RF) (M) (Adm) (c)`, whose first conjunct is
     `∀ Ξ, AdmEff Ξ → (ourInst RF Ξ J).Props` (`Targets/I/Combined.lean`).
   - `AdmEff Ξ := Ξ.NU ∧ Ξ.ClosedLife ∧ Rich Ξ` (`Targets/Instance/Core.lean`).
   - `Tier1 J₁ := Combined orowRF J₁ coreW admClosedOp .abortive`.
   - `combined_prog` and the other corollaries take the binding.

   **Unchecked:** whether `AdmEff` is the right range (neither too narrow nor too wide) has not
   been reviewed. A's properties are proved at no Ξ.

### U.2 Where the Lean departs from this text

| # | where | this text | the Lean | why |
|---|---|---|---|---|
| 1 | A: `AppLaw`, `LoopLaws`, `DriveLaws` (first two clauses), `HandlerSem` (all seven) | at every configuration | each takes `Live c`: `c` is reached from a typed closed program under a runner that keeps its protocol | A's values include variables, and a calculus steps on closed values only, as the literature's reduction rules are stated for closed terms. At an open configuration each law would ask for a step that our machine, and any machine that reduces by substitution, does not take |
| 2 | A: `unfold` | `Val → Val → Val → Val` | `Ty → Ty → Val → Val → Val → Val`: the loop's answer type and close type. The loop programs pass them (`tickL`, `countL`, `divF`, `spinL`, `handleL`, `reconBody`, and `seqL A`) | our instance's `unfoldV` is type-directed: its code depends on the value types (not on the row, item 21) |
| 3 | A: curried functions (`twice`, `compose`, `retryP`) | `lam (lam M)` | `lam (force (lam M))` | `lam` takes a term, and `lam M` is a value |
| 4 | A: `KontLaws`, the handler clause | `catches (handleF l H) m = decide (m = l)` | `catches (handleF l H) m = true ↔ m = l` | `EffAlg` gives labels no decidable equality |
| 5 | A: E1's program | `uses` | `threeUses` | S6 has a count named `uses` |
| 6 | A: `e3cBody` | takes `lt` | takes no argument | `lt` is unused |
| 7 | A: S5's mutual traces | `FinTrace`'s `Kf` and `PendTrace`'s `K₂ Kp p` as parameters | as indices | Lean's mutual inductives share their parameters. The content is unchanged |
| 8 | A: `divInTypes_of_loops` | `Safety`, `DataDiv`, `Loops` | also `RowAlgebra` | the runner that answers nothing answers the pure row only if the pure row admits nothing (`RowSig`) |
| 9 | A: `not_reconciler_of_monoCallback` | the same hypotheses as its three siblings | also `LiftExt`: two distinct labels compose, and the second's row is below the composite | `SubClosed` puts `timeout`'s callbacks at `wait ⊙ ε`; at `ε = (exn)↑` that needs the composite. `LiftExt` is proved at our rows (`liftExt_orow`) |
| 10 | A₃: `Tgt` | `Exp.prim (o) (as : List Exp)`; `Fn` with `params` and `locals`; `Stmt.io (d) (lab op) (arg)`; `Run` an inductive | `Exp.prim (o) (a b)`; `Fn` with `params`; `Stmt.io (ds) (lab op) (args)`; `Run` from a big-step `Call` relation that counts allocations and dispatches | encodings (Conventions: encodings are the builder's). No instruction captures, saves, restores or searches a stack, as asked |
| 11 | A₃: `LoweringCorrect`, `ZeroCost` | through the A-defined functions `L.tgt R`, `dataEnc` and `ioEnc` | through relations. Both quantify over every target platform `ρ` with `PlatformSim L R ρ`, and read answers and traces through `DataEnc v ws` and `IoEnc L tr trT`. `LoweringCorrect`'s two directions are stated separately | a runner's state type is arbitrary and `dataEnc` is defined on data values only, so a runner's target platform is related to it, not computed from it |
| 12 | A₃: the references | `ref : CorpusId → List ℕ → Prog`, with `refCost` checked by running it (`refCost_spec`) | `refCost` is `(0, 0)` at every entry, the claim that each hand-written equivalent allocates nothing and dispatches nothing. `ref` and `refCost_spec` are not written, so the claim is not checked | U.3 |
| 13 | B: `BumpSim` | a docstring only | `∀ P X g cA cA' cB, RelAt g cA cB → BlocksAffine g cB.μ cB.e → PStep cA cA' → (∃ cB'', PStep cB cB'') → ∃ cB' g', PStep cB cB' ∧ (every location the step allocates is unnamed in cB and outside X) ∧ (g' agrees with g on what cB names) ∧ RelAt g' cA' cB' ∧ BlocksAffine g' cB'.μ cB'.e` (`Targets/Base/Machine.lean`) | the finite set `X` lets the bump run avoid the names of all its earlier configurations, which `Bump` asks for. `BlocksAffine` (`g` moves each array block as a block) is needed because array steps compute `ℓ + j` |
| 14 | B: `ReleasedOnceReuse` | four per-step conjuncts | `RelAt (g k) cA cB` | the same four conjuncts, named |
| 15 | B: where `releasedOnceReuse_of_bumpSim` lives | `B/Guarantees.lean` | `B/Routes.lean`, with the run induction `bump_follows` in `B/Release.lean` | the proof uses `releasedOnce_of_ends` (`B/Release.lean`), which `B/Guarantees` does not import |
| 16 | I: `Tier2Programs` | six programs, `reconB` among them | five | `reconB` is not built (U.3) |
| 17 | I: AT07 | `rejects_at07_of_sound`, a derived lemma | `RejectsAT07 J`, the lemma's conclusion, as a definition | the lemma needs AT07's stuck run written out (U.3). `at07_eval` checks the interpreter's run (`.stuck .useAfterFree`) |
| 18 | I: the tier-1 reduction | `status_tier1Core_of : Adequate coreB → FinaliserOrder tier1 → BumpSim → Tier1Core`, in `I/Restricted/Tier1Core.lean` | `Tier1Core` with three lemmas in `I/Combined.lean`: `tier1Core_world` (the world conjuncts and the device at `coreW`); `tier1Core_B_of` (B's guarantees but B5, from `Adequate coreB`); and `tier1Core_guarantees_of` (all of `B.Guarantees`, from `Adequate coreB` and `BumpSim`) | `Tier1Core`'s A conjunct needs the Instance's bridges, which are not built. Of the rest, the world conjuncts, the device and `WBCore` are proved, B's guarantees follow from `Adequate coreB` and `BumpSim`, and the pins lack only `I4a` at today's unr-free kernel |
| 19 | Instance: `ourInst`'s values, terms and contexts | `Val` is Core's `Val`; `Term := Expr × Phase`; contexts are Core's `Kont` marked with a phase; `driveF := (□, drive)` | `Val := OVal`, the expressions in value form, variables included. `Term := Expr`, and contexts are Core's `Kont`. `drive M := driveE M = app driveMark M` and `driveF := driveK = appR driveMark □`, where `driveMark` is a literal that Core never applies. The driver's steps are `OStep.again` and `OStep.fin` | A's `var` needs variables among the values, and Core's `Val` has none. A phase is lost when a finaliser is stored in a frame, so `fins (thenF N D) = [D]` would fail for a driven `D`. As a frame, the driver is a term like any other, and `KontLaws` holds by computation (`kontLaws_ourInst`) |
| 20 | Instance: junk values | — | where an A-former gets a variable where Core needs a value (`appK`, `captureE`, `cancelOfE`, `unfoldE`), it reads it as a junk value | no configuration that a typed closed program reaches has one (`Live`, item 1) |
| 21 | Instance: `unfold`'s row | `unfoldV (loopEffBody S A 1)` | `unfoldV (loopEffBody [] A B)` | A's `unfold` has no row. `unfoldV`'s code is the same at every row: `nodeV` reads only the answer type of `effOf S A` |
| 22 | Instance: `has` | `Row.Has (RF.den Ξ ε η) n i` at every `η` | also `i < 2^32` | operation indices are `UInt32` |
| 23 | Instance: a driven program's type | the loop sum `F_S (A ⊕ U(Loop_S A 1))` | `IsLoopSum`: the loop's row `S₀` is below the step's row `S` | `[sub]` weakens the step's row, not the loop's |
| 24 | Instance: `OurTyping` | `der`, `out` | also `env`, the row form's variables as row variables, through which `F` reads a row. `read` (`⟦J⟧`) is pointwise: at each admissible instance, a derivation at the empty row context | a syntactic conclusion at the row context would not hold of a family that no open type denotes, and `ExtendsNU` asks for every family of today's rules |
| 25 | Instance: `kontLaws_ourInst` | — | takes `Function.Injective (RF.name Ξ)` | `handleF l` must catch `l` alone. Proved at `orowRF` (`kontLaws_orow`) |
| 26 | Audit | the library's audit pins item 1's first four rows; each negative test asserts that its report is non-empty; eight toy worlds | every report is pinned at `coreW`; each negative test checks the toy's own entry; a ninth toy, `stepW₉`, has its predicate as the second binder of its `∀` telescope | every toy shares `coreW`'s closure, so a non-empty report says nothing about the toy. `stepW₉` checks that item 3 reads every binder of a telescope. Item 3 reads `∀`-bound predicates only, and its report at `coreW` is §5.2's computed one: `Table`, `ewpTS`, `vCE._f` |
| 27 | AxiomCheck | definitions as well as theorems | also fails on any `opaque` or `axiom` constant, any `implemented_by`, and any unsafe definition other than the compiler's `._unsafe_rec` copies | the hygiene the build asserts |
| 28 | Status | `status_releasedOnceAll` and `status_p8a_of_endState` both re-pointed to `releasedOnceAll` | `status_releasedOnceAll` kept; `status_p8a_of_endState` retired | both would state the same lemma |
| 29 | `Targets/Checks/RunEnd.lean` (untracked, not imported) | left to the builder | deleted | superseded: each of its 17 theorems has a same-named successor in `Targets/I/RunEnd.lean`, stated against the field `Upd` |
| 30 | §5.1's corrections in `DESIGN.md` | each listed line corrected | a note at the head of `DESIGN.md` and one at D9 say that every statement presenting `ReleasedOnceAll` or P8.a as carrying exactly-once release is superseded, and by what | `DESIGN.md` is superseded in part by this file, and its 35 lines are statements of the old architecture. Every other document and Lean file in §5.1's table is corrected line by line |

**Status rows merged or renamed** (each theorem kept; §4.6's list, as built):

- `status_rowAlgSafe_orow` and `status_rowLink_orow` became `status_rows`.
- `status_outExtends_core` became `status_extendsNU_tier1`, which states both.
- `status_I1_core`, `status_I2_core_abortive`, `status_I3_core`, `status_I5_core` and
  `status_P11_core` became `status_device_core`.
- `status_exclusive_core` is now part of `status_tier1Core_world` (I's `Interface`).
  `status_exclusiveB_core` is new (B6).
- `status_conservativeWB_core` became `status_conservative_core`, which states both.
- `status_redLaws_of_mono`'s row was dropped. The theorem `redLaws_of_mono` is kept
  (`Targets/I/Restricted/Device.lean`).
- `status_endState_prog` became `status_combined_prog`.
- `status_i1Prog_of_endState` and `status_i2Prog_of_endState` became `status_progs_of_combined`.
- `status_not_endState_of_leak` became `status_not_combined_of_leak`.
- `status_carryW_laws` and `status_carryW_printed` became `status_carryW`.
- `status_tier1End_of` was retired. Its proved content is `status_tier1Core_world`,
  `status_tier1Core_B_of` and `status_tier1Core_guarantees_of`.

### U.3 Not built

- **Waiting on the user, or not built in this pass.**
  - `J₁` and `J₂` (§7 Q1–Q2), and `W` and `audit_W`, so `done` is not built.
  - With them: `spanRules_J₂`, `rowVarKernel_J₂`, `I.ovalW`, `I.FLOpen`, `I.fl_of_flOpen`
    (`I/OpenRel.lean` is not created), A's (E) properties at `ourInst J₁`, and `I4a ⟦J₁⟧`.
- **The Instance's bridges (§4.1).**
  - Not built:
    - `machShape_ourInst`'s semantic laws: `AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`;
    - `letLaw_ourInst`; `rowAlgebra_ourInst` (`rowSig_ourInst`);
    - `safety_of_sound`, with `platformOf`, `platformOf_respects`, `runs_platformOf`,
      `runs_platformOf_drive`, `DRunOf` and the stuttering simulation;
    - `effSafe_of_core`, `handlerSem_ourInst`, `noIntercept_of_core`, `unwindOrder_of_core`;
    - `runnerOf`, `det_ourInst`;
    - S6 `ContUse` at any instance.
  - Proved: `ConfLaws`, `KontLaws`, `NoIO`, `DataInj` and `LiftExt`
    (`Targets/Instance/Bridges.lean`).
- **I's discharges (§4.5).** `effSafeDriveOfFL`, `effSafeDrive_tier1`, `effSafe_ourInst_tier1Open`,
  `safety_ourInst_tier1Open_none`, and `not_noColouring_tier1Open` with its three siblings.
  `I/Restricted/InstanceProps.lean` holds `effSafe_tier1` only.
- **§6.1's concrete lemmas, at our instance.**
  - `monoCallback_tier1Open`: an inversion, D21 cost.
  - `not_tier2_tier1`.
  - `not_contUse_of_der_R1` … `_R4` and `refuses_R_tier1Open`. R1–R4 are A programs
    (`Targets/A/Programs.lean`).
  - `eN_tier1Open`: the positive (E) runs at `tier1Open`.
  - An interpreter proved to agree with `ourInst`'s steps.
  - `Instance/NonVacuity.lean` is not created.
- **The composite.**
  - `reconB`, its Core term and its interpreter run.
  - `rejects_at07_of_sound`.
  - `CompositeT1` at a `J` beyond `tier1`: of its NU derivations, only `d_storeCancelNU` exists.
  - `Accepts`, `Rejects` and `Tier2Programs` at any typing system.
- **B5's machine lemma.** `BumpSim` (OQ-43, §7 Q4) is not proved. `releasedOnceReuse_of_bumpSim`
  is, so B5 at tier 1 follows from `BumpSim` and `Adequate coreB` (`tier1Core_guarantees_of`).
  Its side condition `BlocksAffine` reads the array values `(ℓ, n)` (`Val.arr ℓ n`) that the term
  or a stored value holds (`Expr.MentionsArr`), and asks `g (ℓ + j) = g ℓ + j` for `j ≤ n`: `idx`
  computes `ℓ + j` for `j < n`, and `split` bases its last part at `ℓ + n`. An earlier reading
  left `n` unbound, so it constrained `g` above every named location, and a verifier refuted
  `BumpSim` at an `alloc` step with a finite `X` (heap `{5 ↦ loc 5}`, `g = id`, `X = {3}`). At the
  current reading `bumpSim_at_reuse` (`B/NonVacuity.lean`) meets `BumpSim`'s conclusion at that
  step for every `X`. Reading `j < n` instead is refuted at a `split` whose end location a stored
  value names (checked in scratch, not kept in the build).
- **A₃.** `Tgt.ref`, `refCost_spec`, `not_zeroCost_of_heapRuntime`, and the per-iteration statement
  for the driven programs.
- **Adequacy at BoLo** (the library's second wave): `Adequate coreB` at every platform and for the
  drive, and `AdequateOfLaws`.

### U.4 Proved in the build, beyond the moves

- **A.**
  - `not_eProps_of_emptyTyping`, `not_eProps_of_noLabels`.
  - `not_noColouring_of_monoCallback` and its three siblings.
  - `not_loops_of_total`, `divInTypes_of_loops`.
  - `not_der_unhandled`, `c1_of_rowSig`.
  - `rtick_respects`, `rtl_respects`, `rrec_respects`.
- **B.**
  - `not_releasedOnceReuse_staleFree`.
  - `releasedOnceReuse_of_bumpSim`, with `bump_follows` and its machine lemmas: heap domains stay
    finite, a value takes no step, and `Final` transfers back along a relation.
  - `bumpSim_at_reuse`: `BumpSim`'s conclusion at an `alloc` step whose given run reuses a
    location, for every finite `X`.
  - `soundContractsOfFL`, `contractsW_nil`, `releasedOnceReuse₀_of`.
  - `exclusiveB_core`, `sliceShapeB_core`, `wBound_core`, `extendsB_tier1`.
- **I.**
  - `combined_prog`, `i1Prog_of_combined`, `i2Prog_of_combined`, `effSafe_core_of_combined`.
  - `soundnessContractsAR_of_combined`, which goes through `contractsW_of_meets`.
  - `not_combined_of_leak`.
  - `tier1Core_world`, `tier1Core_B_of`, `tier1Core_guarantees_of`.
  - `sliceShapeI_core`, `embedsNil_core`.
  - `genSelf_eval`, `at07_eval`.
- **The Instance.**
  - `tier1Open_read`.
  - `confLaws_ourInst`, `kontLaws_ourInst`, `kontLaws_orow`, `noIO_ourInst`, `dataInj_ourInst`.
  - `liftExt_orow`, `orowRF_name_injective`.

---

## Sources

**Repository** (`~/repos/borrow-core-targets`, branch `targets` at `938d280`):

- `docs/effects-state/`: `BRIEF.md` (all); `04-decisions.md` (summary, §1–§8);
  `05a-open-questions-1-34.md` (header, F1–F5, OQ-8, OQ-9, OQ-10–OQ-13, OQ-23–OQ-28);
  `05b-open-questions-35-68.md` (the decisions table, OQ-43, OQ-44, OQ-50, OQ-51, OQ-56–OQ-60).
- `docs/decisions.md` (decisions 33–36, 48, 51, 55, 57).
- `research/effects/src`: `intro.md`, `system-a.md`, `system-b.md`, `interaction.md`, `register.md`,
  `decisions.md`, `SUMMARY.md`, `method.md`, `literature.md`, `foundations/*`, `properties/*`,
  `design-space/axes.md`, `side/multi-shot.md`, `tracks/*`. `research/effects/survey.md` (TL;DR,
  §1.1–§1.11, §2, §3).
- `experiments/Targets`: `README.md`, `AGREE.md`, `DESIGN.md` (§8, §9, §10, Corrections,
  Unresolved, Builder's notes, and the lines of §5.1), `FIX-RUN-END.md` (§0–§4), `RESTRUCTURE-v1.md`
  (all), `Targets.lean`, every file of `Targets/Defs/*` and `Targets/Statements/*`,
  `Targets/Audit.lean`, `Targets/AxiomCheck.lean` (header), every theorem name of
  `Targets/Restricted/*`, `Targets/Restricted/EffectSafety.lean`, `AcceptedT1.lean` and
  `Soundness.lean` in full, `Targets/Status.lean` and `Targets/Checks/RunEnd.lean`.
- The review findings: `restructure-v1-reviews.json` (all twenty), `findings2-7.json`, and the
  three reviews of earlier drafts of this file (§9).
- For the import check (§4.5), in full: `Targets/Statements/Conservativity.lean`,
  `Statements/Composition.lean`, `Statements/Handlers.lean`, `Statements/Abstraction.lean`,
  `Statements/Device.lean`, `Defs/Ctx.lean`, `Defs/Programs.lean`, `Restricted/CoreLaws.lean`,
  `Restricted/Composition.lean`, `Restricted/Transport.lean`, `Restricted/Corollaries.lean`, and
  the import lines of every file of `Targets/`.
- `SPEC.md` §14 (*Types*, *The delay bind*, *The fuel handler*, *The outermost handler*), §15, and §19
  (all, *Acceptance* and *As built* included).
- `Core/`:
  - `Types.lean` (`Qual`, `VTy`, `CTy`, `CTy.effOf`, `loopBody`, `loopEffBody`, `loopEff`, `loop`,
    `delay`);
  - `Fundamental.lean` (`CDerives`, every rule, `fundamentalC`, `reclaim`, `theorem32`, `adequacyC`);
  - `Demonic.lean` (`wpTS_demonic`, `wpTSD_safe`, `fundamentalD`, `theorem32D`, `adequacyD`,
    `adequacyD_safe`);
  - `EffRules.lean` (`Row`, `Row.find`, `OpSig.abort`, `RowLe`, `Row.Weak`, `Row.Unr`,
    `Row.abortOnly`, `Row.Uniq`, `kTy`, `clauseTy`, `clausesTy`, `retTy`, `hndTerm`, `thenE`,
    `then_compatC`);
  - `EffPrograms.lean` (the acceptance programs, `failSig`, `logSig`, `yieldSig`, `suspSig`,
    `takeProg`, `storeCancel`, `tickProg`);
  - `EffCancel.lean` (`prog`, `prog₃`, `body_run`);
  - `Nu.lean` (`unfoldV`, `etaN`, `hN`, `hN_steps`, `etaN_obs`); `DelayPrograms.lean` (`driveE`,
    `d_driveL`); `Alloc.lean` (`Alloc`, `AHead`, `AStep1`, `ARun`);
  - `Relation.lean` (`vCE`, whose `U` clause quantifies over `Ext`-futures, §3.6);
    `RelationFacts.lean` (`vC_outlives`, `vC_outlivesLe`); `Invariant.lean` (`TW.valid`, `TI`,
    `TW.inv`); `Totality.lean`; `Stdio.lean` (`ExternsMeet`, `externs_every_run`).
- `Paper/S1_Syntax/Definitions.lean` (`Prim`, `Expr`, `IsVal`, `Loc`); `Paper/S3_Dynamics/Definitions.lean`
  (`Kont` with its `seq` frame, and `Kont.plug`, `Heap`, `Kont.HasHnd`, `Kont.Catches`, `kappa`,
  `cancelVal`, `errNext`, `hndE`, `ubindE`, `ccatchE`, `cfinE`, `performE`, `raiseE`, `Head`'s effect steps `hret`, `hop`,
  `hunwind`, `uthen`, `ufin`, `ufinC`, `cfret`, `cferr`, `cancel`, `creraise`);
  `Paper/S5_Model/Definitions.lean` (`Life`, `WRes`, `WProp`); `Paper/S6_8_FundamentalProperty/Lemmas.lean:164`;
  `Paper/S6_2_NonStandardLemmas/Lemmas.lean:3620`.
- `Core/Persistent.lean` (`VTy.persistent`, `Ctx.SplitP`, `Ctx.DeadP`); `Core/EffBorrow.lean`
  (`withborUE`, `withbor1UTy`, `withbor2UTy`, `withloadUTy`, `Row.Unwind`); `Core/Steps.lean`
  (`plug_cmp`, `plug_decomp`, `head_det_eff`); `Core/FrameRecords.lean` (`SRec`).
- `Support/Dynamics/Interpreter.lean` (`eval`, with no theorem tying it to `Step1`).
- `Backend/Flat/Syntax.lean`, `Backend/Flat/Interp.lean` (the flat IR and its counters).
- `lib/div.bc` (`div_bind`, `div_fuel`); `experiments/TwoRun/README.md`, `TwoRun/Fresh.lean`
  (`Named`, `Step1F`, `FreshRun`), `TwoRun/Sim.lean` (`HeapRel`, `Heap.push`, `run_sim`,
  `fresh_run_image`); `experiments/HandlersAsBorrows` (`twoBlocks_refused`, `translate_typed`,
  `handle_is_shift`, `effect_safety`); `experiments/SecondClass` (`handleAt_compatC`).
- `docs/operator/README.md` (§0–§4); `corpus/reject/gen-self-borrow.bc`, `corpus/gen-cell.bc`,
  `corpus/pending/yield-callback.bc`, `corpus/pending/async-borrow.bc`,
  `corpus/pending/callbacks-in-data.bc`.
- **Computed for this design** (a scratch file importing `Targets.Audit`, not committed): `coreW`'s
  extended audit report, and the reports of `stepW₇` and `stepW₈` (§5.2).

**The paper.** [CONF] `3764117.pdf` (as text): 415:18 (adequacy "safe, terminating, and reclaim
memory"), Theorem 3.2, Corollary 3.3, 415:21, 415:23. [TR] `3764117-supplement.pdf` (as text):
Lemma 6.60, Lemma 6.151.

**Primary literature, read at the cited statements:**

- Plotkin–Pretnar, *Handling Algebraic Effects*, LMCS 9(4:23) 2013 (arXiv 1312.1399): abstract, §1.2,
  §1.3, Def. 4.2, Def. 4.5, the sentence after Def. 4.5.
- Bauer–Pretnar, *An Effect System for Algebraic Effects and Handlers*, LMCS 10(4:9) 2014 (arXiv
  1306.6316): abstract, Fig. 1, Thm 4.1, Cor. 4.2.
- Yoshioka–Sekiyama–Igarashi, *Abstracting Effect Systems for Algebraic Effect Handlers*, arXiv
  2404.16381: Def. 3.4, Def. 3.5, Fig. 4 (R_Handle2), Def. 5.1, Example 5.2, Lemma 5.4, Lemma 5.5,
  Lemma 5.7, Thm 5.8, Thm 5.9, Def. 7.1, Def. 7.6.
- Tang–Hillerström–Lindley–Morris, *Soundly Handling Linearity*, POPL 2024 (arXiv 2307.09383):
  Def. 3.1, Thm 3.2, Thm 3.3, Thm 3.4, Def. 3.5, Thm 3.6.
- van Rooij–Krebbers, *Affect: An Affine Type and Effect System*, POPL 2025: Thm 2.1, §2, §3.3
  (types), §5 (adequacy).
- Kammar, *An Algebraic Theory of Type-and-Effect Systems*, PhD thesis 2014: abstract, (11.1),
  Thm 12.5. It is quoted in place of Kammar–Plotkin POPL 2012, which it cites as previous work and
  whose PDF could not be retrieved.
- Zhang–Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019: abstract, Example 1,
  Thm 1, Thm 3.
- Ahman–Bauer, *Runners in Action*, ESOP 2020 (arXiv 1910.11629): Def. 1, Def. 2, Thm 7.
- Voigt–Schuster–Brachthäuser, *Dynamic Wind for Effect Handlers*: Thm 3.6.
