# RESTRUCTURE: an effect system, a borrow calculus, and their interaction

**What this is.** The design that reorganises `experiments/Targets` into the two systems the user
asked for and the rules for their interaction. It is a plan for the builder; no Lean is written by
it. It replaces the architecture of `DESIGN.md` (§1.0–§1.5, §4.3, §9, §10's done-shape). The
semantic world of `DESIGN.md` §1.3–§1.4 and `FIX-RUN-END.md` is carried over as the proof device,
with its fields split in two: the borrow calculus's own world (`B.BWorld`), and the interaction's
extension of it (`I.SemWorld`), which adds what suspensions hold, the stop condition and the
continuation's share. It resolves verifier findings #2–#7 (`findings2-7.json`; `AGREE.md` majors
2–7) and the twenty findings of the review of this file's first version; §5.5 maps each of those to
its resolution. Every proved result of the library at `938d280` gets a home in §4.4, or is listed in
§4.5 with the reason it is restated.

**The framing (the user, 2026-10-05).**

> "We were to define the desired properties of _an effect system_ and tie it in to the core _in
> the interaction between effects and borrows_."
>
> "We have to design this as two systems, which may or may not overlap or be orthogonal. It might
> be possible to use BoLo primitives to produce effect system properties we want… but the primary
> thing is we need an effect system that satisfies the effect algebra and a borrow calculus that
> satisfies BoLo's guarantees and the rules for their interaction."
>
> "There might be a way to get some effect properties we want by leaning on borrow properties but
> it's not necessary."

**What the library's shape got wrong.** Its brief said to define every target "over Core's
existing syntax and semantics wherever they exist" (`DESIGN.md` l.18). So the effect system *was*
Core: a row was Core's `Row`, a handler Core's `hnd`, the typing parameter a family of Core
judgements, and every effect property a Core statement. Three consequences followed. Nothing could
be said of an effect system as such. Row variables existed only at the meta level, as families over
row environments (finding #3). And the end state mixed program-level guarantees with the proof
device's option-sensitive laws (finding #5). This design separates the two systems first, and lets
Core in only as one instance.

**Conventions.**

- **Worlds.** `[abstract]` is a statement about every instance of System A. `[prog]` mentions runs
  and a typing system, no semantic world. `[B]` is about a borrow world `M : B.BWorld`; `[I]` about
  `M : I.SemWorld`, which extends it. `[Core σ=[]]` is `coreB`/`coreW`/`tier1`. `[PAPER]`, `[SIB]`,
  `[GE]` as in the brief.
- **Status words** are `Status.lean`'s: PROVED, PROVED AT σ=[], PROVED AT A RESTRICTION (named),
  OPEN. **(checked)** marks a result proved in the library at `938d280`. **to build** marks Lean
  this design asks for.
- **Literature quotes** are verbatim from the texts read for this design (§Sources). Where a primary
  source could not be retrieved, the quote names the text it comes from.
- **Lean-shaped code** fixes every definition's content. Field order, universe levels and the
  encoding of paths as lists are the builder's.

---

## 0. The shape on one page

| part | module | contents | imports |
|---|---|---|---|
| **A** | `Targets/A/*` | an effect system, abstractly: the effect algebra with row variables (`EffAlg`), the structure `EffectSystem` over any calculus with effects, its requirements, the first-pass properties A₁, the binary laws A₂ and the erased lowering A₃ (stated), and A's non-vacuity lemmas | Mathlib only. No `Core`, no `Paper`, no BoLo |
| base | `Targets/Base/*` | Core's machine and typing as B and Instance read them, and nothing of A: `Rows.lean` (Core's rows: `RVar`, `Row.NU`, `RowClass`, `RowCon`, `RowCtx`, `RowEnv`, `RowCtx.Models`, `EffCtx`, `RowEq`, `Row.Has`, `ORow`, `Kont.fins`, `cancelOf`), `Typing.lean` (`TypingJ`, `tier1`, `CDerivesNU`, the `RC_*`, the open-row syntax `OVTy`/`OCTy`, `OurTyping` and its family reading `⟦·⟧`), `Machine.lean` (platforms, runs, `Final`, `SafeRuns`, `Terminates`, `SafeDrive`, `DivFree`, Core's `StopsIn`, `EffSafe`, `CancelRun`, `UnwindRun`, `CancelOrder`, `UnwindOrder`, `FinaliserOrder`, `NoInterception`) | `Core` |
| **B** | `Targets/B/*` | BoLo's guarantees over a typing system and a **borrow world** `BWorld` whose fields are the borrow calculus's only; each proved at BoLo by citing `Core`/`Paper`; the routes from B1–B2 to the program-level guarantees | `Core`, `Paper`, base |
| **Instance** | `Targets/Instance/*` | our calculus as one instance of A: `Rows.lean` (`orowAlg`, `closedRowAlg`, `RowForm`, `RowLink`, `orowRF`: A's algebra at our rows), `Typing.lean` (`J₁`, `J₂`), `Core.lean` (`ourInst`, the runner–platform correspondence, A's requirements at Core by computation), `Programs.lean` (the acceptance programs and their runs), `Laws.lean` (A₂ at the instance), `Lowering.lean` (A₃ at the backend, named-only) | A, `Core`, base. **Not B** |
| **I** | `Targets/I/*` | the interaction, the only place A and B meet: `World.lean` (`SemWorld extends BWorld`, the device's carrier, FIX-RUN-END), `Interface.lean`, `Device.lean`, `RunEnd.lean`, `Binder.lean`, `Answering.lean` (I4), `Routes.lean` (every route from B to an A property: effect safety and safety from FL, the extern routes, the borrow-derived routes of §4.3), `NonVacuity.lean`, `Combined.lean` | everything above |

**Imports.** A and base are independent. B imports base; Instance imports A and base. I imports
everything; `I/Combined.lean` is the top. A and B meet only in I: B mentions no `EffectSystem`, and
Instance mentions no borrow world or guarantee.

**The combined theorem** (§3.5), one definition for both tiers:

```lean
/-- **The combined theorem**: our calculus, at the typing system `J`, with semantic world `M`,
OQ-56's admissibility `Adm`, and the class `c` of rows a lend may span. -/
def Combined (J : OurTyping) (M : I.SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  A.Props₁ (ourInst J)          -- nothing breaks the effect algebra (System A, first pass)
  ∧ B.Guarantees J M.toBWorld   -- nothing breaks the borrow calculus (System B at the composite)
  ∧ I.Interface M               -- the interaction's option-neutral rules at the world
  ∧ I.Pins J Adm c              -- what the composite's typing must contain
```

**Done** is `Combined J₂ W Adm .any` at a named tier-2 typing system `J₂` and a named world `W`,
together with two audits of those definitions: `audit_W` (no step-indexing, decision 7; extended
for finding #6, §5.2) and `audit_J` (the row variables are the kernel's syntax, §5.2). **Tier 1** is
`Combined J₁ coreW admClosedOp .abortive` with `audit_J₁`. Tier 1 and tier 2 are the same
definition over two typing systems and two row classes; nothing is added to either.

**Where the old end state's conjuncts went.**

| `DESIGN.md` `Guarantees`/`EndStateAt` conjunct | new home |
|---|---|
| `RowAlgSafe RF`, `RowLink RF` | A: `RowAlgebra` and `RowSig` at the instance's own algebra; `RowLink` is an ingredient of the Instance's denotation lemma (§4.2) |
| `ExtendsNU J`, `OutExtends J.out`, `AdmExtends Adm`, `Tier2Pinned`, `AcceptsTier2`, `I4a` | I: `Pins` (in done; `Tier2Pinned` is `SpanRulesAt … .any`) |
| `Soundness J`, `SoundnessContracts J` | B: `Sound J M`, the externs' contracts its hypothesis, read at the world (finding #7); `SoundnessContractsAR` a corollary of done |
| `ReleasedOnceAll J` | **out of done**: a run lemma, a tautology about runs (finding #2); done holds B5 `ReleasedOnceEvery` |
| `EffSafe J` | A: `EffSafe` at the instance |
| `NoInterception J`, `FinaliserOrder J` | A: `Cancellation` (`NoIntercept`, `UnwindOrder`) at the instance; Core's syntactic `NoInterception` and run shapes are the instance's route |
| `WLaws M` | B: `WBoundB` (data, value shapes, eliminations, the nil slice's borrow structure); I: `WBoundI` (rows read through their protocol, the share's monotonicity, adequacy at stops from every index, the nil slice's stop and holdings); `Mono` to the device (finding #5) |
| `FL M J`, `Adequate M` | B1, B2 (in done) |
| `I1 M` | device; done holds `I1Prog` as a corollary |
| `I2 M J.out Adm c` | I: `Arises M` (in done); `StopVisible`, `ShareResume`, `FramesW`, `SpanBorrows` to the device (finding #5) |
| `I3 M` (`ShareCancel`) | device (finding #5); done holds A's `Cancellation` and B5 at the runs that cancel |
| `I5 M` | device (`I5beta`, `AntiFrameW`, `FrameW`); done holds A's deep resume (β operationally) |
| `LifetimeSound M J.out` | B7 (in done) |
| `Exclusive M` | B6 is `ExclusiveB` (every configuration the world reaches is valid); I's `Exclusive` (the typed invariant, with what suspensions hold counted) is in `Interface` |
| `P11 M` | device (`HandleCompat`, `RedLaws`); done holds A's `HandlerSem` and `HandlerRed` |
| `ConservativeWB M` | I: `EmbedsNil` (in done, at the nil index); the future-index form to the device (§4.5) |

---

## 1. System A: an effect system on its own

System A is judged on its own terms, with no borrows in sight. Its definitions mention no BoLo and
no Core. Our calculus is one instance (§4). **Every decided feature is a requirement of A**: §1.8
lists each with the requirement that carries it.

### 1.1 What the sources say an effect system is

| ingredient | source | statement shape (verbatim) |
|---|---|---|
| operations and signatures | Plotkin–Pretnar, LMCS 2013, Def. 4.2 | "A model M of the effect theory T is a set \|M\|, called the carrier of the model, together with an operation op_M : ⟦α⟧ × \|M\|^⟦β⟧ → \|M\| for each operation symbol op : α ↠ β" |
| rows as an effect algebra, with variables | Yoshioka–Sekiyama–Igarashi, arXiv 2404.16381, Fig. 1, Fig. 2, Def. 3.5 | "𝜀 ::= 𝜌 \| F 𝑺 (eﬀects)" (Fig. 1's grammar; the extracted text renders `::=` as `F`); K_Var "⊢Γ 𝛼 :K ∈ Γ ⟹ Γ ⊢ 𝛼 :K"; "⟨Eff(Σ), ⊙, 0⟩ is a partial monoid under ∼"; "Typelike substitution respecting well-formedness is a homomorphism for ⊙, (−)↑, and ∼" |
| generalisation and instantiation | Yoshioka et al. Fig. 5 | T_TAbs "Γ, 𝛼 : K ⊢ e : A \| 𝜀 ⟹ Γ ⊢ Λ𝛼 : K.e : ∀𝛼 : K.A𝜀 \| 0"; T_TApp "Γ ⊢ v : ∀𝛼 : K.A𝜀 \| 0, Γ ⊢ 𝑆 : K ⟹ Γ ⊢ v 𝑆 : A[𝑆/𝛼] \| 𝜀 [𝑆/𝛼]" |
| dirt: a computation's possible operations | Bauer–Pretnar, LMCS 10(4:9) 2014, §2 | "A dirty type A ! ∆ is just a pure type A tagged with a finite set ∆ of operations that might be called during evaluation" |
| annotations are operations | Kammar, *An Algebraic Theory of Type-and-Effect Systems* (2014), abstract (the thesis of Kammar–Plotkin POPL 2012) | "The key observation is that annotation effects can be identified with the effect operations." |
| handling is the induced homomorphism | Plotkin–Pretnar §1.1 | "h(M) … is the unique homomorphism (a map preserving operations) from A+exc to M that extends the map in1" |
| deep handlers | Yoshioka et al. §4.3; Tang et al. Fig. 7 (L-Op); Tang et al. Thm 3.4.3 | "the return type of a continuation variable k equals the type B of the handling expression as the effect handlers in λEA are deep"; "W = λ^Y y^B. handle E[(return y)^E] with H"; "Deep handlers are unlimited: if Δ; Γ ⊢ 𝐻 : 𝐶 ⇒ 𝐷, then Δ ⊢ Γ : •" |
| continuation linearity | Tang–Hillerström–Lindley–Morris, POPL 2024, Thm 3.6 | "For any closed, well-typed and linear safe computation M in F◦eff, if M ⤳^S_T N, then N is linear safe and ℒ(M) ∪ S = ℒ(N) ∪ T." |
| affine continuations and safety | van Rooij–Krebbers, Affect, POPL 2025, §3.2 | "safe e := ∀ e′ σ′. e / ∅ →∗ e′ / σ′ =⇒ e′ ∈ Val ∨ (∃ e″ σ″. e′ / σ′ → e″ / σ″)"; "one-shot continuations … should not be resumed more than once" |
| the platform | Ahman–Bauer, ESOP 2020, Def. 1 | "A runner R for a signature Σ is given by a carrier set \|R\| together with, for each op ∈ Σ, a co-operation op_R : A_op → (\|R\| ⇒ B_op × \|R\|)" |
| a generic function at two effects | Zhang–Myers, POPL 2019, Example 1 | "Let f be a variable with an effect-polymorphic type T = ∀α . (N → [N]α ) → [N]α"; its clients are "f [∅] (λx : N. x + x)" and "f [h.lbl] (g h)" |

A is therefore: a signature of operations with arities and control classes; rows over it forming an
effect algebra whose elements include row variables; types indexed by rows, with a row-`∀`; a
typing judgement at a row context, with generalisation and instantiation; handlers as models,
handling as the induced homomorphism, deep; continuations as values with a linear or affine use;
an operational semantics whose steps carry events; a platform that answers the operations left at
the top. **Cancellation and finalisation are ours**: SPEC §19 as built (decision 62). Ahman–Bauer's
Thm 7 ("A well-typed run factors through finalisation") and Voigt–Schuster–Brachthäuser's Thm 3.6
(preservation of `ActiveOpen`/`InactiveClosed`) are possible proof routes for them, not their shape.

### 1.2 The structure, field by field

```lean
namespace A

/-- Yoshioka–Sekiyama–Igarashi Def. 3.5's data.  A row variable is an effect (Fig. 1:
"𝜀 ::= 𝜌 | F 𝑺"), so a row that ends in a variable is an element of `Eff`. -/
structure EffAlg where
  Lab Eff Var : Type
  WF    : List Var → Eff → Prop          -- `Γ ⊢ ε : Eff`, `Γ` the row variables in scope
  WFLab : List Var → Lab → Prop
  comp  : Eff → Eff → Option Eff         -- `⊙`, partial
  unit  : Eff                            -- `0`
  lift  : Lab → Eff                      -- `(L)↑`
  eqv   : Eff → Eff → Prop               -- `∼`
  var   : Var → Eff                      -- the row variable `ρ`, as an effect
  subst : Var → Eff → Eff → Eff          -- `ε[S/α]`

-- `EffAlg.Laws` (Def. 3.5), `EffAlg.Safe` (Def. 5.1) and `EffAlg.Sub` (`ε₁ < ε₂`) move unchanged.

/-- The variables: well formed exactly in scope (K_Var), and substitution replaces exactly its own
variable. -/
structure EffAlg.VarLaws (EA : EffAlg) : Prop where
  wf_var      : ∀ Γ α, EA.WF Γ (EA.var α) ↔ α ∈ Γ
  subst_self  : ∀ α S, EA.subst α S (EA.var α) = S
  subst_other : ∀ α β S, α ≠ β → EA.subst α S (EA.var β) = EA.var β

/-- Never resumed; resumed exactly once; resumed or cancelled exactly once. -/
inductive OpClass | abortive | linear | affine

/-- `A ↠^c B` (Plotkin–Pretnar's `op : α ↠ β`).  Arities are value types: operations are
algebraic (higher-order operations: not now). -/
structure OpSig (Ty : Type) where
  arg : Ty
  ans : Ty
  cls : OpClass

/-- What a judgement types: a value at a value type, or a computation at a computation type. -/
inductive Jdg (Ty CTy : Type) | val (A : Ty) | comp (C : CTy)

/-- The events a step carries. -/
inductive Ev (Lab Val : Type)
  | tau                                    -- a silent step
  | catch (l : Lab) (i : ℕ)                -- a handler of `l` catches its operation `i`
  | fire (D : Val)                         -- a finaliser starts: an unwind or a cancel reached its frame
  | finEnd (r : Option (Lab × ℕ × Val))    -- a cancel's running finaliser ended: returned, or a raise escaped it
  | io (l : Lab) (i : ℕ) (v w : Val)       -- the platform answered `l.i` at `v` with `w` (runner steps only)

/-- **An effect system**: any calculus with effects, read as CBPV with an effect index. -/
structure EffectSystem where
  -- carriers
  EA : EffAlg
  RKind Ty CTy Term Val Hnd Kont Conf Ctx : Type
  -- value types
  UnitT    : Ty
  Tensor Sum : Ty → Ty → Ty
  U        : CTy → Ty                       -- a suspended computation
  Bang     : Ty → Ty                        -- `!A`: values used any number of times
  kTy      : OpClass → Ty → CTy → Ty        -- κ at an operation answering `B`, the handler answering `C`
  -- computation types
  F        : EA.Eff → Ty → CTy              -- `F_ε A`, Bauer–Pretnar's `A ! ε`
  Arr      : Ty → CTy → CTy                 -- `A ⊸ C`
  Loop     : EA.Eff → Ty → Ty → CTy         -- `Loop_ε A B = νX. F_ε(A ⊕ U X) & F_ε B`
  All      : EA.Var → RKind → CTy → CTy     -- `∀ρ:k. C`; Yoshioka's `∀α:K.A^ε` is `U (All α K (F ε A))`
  -- the one signature object, and which operations a row admits
  sig      : EA.Lab → List (OpSig Ty)
  has      : EA.Eff → EA.Lab → ℕ → Prop
  -- the predicates the properties read
  Drop Pers Data : Ty → Prop                -- may be weakened; may be contracted; first-order data
  DivFree  : CTy → Prop                     -- the answers whose programs the system claims terminate
  -- row substitution in types and contexts
  substTy  : EA.Var → EA.Eff → Ty → Ty
  substCTy : EA.Var → EA.Eff → CTy → CTy
  substC   : EA.Var → EA.Eff → Ctx → Ctx
  -- values
  unitV    : Val
  pair     : Val → Val → Val
  inl inr  : Val → Val
  var0     : Val                            -- the variable the innermost binder binds
  genV     : EA.Var → Val → Val             -- `Λρ. V` (T_TAbs, at a value)
  instV    : Val → EA.Eff → Val             -- `V ε` (T_TApp)
  -- computations
  val      : Val → Term                     -- a value, as the subject of a value judgement
  ret      : Val → Term                     -- `return V`
  seqT     : Term → Term → Term             -- `M; N`
  letv     : Val → Term → Term              -- `let x = V in M`, `x` the `var0` of `M`
  app      : Val → Val → Term               -- `V W`: apply a suspended function
  subst0   : Term → Val → Term              -- `M[V/var0]`, the binder removed
  next close : Val → Term                   -- a loop's two observations
  perform raise : EA.Lab → ℕ → Val → Term
  handle   : EA.Lab → Hnd → Term → Term
  retC     : Hnd → Val                      -- the return clause
  opC      : Hnd → ℕ → Val                  -- the clause of operation `i`
  capture  : EA.Lab → Hnd → Kont → Val      -- κ, handed to the clause of a caught operation
  resume   : Val → Val → Term
  cancel   : Val → Term
  cancelOf : EA.Lab → Hnd → Kont → Term     -- the start of κ's cancel run
  thenT    : Term → Term → Val → Term       -- `M then x. N unwind D`, `D` a suspended finaliser
  -- evaluation contexts
  hole     : Kont
  kcomp    : Kont → Kont → Kont             -- `kcomp K₁ K₂`: `K₂` plugged into `K₁`
  handleF  : EA.Lab → Hnd → Kont            -- `handle l H □`
  thenF    : Term → Val → Kont              -- `□ then x. N unwind D`
  plug     : Kont → Term → Term
  catches  : Kont → EA.Lab → Bool           -- a handler frame of `l` (Tang's `ℓ ∈ bl(E)`)
  unwindClear : Kont → Prop                 -- no frame but a handler frame stops a raise
  fins     : Kont → List Val                -- the finalisers of its finaliser frames, innermost first
  -- runs
  init     : Term → Conf
  term     : Conf → Term
  setT     : Conf → Term → Conf             -- the same store, another term
  step     : Conf → Ev EA.Lab Val → Conf → Prop
  -- typing
  admits   : List (EA.Var × RKind) → RKind → EA.Eff → Prop   -- `Θ ⊢ ε : k`
  emp      : Ctx
  ext      : Ctx → Ty → Ctx
  split    : Ctx → Ctx → Ctx → Prop
  der      : List (EA.Var × RKind) → Ctx → Term → Jdg Ty CTy → Prop

/-- **The platform**: a runner (Ahman–Bauer Def. 1) for the operations its effect admits. -/
structure Runner (S : EffectSystem) where
  eff : S.EA.Eff
  St  : Type
  s₀  : St
  co  : St → S.EA.Lab → ℕ → S.Val → Option (S.Val × St)
```

**Derived, in `Targets/A/System.lean`**, one line each (`S.Ev` is `Ev S.EA.Lab S.Val`):

```lean
def one (A) : S.Ctx := S.ext S.emp A
def substJ (α ε) : Jdg S.Ty S.CTy → Jdg S.Ty S.CTy        -- `.val A ↦ .val (substTy α ε A)`, `.comp C ↦ .comp (substCTy α ε C)`
def WFRow (Θ) (ε) : Prop := S.EA.WF (Θ.map Prod.fst) ε
def IsVal (c : S.Conf) : Prop := ∃ v, S.term c = S.ret v
def PureStep (c ev c') : Prop := S.step c ev c' ∧ c' = S.setT c (S.term c')     -- the store unchanged
def PureSteps : S.Conf → S.Conf → Prop := ReflTransGen (fun c c' => ∃ ev, S.PureStep c ev c')
def Reach : S.Conf → S.Conf → Prop := ReflTransGen (fun c c' => ∃ ev, S.step c ev c')
-- runs under a runner: configurations carry the runner's state
abbrev RConf (R : S.Runner) := S.Conf × R.St
def rinit (R) (e) : S.RConf R := (S.init e, R.s₀)
def setR (c : S.RConf R) (t) : S.RConf R := (S.setT c.1 t, c.2)
inductive RStep (R) : S.RConf R → S.Ev → S.RConf R → Prop
  | mach {c ev c' s} : S.step c ev c' → RStep (c, s) ev (c', s)
  | io {c s s' K l i v w} : S.term c = S.plug K (S.perform l i v) → S.catches K l = false →
      S.has R.eff l i → R.co s l i v = some (w, s') →
      RStep (c, s) (.io l i v w) (S.setT c (S.plug K (S.ret w)), s')
inductive RPath (R) : S.RConf R → List (S.Ev × S.RConf R) → Prop     -- a run, step by step
  | nil {c} : RPath c []
  | cons {c ev c' q} : S.RStep R c ev c' → RPath c' q → RPath c ((ev, c') :: q)
-- `q.cfg c j`: the `j`-th configuration of the path `q` from `c` (`q.cfg c 0 = c`); `q.ev j`: the
-- event of its `j`-th step; `q.seg j j'`: its steps from the `j`-th configuration to the `j'`-th;
-- `q.ios`: its `io` events in order.  `PurePath R c q c'`: an `RPath` from `c` to `c'` each of whose
-- steps is an `RStep.mach` of a `PureStep`.  `MPath c q`: a path of `S.step` (no runner);
-- `MComplete c q`: an `MPath` ending at a value.
def RReach (R) (c c' : S.RConf R) : Prop := ∃ q, S.RPath R c q ∧ q.cfg c q.length = c'
def CompleteFrom (R) (c) (q) : Prop := S.RPath R c q ∧ S.IsVal (q.cfg c q.length).1
def Obs (R) (e) (tr) (v) : Prop :=                                              -- io trace and answer
  ∃ q, S.CompleteFrom R (S.rinit R e) q ∧ tr = q.ios ∧ S.term (q.cfg _ q.length).1 = S.ret v
def Answers (R) (ε) : Prop := ∀ l i, S.has ε l i → S.has R.eff l i               -- the runner answers ε
def R₀ : S.Runner := ⟨S.EA.unit, Unit, (), fun _ _ _ _ => none⟩                 -- the platform with no operation
def Runner.Respects (R) : Prop :=                                                -- `Platform.Respects`, abstracted
  ∀ l i o, S.has R.eff l i → (S.sig l)[i]? = some o → o.cls = .linear ∧ S.Data o.arg ∧ S.Data o.ans ∧
    ∀ s v, S.der [] S.emp (S.val v) (.val o.arg) →
      ∃ w s', R.co s l i v = some (w, s') ∧ S.der [] S.emp (S.val w) (.val o.ans)
def SafeRuns (R) (e) : Prop := ∀ c, S.RReach R (S.rinit R e) c → S.IsVal c.1 ∨ ∃ ev c', S.RStep R c ev c'
def Terminates (R) (e) : Prop := (∀ c, S.RReach R (S.rinit R e) c → ∃ c', S.RReach R c c' ∧ S.IsVal c'.1) ∧
  ¬ ∃ f : ℕ → S.RConf R, f 0 = S.rinit R e ∧ ∀ n, ∃ ev, S.RStep R (f n) ev (f (n + 1))
-- the drive (SPEC §11, §14): the runtime drives a program that returns a loop, and never closes it
inductive Phase | main | drive
inductive DStep (R) : S.RConf R × Phase → S.Ev → S.RConf R × Phase → Prop
  | run {c ev c' ph} : S.RStep R c ev c' → DStep (c, ph) ev (c', ph)
  | start {c l} : S.term c.1 = S.ret l → DStep (c, .main) .tau (S.setR c (S.next l), .drive)
  | again {c l} : S.term c.1 = S.ret (S.inr l) → DStep (c, .drive) .tau (S.setR c (S.next l), .drive)
-- `DPath`, `DReach` as `RPath`, `RReach`
def FinalDrive (d : S.RConf R × Phase) : Prop := d.2 = .drive ∧ ∃ a, S.term d.1.1 = S.ret (S.inl a)
def SafeDrive (R) (e) : Prop := ∀ d, S.DReach R (S.rinit R e, .main) d → S.FinalDrive d ∨ ∃ ev d', S.DStep R d ev d'
-- the shapes the requirements read
def AtCatch (c : S.Conf) (K₀ l H K i v) : Prop :=
  S.term c = S.plug K₀ (S.handle l H (S.plug K (S.perform l i v))) ∧ S.catches K l = false
def AtResume (c : S.Conf) (l H K) : Prop := ∃ K₁ w, S.term c = S.plug K₁ (S.resume (S.capture l H K) w)
def AtCancel (c : S.Conf) (K₁ l H K) : Prop := S.term c = S.plug K₁ (S.cancel (S.capture l H K))
def clauseArg (o : OpSig S.Ty) (ε R) : S.Ty :=
  if o.cls = .abortive then o.arg else S.Tensor o.arg (S.kTy o.cls o.ans (S.F ε R))
```

**The fields, and what each is for.**

| field(s) | what it is | the literature's object |
|---|---|---|
| `EA` | the rows: labels, effects (row variables among them, `var`), `⊙`, `0`, `(−)↑`, `∼`, substitution | Yoshioka Fig. 1 and Def. 3.5 (an `EffAlg`, moved Core-free, with `var` added) |
| `sig`, `has` | each label's operations, numbered, with arity and class; which operations a row admits | Plotkin–Pretnar's signature; Yoshioka's proper effect context (Def. 5.3); Bauer–Pretnar's dirt `∆` |
| `OpClass` | abortive, linear, affine | Koka's `final ctl`/`ctl`; Tang et al.'s control-flow linearity; Affect's one-shot |
| `UnitT`, `Tensor`, `Sum`, `U`, `Bang`, `kTy`, `F`, `Arr`, `Loop`, `All` | the type formers the effect properties read | CBPV with an effect index (Plotkin–Pretnar's `F`, Bauer–Pretnar's `A ! ∆`); `!` of linear logic; Yoshioka's `∀α:K.A^ε` |
| `kTy` | the continuation's type per class: a linear κ is resumed, an affine κ resumed or cancelled | Tang Thm 3.4; SPEC §19's `K_i` |
| `Drop`, `Pers` | the structural predicates: what may be weakened, what may be contracted | Tang's `•` kind |
| `Data`, `DivFree` | observable answers; the answers claimed to terminate | divergence as an effect (decision 35) |
| `substTy`, `substCTy`, `substC` | row substitution in types and contexts | Yoshioka Def. 1.10 (typelike substitution) |
| `genV`, `instV` | row abstraction and instantiation at values | Yoshioka T_TAbs, T_TApp |
| `val`, `ret`, `seqT`, `letv`, `app`, `var0`, `subst0`, `unitV`, `pair`, `inl`, `inr` | the CBPV skeleton the requirements are stated with | Levy's CBPV; Plotkin–Pretnar's `M to x. N` |
| `next`, `close` | a loop's observations | SPEC §7: "`next` finishes with `A` or goes on; `close` ends it early with the residual `B`" |
| `perform`, `raise`, `handle`, `retC`, `opC` | the effect formers; a handler is a return clause and a clause per operation | Plotkin–Pretnar `op_V(x.M)`, `M handled with H`; Bauer–Pretnar `ι#op e (x. c′)` |
| `capture`, `resume`, `cancel`, `cancelOf` | the continuation value and its two eliminations | System C `cap`; Affect `cont ℓ N`; SPEC §19's `kappa` |
| `thenT`, `thenF`, `fins` | finaliser frames | Voigt et al.'s finaliser frames; Ahman–Bauer's `finally F` |
| `Kont`, `hole`, `kcomp`, `handleF`, `plug`, `catches`, `unwindClear` | evaluation contexts, their handler frames | Tang's `E` and `bl(E)`; Yoshioka's `E` and `n−free(L, E)` |
| `Conf`, `init`, `term`, `setT`, `step` | a labelled small-step semantics | the operation-event semantics |
| `RKind`, `admits`, `Ctx`, `emp`, `ext`, `split`, `der` | the typing judgement at a row context | Yoshioka's `Γ ⊢ e : A \| ε` with typelike variables, `Γ ⊢ S : K` |
| `Runner` | the platform | Ahman–Bauer Def. 1 |

**What A leaves to the instance.** The instance's own value types, terms and rules (for us: BoLo's
references, borrows and borrow constants, and Core's typing rules for application, pairs and
sums) are the instance's. A pins the effect formers, the effect rules, the effect semantics, the
structural rules as far as continuations need them, and the CBPV skeleton it states them with. The
acceptance witnesses (A-ACC) are existential, so the instance's own rules must type them.

### 1.3 Requirements on an admissible instance

Each is a `def … : Prop` over `S : EffectSystem`. `Admissible S` is their conjunction.

**A-MACH: the machine's shape.**

```lean
/-- Configurations: a term and the rest (the store), read and replaced. -/
def ConfLaws (S) : Prop :=
  (∀ e, S.term (S.init e) = e) ∧ (∀ c t, S.term (S.setT c t) = t) ∧
  (∀ c, S.setT c (S.term c) = c) ∧ (∀ c t t', S.setT (S.setT c t) t' = S.setT c t')

/-- Evaluation contexts.  Plugging composes and is injective in the hole.  A handler frame catches
its own label only, so forwarding is structural: an operation of another label passes it.  A
finaliser frame stops every raise and holds its finaliser. -/
def KontLaws (S) : Prop :=
  (∀ t, S.plug S.hole t = t) ∧ (∀ K₁ K₂ t, S.plug (S.kcomp K₁ K₂) t = S.plug K₁ (S.plug K₂ t)) ∧
  (∀ K t t', S.plug K t = S.plug K t' → t = t') ∧
  (∀ l H t, S.plug (S.handleF l H) t = S.handle l H t) ∧ (∀ M N D, S.plug (S.thenF N D) M = S.thenT M N D) ∧
  (∀ m, S.catches S.hole m = false) ∧ (∀ l H m, S.catches (S.handleF l H) m = decide (m = l)) ∧
  (∀ N D m, S.catches (S.thenF N D) m = false) ∧
  (∀ K₁ K₂ m, S.catches (S.kcomp K₁ K₂) m = (S.catches K₁ m || S.catches K₂ m)) ∧
  S.unwindClear S.hole ∧ (∀ l H, S.unwindClear (S.handleF l H)) ∧ (∀ N D, ¬ S.unwindClear (S.thenF N D)) ∧
  (∀ K₁ K₂, S.unwindClear (S.kcomp K₁ K₂) ↔ S.unwindClear K₁ ∧ S.unwindClear K₂) ∧
  (∀ K, S.unwindClear K → S.fins K = []) ∧
  S.fins S.hole = [] ∧ (∀ l H, S.fins (S.handleF l H) = []) ∧ (∀ N D, S.fins (S.thenF N D) = [D]) ∧
  (∀ K₁ K₂, S.fins (S.kcomp K₁ K₂) = S.fins K₂ ++ S.fins K₁)

/-- A step of a term is its step in every context (Yoshioka E_Eval: "e1 ↦ e2 ⟹ E[e1] −→ E[e2]"). -/
def Congr (S) : Prop :=
  ∀ c t ev c' K, S.step (S.setT c t) ev c' →
    S.step (S.setT c (S.plug K t)) ev (S.setT c' (S.plug K (S.term c')))

/-- The machine never answers an operation: `io` events are the runner's (`RStep.io`) only. -/
def NoIO (S) : Prop := ∀ c l i v w c', ¬ S.step c (.io l i v w) c'

def MachShape (S) : Prop := ConfLaws S ∧ KontLaws S ∧ Congr S ∧ NoIO S
```

`Congr` and `KontLaws` make every handler step below hold in every outer context, and they are what
the finaliser traces of A-CAN read: "a step of the inner term alone".

**A-ROWS (T0): the rows form a safe effect algebra with variables, over one signature object.**

```lean
/-- Yoshioka Def. 3.5 (laws), Def. 5.1 (safety), and the variables (K_Var, substitution). -/
def RowAlgebra (S) : Prop := S.EA.Laws ∧ S.EA.Safe ∧ S.EA.VarLaws

/-- **One signature object**: `(l)↑` admits exactly `l`'s operations (it is the signature `sig l`
denotes); `⊙` unions what its arguments admit; `0` admits nothing, and neither does a variable
before it is instantiated; `∼` preserves what is admitted; substitution adds the substituted row's
operations and nothing else; no signature is empty. -/
def RowSig (S) : Prop :=
  (∀ l m i, S.has (S.EA.lift l) m i ↔ m = l ∧ i < (S.sig l).length) ∧
  (∀ l i, ¬ S.has S.EA.unit l i) ∧ (∀ α l i, ¬ S.has (S.EA.var α) l i) ∧
  (∀ ε₁ ε₂ ε l i, S.EA.comp ε₁ ε₂ = some ε → (S.has ε l i ↔ S.has ε₁ l i ∨ S.has ε₂ l i)) ∧
  (∀ ε₁ ε₂ l i, S.EA.eqv ε₁ ε₂ → (S.has ε₁ l i ↔ S.has ε₂ l i)) ∧
  (∀ α ε' ε l i, S.has ε l i → S.has (S.EA.subst α ε' ε) l i) ∧
  (∀ α ε' ε l i, S.has (S.EA.subst α ε' ε) l i → S.has ε l i ∨ S.has ε' l i) ∧
  (∀ l, S.sig l ≠ [])
```

Def. 5.1: "(1) For any L, (L)↑ < 0 does not hold. (2) If (L)↑ < ε and (L′)↑ ⊙ ε′ ∼ ε and L ≠ L′,
then (L)↑ < ε′." Condition (1) "disallows the subeffecting to hide an invoked effect label"; (2)
means a handler of `L′` never erases `L`. Condition (1) follows from `RowSig` (`c1_of_rowSig`, to
build). Condition (2) speaks of `<`, a statement about `⊙` and `∼` that `has` cannot rebuild, so
`RowAlgebra` keeps both as stated. Its per-operation reading also follows from `RowSig`'s `⊙` and `∼`
clauses: a handler of `L′` leaves every operation of `L ≠ L′` in the row (`handled_has_of_rowSig`,
to build). Def. 7.1 (masking) and Def. 7.6 (type-argument dispatch) apply only if an instance adds
masking or erases effect type arguments.

**Why `has`, and not "every row is a `⊙` of lifts".** Rows are sums of signatures: `(l)↑` is a
whole signature and `⊙` is union, and that is what `RowSig` requires. A does not require every
well-formed row to be `∼` to a `⊙` of lifts and a variable, because SPEC §19's finaliser row
`Σ^abort` "keeps `Σ`'s abortive operations": it is part of a signature, and cancellation as built is
decided (decision 62). So operations enter a row through `has`, and `StopsIn`, `[perform]`,
`[raise]` and `Answers` read `has`, never `Sub (lift l) ε`.

**A-ROW: row variables are in the kernel (decision 62).**

```lean
/-- Row substitution commutes with every type former A has, avoids capture at `All`, and leaves
signatures alone: operations are not row-polymorphic (monomorphic signatures, as Kammar–Pretnar,
which need no value restriction). -/
def TySubst (S) : Prop :=
  (∀ α ε ε' A, S.substCTy α ε (S.F ε' A) = S.F (S.EA.subst α ε ε') (S.substTy α ε A)) ∧
  (∀ α ε A C, S.substCTy α ε (S.Arr A C) = S.Arr (S.substTy α ε A) (S.substCTy α ε C)) ∧
  (∀ α ε ε' A B, S.substCTy α ε (S.Loop ε' A B) =
     S.Loop (S.EA.subst α ε ε') (S.substTy α ε A) (S.substTy α ε B)) ∧
  (∀ α ε k C, S.substCTy α ε (S.All α k C) = S.All α k C) ∧
  (∀ α β ε k C Γ, α ≠ β → β ∉ Γ → S.EA.WF Γ ε →
     S.substCTy α ε (S.All β k C) = S.All β k (S.substCTy α ε C)) ∧
  (∀ α ε C, S.substTy α ε (S.U C) = S.U (S.substCTy α ε C)) ∧
  (∀ α ε A, S.substTy α ε (S.Bang A) = S.Bang (S.substTy α ε A)) ∧
  (∀ α ε A B, S.substTy α ε (S.Tensor A B) = S.Tensor (S.substTy α ε A) (S.substTy α ε B)) ∧
  (∀ α ε A B, S.substTy α ε (S.Sum A B) = S.Sum (S.substTy α ε A) (S.substTy α ε B)) ∧
  (∀ α ε, S.substTy α ε S.UnitT = S.UnitT) ∧
  (∀ α ε c B C, S.substTy α ε (S.kTy c B C) = S.kTy c (S.substTy α ε B) (S.substCTy α ε C)) ∧
  (∀ α ε, S.substC α ε S.emp = S.emp) ∧
  (∀ α ε Γ A, S.substC α ε (S.ext Γ A) = S.ext (S.substC α ε Γ) (S.substTy α ε A)) ∧
  (∀ α ε l o, o ∈ S.sig l → S.substTy α ε o.arg = o.arg ∧ S.substTy α ε o.ans = o.ans)

/-- **One generic function, bound once, used at two rows** (Zhang–Myers Example 1, whose `f` "with
an effect-polymorphic type T = ∀α . (N → [N]α ) → [N]α" is used at "[∅]" and at "[h.lbl]").  `f`
is typed once, at a row variable.  The closed program binds it once and calls it at `ρ := 0` with
`g₀`, then at `ρ := (l)↑` with `g₁`, under a handler of `l`.  The program is typed at the pure
row, and its complete run under the platform with no operation catches an operation of `l`. -/
def AccRowPoly (S) : Prop :=
  ∃ (ρ : S.EA.Var) (k : S.RKind) (A B R : S.Ty) (vf g₀ g₁ : S.Val) (l : S.EA.Lab) (H : S.Hnd) (i : ℕ) q,
    let Cf := S.Arr (S.U (S.Arr A (S.F (S.EA.var ρ) B))) (S.F (S.EA.var ρ) S.UnitT)
    let use := fun ε g => S.app (S.instV S.var0 ε) g
    let body := S.seqT (use S.EA.unit g₀) (S.handle l H (use (S.EA.lift l) g₁))
    S.Data R ∧ S.admits [] k S.EA.unit ∧ S.admits [] k (S.EA.lift l) ∧
    S.der [] S.emp (S.val vf) (.val (S.Bang (S.U (S.All ρ k Cf)))) ∧
    S.der [] (S.one (S.Bang (S.U (S.All ρ k Cf)))) body (.comp (S.F S.EA.unit R)) ∧
    S.der [] S.emp (S.letv vf body) (.comp (S.F S.EA.unit R)) ∧
    S.CompleteFrom S.R₀ (S.rinit S.R₀ (S.letv vf body)) q ∧ Ev.catch l i ∈ q.map Prod.fst

/-- **Row variables in the kernel**: generalisation and instantiation, substitution, and the
generic function above. -/
def RowPoly (S) : Prop :=
  -- generalisation (T_TAbs, at a value: the value restriction, as Affect's)
  (∀ Θ Γ α k v C, α ∉ Θ.map Prod.fst → (∀ ε, S.substC α ε Γ = Γ) →
     S.der ((α, k) :: Θ) Γ (S.val v) (.val (S.U C)) →
     S.der Θ Γ (S.val (S.genV α v)) (.val (S.U (S.All α k C)))) ∧
  -- instantiation (T_TApp)
  (∀ Θ Γ α k v C ε, S.der Θ Γ (S.val v) (.val (S.U (S.All α k C))) → S.admits Θ k ε → S.WFRow Θ ε →
     S.der Θ Γ (S.val (S.instV v ε)) (.val (S.U (S.substCTy α ε C)))) ∧
  -- substitution: a judgement at a row variable holds at every admissible row put for it
  (∀ Θ α k Γ e j ε, S.der ((α, k) :: Θ) Γ e j → S.admits Θ k ε → S.WFRow Θ ε →
     S.der Θ (S.substC α ε Γ) e (S.substJ α ε j)) ∧
  S.AccRowPoly
```

**What this requires, and what it leaves open.** Row variables are elements of the algebra
(`var`, `VarLaws`), types carry them (`F (var ρ) B`, through `TySubst`, which ties every former to
`EA.subst`), there is a binder for them (`All`) with Yoshioka's two rules, and one program must bind
a generic value once and use it at two rows. That program is the decisive requirement. A typing
system with closed rows only gives the let-bound `f` one type. Its first use is outside every
handler of `l` in a program at row `0`, so that type's row admits nothing. Its second use passes a
callback that performs `l`. So no closed type serves both, and the closed-instance reading fails A
(§6.2). A requires nothing of a generic value passed as an argument, stored or returned: that is
rank-n polymorphism, which is OQ-13's remaining question (§7 Q2). **The floor A requires is rank 1:
a generic value bound by `let` and used at several rows.** `audit_J` (§5.2) is then a check on how
the named kernel represents this, not the place the requirement lives.

**A-RULES: the typing is closed under the effect rules, stated with the algebra.**

```lean
/-- A handler of `l` for a computation of `A`, answering `R` at row `ε` (Yoshioka H_Return, H_Op;
SPEC §19 `[handle]`, "Γ₁ ⊢ H : !U(A ⊸ F_Σ R) ⊗ ⊗_i !U(A_i ⊗ K_i ⊸ F_Σ R)").  The clauses are
`!`-thunks: a deep handler's clauses are unlimited (Tang Thm 3.4.3).  κ answers the handling's own
type: deep. -/
def HndTyped (S) (Θ Γ) (l : S.EA.Lab) (H : S.Hnd) (A : S.Ty) (ε : S.EA.Eff) (R : S.Ty) : Prop :=
  S.der Θ Γ (S.val (S.retC H)) (.val (S.Bang (S.U (S.Arr A (S.F ε R))))) ∧
  ∀ i o, (S.sig l)[i]? = some o →
    S.der Θ Γ (S.val (S.opC H i)) (.val (S.Bang (S.U (S.Arr (S.clauseArg o ε R) (S.F ε R)))))

/-- `[then]` (SPEC §19): `M then x. N unwind D`.  `D` runs in `N`'s context, additively, and
performs only abortive operations of the row (SPEC's `F_{Σ^abort} 1`). -/
def ThenRule (S) : Prop :=
  ∀ Θ Γ Γ₁ Γ₂ M N D ε εD A B, S.split Γ Γ₁ Γ₂ →
    S.der Θ Γ₁ M (.comp (S.F ε A)) → S.der Θ (S.ext Γ₂ A) N (.comp (S.F ε B)) →
    S.der Θ Γ₂ (S.val D) (.val (S.U (S.Arr S.UnitT (S.F εD S.UnitT)))) →
    (∀ l i, S.has εD l i → S.has ε l i ∧ ∃ o, (S.sig l)[i]? = some o ∧ o.cls = .abortive) →
    S.der Θ Γ (S.thenT M N D) (.comp (S.F ε B))

def EffRules (S) : Prop :=
  -- [sub] (Yoshioka T_Sub/ST_Comp: "Γ ⊢ ε₁ < ε₂ ≝ ∃ε. ε₁ ⊙ ε ∼ ε₂")
  (∀ Θ Γ e ε₁ ε₂ A, S.der Θ Γ e (.comp (S.F ε₁ A)) → S.EA.Sub ε₁ ε₂ → S.der Θ Γ e (.comp (S.F ε₂ A))) ∧
  -- [perform] (T_Op): a resuming operation the row admits
  (∀ Θ Γ v l i o ε, (S.sig l)[i]? = some o → o.cls ≠ .abortive → S.has ε l i →
     S.der Θ Γ (S.val v) (.val o.arg) → S.der Θ Γ (S.perform l i v) (.comp (S.F ε o.ans))) ∧
  -- [raise]: an abortive operation the row admits, at any answer
  (∀ Θ Γ v l i o ε B, (S.sig l)[i]? = some o → o.cls = .abortive → S.has ε l i →
     S.der Θ Γ (S.val v) (.val o.arg) → S.der Θ Γ (S.raise l i v) (.comp (S.F ε B))) ∧
  -- [handle] (T_Handling: "(l 𝑺)↑ ⊙ 𝜀 ∼ 𝜀′"): the handled row is `(l)↑ ⊙ ε`
  (∀ Θ Γ Γ₁ Γ₂ l H e ε ε' ε'' A R, S.split Γ Γ₁ Γ₂ →
     S.EA.comp (S.EA.lift l) ε = some ε'' → S.EA.eqv ε'' ε' →
     S.der Θ Γ₂ e (.comp (S.F ε' A)) → S.HndTyped Θ Γ₁ l H A ε R →
     S.der Θ Γ (S.handle l H e) (.comp (S.F ε R))) ∧
  S.ThenRule
```

**A-SEM: handling is the induced homomorphism, deep (Plotkin–Pretnar; decision 62).** Every
conjunct holds in an arbitrary outer context `K₀`.

```lean
def HandlerSem (S) : Prop :=
  -- return: "return V handled with … to x : A. N(x) = N(V)"
  (∀ c K₀ l H v, S.term c = S.plug K₀ (S.handle l H (S.ret v)) →
     S.step c .tau (S.setT c (S.plug K₀ (S.app (S.retC H) v)))) ∧
  -- a resuming operation, deep (Tang L-Op; Yoshioka R_Handle2): the clause gets the argument and κ
  (∀ c K₀ l H K i v o, S.AtCatch c K₀ l H K i v → (S.sig l)[i]? = some o → o.cls ≠ .abortive →
     S.step c (.catch l i) (S.setT c (S.plug K₀ (S.app (S.opC H i) (S.pair v (S.capture l H K)))))) ∧
  -- an abortive operation: "raise_e′ () handled with … = N_e′"; the clause gets the argument only
  (∀ c K₀ l H K i v o, S.term c = S.plug K₀ (S.handle l H (S.plug K (S.raise l i v))) →
     S.catches K l = false → S.unwindClear K → (S.sig l)[i]? = some o → o.cls = .abortive →
     S.step c (.catch l i) (S.setT c (S.plug K₀ (S.app (S.opC H i) v)))) ∧
  -- deep resume: resuming κ at w runs the frozen context at w under the same handler
  (∀ c K₀ l H K w, S.term c = S.plug K₀ (S.resume (S.capture l H K) w) →
     S.PureSteps c (S.setT c (S.plug K₀ (S.handle l H (S.plug K (S.ret w)))))) ∧
  -- cancel: cancelling κ starts κ's cancel run, in the canceller's context
  (∀ c K₀ l H K, S.term c = S.plug K₀ (S.cancel (S.capture l H K)) →
     S.PureSteps c (S.setT c (S.plug K₀ (S.cancelOf l H K)))) ∧
  -- finalise: a raise that reaches a finaliser frame fires its finaliser (SPEC [finalise])
  (∀ c K₀ M N D K m j w, S.term c = S.plug K₀ (S.thenT (S.plug K (S.raise m j w)) N D) →
     S.catches K m = false → S.unwindClear K → ∃ c', S.step c (.fire D) c')
```

**Forwarding** is structural: `KontLaws` says a handler frame of `l` catches `l` only
(`catches (handleF l H) m = decide (m = l)`), so an operation of `m ≠ l` passes it. It is caught by
the next frame out that catches `m`, with a continuation whose context contains `handleF l H`.
`DeepResume` reinstalls the inner handler when that continuation is resumed. The fourth conjunct is
I5's β read operationally, and is what "deep" means: the continuation re-installs the handler
(Plotkin–Pretnar's homomorphism applied under κ). With no equations in signatures (OQ-22), every
interpretation is a model of the free theory, so Plotkin–Pretnar's correctness condition (Def. 4.5:
"the set U⟦C⟧ together with the op_H(c) forms a model of T") holds of every handler, and handler
correctness is these equations.

**A-LIN: continuations are linear or affine; discard is an explicit cancel; no forget.**

```lean
/-- **The structural rules, tied to the typing**, at the places where nothing can absorb a context.
`Drop` is exactly what may be dropped before the unit value, and `Pers` exactly what may be paired
with itself.  In every context, the unit value and its return are typed only if the variable bound
last may be dropped, and the self-pair only if it may be contracted. -/
def Structural (S) : Prop :=
  (∀ Θ A, S.der Θ (S.one A) (S.val S.unitV) (.val S.UnitT) ↔ S.Drop A) ∧
  (∀ Θ A, S.der Θ (S.one A) (S.val (S.pair S.var0 S.var0)) (.val (S.Tensor A A)) ↔ S.Pers A) ∧
  (∀ Θ Γ A, S.der Θ (S.ext Γ A) (S.val S.unitV) (.val S.UnitT) → S.Drop A) ∧
  (∀ Θ Γ A ε, S.der Θ (S.ext Γ A) (S.ret S.unitV) (.comp (S.F ε S.UnitT)) → S.Drop A) ∧
  (∀ Θ Γ A, S.der Θ (S.ext Γ A) (S.val (S.pair S.var0 S.var0)) (.val (S.Tensor A A)) → S.Pers A)

/-- The eliminations of a κ bound last: resume it, or cancel it. -/
def Elims (S) (w : S.Val) : List S.Term := [S.resume S.var0 w, S.cancel S.var0]

def ContDiscipline (S) : Prop :=
  Structural S ∧
  -- `!` is unlimited, and is used as what it holds (dereliction)
  (∀ A, S.Drop (S.Bang A) ∧ S.Pers (S.Bang A)) ∧
  (∀ Θ Γ v A, S.der Θ Γ (S.val v) (.val (S.Bang A)) → S.der Θ Γ (S.val v) (.val A)) ∧
  -- `()` is unlimited; a pair is dropped or contracted only with both halves
  S.Drop S.UnitT ∧ S.Pers S.UnitT ∧
  (∀ A B, S.Drop (S.Tensor A B) ↔ S.Drop A ∧ S.Drop B) ∧ (∀ A B, S.Pers (S.Tensor A B) ↔ S.Pers A ∧ S.Pers B) ∧
  -- a linear or affine κ is neither forgotten nor copied
  (∀ c B C, c ≠ .abortive → ¬ S.Drop (S.kTy c B C) ∧ ¬ S.Pers (S.kTy c B C)) ∧
  -- … and is not eliminated twice in sequence
  (∀ Θ Γ c B ε w₁ w₂ E₁ E₂, c ≠ .abortive → E₁ ∈ S.Elims w₁ → E₂ ∈ S.Elims w₂ →
     ¬ S.der Θ (S.ext Γ (S.kTy c B (S.F ε S.UnitT))) (S.seqT E₁ E₂) (.comp (S.F ε S.UnitT))) ∧
  -- it is resumed at its answer type
  (∀ Θ Γ Γ₁ Γ₂ κ w c B C, c ≠ .abortive → S.split Γ Γ₁ Γ₂ →
     S.der Θ Γ₁ (S.val κ) (.val (S.kTy c B C)) → S.der Θ Γ₂ (S.val w) (.val B) →
     S.der Θ Γ (S.resume κ w) (.comp C)) ∧
  -- an affine κ may be cancelled, at its handler's row (SPEC §19's `U((B ⊸ F_Σ R) & F_Σ 1)`)
  (∀ Θ Γ κ B ε R, S.der Θ Γ (S.val κ) (.val (S.kTy .affine B (S.F ε R))) →
     S.der Θ Γ (S.cancel κ) (.comp (S.F ε S.UnitT))) ∧
  -- a linear κ has no cancel that can run (SPEC §19's linear `K_i` is `U((B ⊸ F_Σ R) & ⊤)`)
  (∀ Θ Γ B C ε A, ¬ S.der Θ (S.ext Γ (S.kTy .linear B C)) (S.cancel S.var0) (.comp (S.F ε A)))
```

`Structural` bounds the typing from both sides, so `¬ Drop (kTy …)` and `¬ Pers (kTy …)` have
content. A typing with a general weakening rule, or weakening at thunk types (the `AGREE.md` minor
finding), types the unit value with a κ in context, so it fails. A typing with a general contraction
rule types the self-pair of a κ, so it fails. The last κ conjunct excludes resuming or cancelling one
κ twice in sequence. The old no-discard conjunct is `Structural`'s fourth clause at a κ.

**Why at those places, and not at every term that ignores a variable.** A linear typing's
`⊤`-introduction and `0`-elimination absorb any context. In Core, `topI` types `⟨⟩ : ⊤` at any
context, and `zeroE` types `absurd V` "at any rest of the context". So `λz. absurd z : U(0 ⊸ C)` is
typed in a context holding a κ and ignores it. This is sound, since neither a `⊤` computation nor a
`0`-elimination ever runs. But it means "every term typed with a live κ uses it" is false of Core,
and a requirement in that form would make Core fail A. (The derivation is a check to build,
`absurd_absorbs`, from `lam`, `zeroE` and `Ctx.SplitP.right`.) The unit value, its return and the
self-pair are typed by no absorbing rule. At them, Core weakens only at persistent slots
(`Ctx.DeadP.drop`, `Ctx.SoloP.skip`), contracts only there (`Ctx.SplitP.dup`), and a κ type is a
thunk, which is not persistent. So at our instance the proofs are inversions of `unitI` and of
`tensorI` with `var`. That a κ is used on every run that completes is a run-level count; it is P8.b
(§1.5) and OQ-50's question, outside the first pass. A forgotten κ that holds a resource is also a
leak, which B4 excludes.

The linear κ's cancel is excluded at every returner type. A linear κ's cancel branch is at `⊤`, so
`cancel κ` may be typed at `⊤`, but never at a type that can be run.

**A-DIV: divergence is an effect (decision 35).**

```lean
/-- First-order data are the observable answers; every returner at a data answer is claimed to
terminate; a computation that may run forever is a `Loop`, observed by `next` and `close` and run by
the drive. -/
def DataDiv (S) : Prop :=
  S.Data S.UnitT ∧ (∀ A B, S.Data A → S.Data B → S.Data (S.Tensor A B) ∧ S.Data (S.Sum A B)) ∧
  (∀ C, ¬ S.Data (S.U C)) ∧ (∀ c B C, ¬ S.Data (S.kTy c B C)) ∧
  (∀ ε A, S.Data A → S.DivFree (S.F ε A)) ∧
  (∀ Θ Γ l ε A B, S.der Θ Γ (S.val l) (.val (S.U (S.Loop ε A B))) →
     S.der Θ Γ (S.next l) (.comp (S.F ε (S.Sum A (S.U (S.Loop ε A B))))) ∧
     S.der Θ Γ (S.close l) (.comp (S.F ε B)))
```

Decision 35: "Any function may loop without bound if its type says so; … code without it is total
(a theorem, `total_no_infinite_run`). A div function returns a loop, `A ⇒ U(Loop B R)`; … running a
loop is handling the effect: the runtime drives `main` forever". `DivFree` is pinned from below at
every data answer, so A1's termination clause has content. `Loop` has its observations and the
drive (`DStep`, `SafeDrive`), and A-ACC asks for a loop that is driven and one whose drive never
ends. So an instance that types no divergence fails A, and so does one that tracks divergence
nowhere.

**A-ACC: acceptance witnesses (lower bounds).** Each is an event sequence on a complete run, under
the platform with no operation, of a closed program typed at a data answer at the pure row.

```lean
def Witness (S) (P : S.Term → List (S.Ev × S.RConf S.R₀) → Prop) : Prop :=
  ∃ e A q, S.Data A ∧ S.der [] S.emp e (.comp (S.F S.EA.unit A)) ∧
    S.CompleteFrom S.R₀ (S.rinit S.R₀ e) q ∧ P e q

def Acceptance (S) : Prop :=
  -- (a) deep, linear: a linear operation caught, its continuation resumed, and an operation the
  --     resumed context performs caught again by the same handler
  S.Witness (fun e q => ∃ j₁ j₂ j₃ K₀ K₀' l H K K' i i' v v' o,
      j₁ < j₂ ∧ j₂ < j₃ ∧ (S.sig l)[i]? = some o ∧ o.cls = .linear ∧
      S.AtCatch (q.cfg _ j₁).1 K₀ l H K i v ∧ S.AtResume (q.cfg _ j₂).1 l H K ∧
      S.AtCatch (q.cfg _ j₃).1 K₀' l H K' i' v') ∧
  -- (b) affine, cancelled: the cancel completes, its one frozen finaliser fired, the canceller answered
  S.Witness (fun e q => ∃ j₁ j₂ j₃ j₄ K₀ K₁ l H K i v o D,
      j₁ < j₂ ∧ j₂ ≤ j₃ ∧ j₃ < j₄ ∧ (S.sig l)[i]? = some o ∧ o.cls = .affine ∧
      S.AtCatch (q.cfg _ j₁).1 K₀ l H K i v ∧ S.AtCancel (q.cfg _ j₂).1 K₁ l H K ∧ S.fins K = [D] ∧
      S.term (q.cfg _ j₃).1 = S.plug K₁ (S.cancelOf l H K) ∧
      S.CancelTrace S.R₀ (S.Region l K) K₁ (q.cfg _ j₃) [D] none (q.seg j₃ j₄) ∧
      S.Answered K₁ none (S.term (q.cfg _ j₄).1)) ∧
  -- (c) a raise caught by a handler
  S.Witness (fun e q => ∃ j l i o, q.ev j = .catch l i ∧ (S.sig l)[i]? = some o ∧ o.cls = .abortive) ∧
  -- (d) an unwind through a finaliser frame
  S.Witness (fun e q => ∃ j j' K₀ K m i w D, j < j' ∧
      S.term (q.cfg _ j).1 = S.plug K₀ (S.plug K (S.raise m i w)) ∧ S.catches K m = false ∧
      D ∈ S.fins K ∧ q.ev j' = .fire D) ∧
  -- (e) a loop driven: a complete drive in which the loop goes on at least once
  (∃ e A B d, S.Data A ∧ S.der [] S.emp e (.comp (S.F S.EA.unit (S.U (S.Loop S.EA.unit A B)))) ∧
     S.DPath S.R₀ (S.rinit S.R₀ e, .main) d ∧ S.FinalDrive (d.cfg _ d.length) ∧
     ∃ j l, (d.cfg _ j).2 = .drive ∧ S.term (d.cfg _ j).1.1 = S.ret (S.inr l) ∧ j < d.length) ∧
  -- (f) divergence: a loop whose drive never finishes
  (∃ e A B, S.der [] S.emp e (.comp (S.F S.EA.unit (S.U (S.Loop S.EA.unit A B)))) ∧
     ∀ n, ∃ d, S.DPath S.R₀ (S.rinit S.R₀ e, .main) d ∧ n ≤ d.length ∧ ∀ j, ¬ S.FinalDrive (d.cfg _ j))
```

`CancelTrace`, `Region` and `Answered` are A-CAN's (§1.4). Witness (b) has a complete cancel: the
trace reaches the answer, so A-CAN's order is not vacuous. With `EffRules` (closure) and the safety
properties of §1.4 (upper bounds), these keep A from being met by an instance with no effects, no
runs, an empty typing, no affine operations, no finalisers, shallow handlers or no divergence
(§6.1).

**Admissible.**

```lean
def Admissible (S) : Prop :=
  MachShape S ∧ RowAlgebra S ∧ RowSig S ∧ TySubst S ∧ RowPoly S ∧ EffRules S ∧
  HandlerSem S ∧ ContDiscipline S ∧ DataDiv S ∧ Acceptance S
```

### 1.4 Properties: A₁, the first pass

Each is a theorem an instance proves.

**P2 Effect safety.**

```lean
/-- A stop at an operation the row admits: an uncaught `perform` of a resuming operation, or an
uncaught `raise` of an abortive one with no finaliser frame in the way. -/
def StopsIn (S) (ε) (c : S.Conf) : Prop :=
  ∃ K l i v o, (S.sig l)[i]? = some o ∧ S.has ε l i ∧ S.catches K l = false ∧
    ((S.term c = S.plug K (S.perform l i v) ∧ o.cls ≠ .abortive) ∨
     (S.term c = S.plug K (S.raise l i v) ∧ o.cls = .abortive ∧ S.unwindClear K))

def EffSafe (S) : Prop :=
  ∀ e ε A, S.der [] S.emp e (.comp (S.F ε A)) → ∀ c, S.Reach (S.init e) c →
    S.IsVal c ∨ (∃ ev c', S.step c ev c') ∨ S.StopsIn ε c
```

At `ε = 0`, `RowSig` gives `¬ S.has 0 l i`, so `StopsIn 0` is empty: no unhandled operation. Sources:
Yoshioka Lemma 5.4 ("If ∅ ⊢ e : A | ε and e −→∗ e′ ↛, then … e′ = v … or e′ = E[op_l S T v] … such
that 0−free(l S, E)") and Thm 5.8 ("If ∅ ⊢ e : A | 0 and e −→∗ e′ ↛, then e′ = v for some v");
Bauer–Pretnar Thm 4.1 (Progress: "either • there exists a computation c′ such that c ⇝ c′, or • c is
of the form val e …, or • c is of the form ι#op e (x. c′) for some ι#op ∈ ∆"); Tang Thm 3.2; System C
Cor. 9 ("never results in an undelimited label").

**A1 Safety and divergence.**

```lean
/-- Under every platform that keeps its protocol, every run of a program at a row the platform
answers is never stuck; at a div-free answer it terminates; a returned loop is safe on every finite
prefix of its drive. -/
def Safety (S) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε →
    (S.der [] S.emp e (.comp (S.F ε A)) → S.SafeRuns R e ∧ (S.DivFree (S.F ε A) → S.Terminates R e)) ∧
    (∀ B, S.Data A → S.der [] S.emp e (.comp (S.F ε (S.U (S.Loop ε A B)))) → S.SafeDrive R e)
```

Sources: Affect §3.2's `safe e`, and "⊢ e : ⟨⟩ : τ ⊣ =⇒ safe e"; Bauer–Pretnar Cor. 4.2 ("A
terminating computation of type A ! ∆ returns a value of type A, or calls an operation in ∆. In
particular, a terminating computation of type A ! ∅ does not call any operations and returns a pure
value of type A"); [CONF] 415:18, adequacy "really does characterize executions that are safe,
terminating, and reclaim memory". `DataDiv` makes every data answer div-free, so termination is
claimed at every data answer and divergence lives in `Loop`. Main's row is the platform's (OQ-51
(a)): `Answers R ε` with `R.Respects` leaves only linear data operations in `ε`, so an abortive
operation must be handled before the top.

**A-CAN Cancellation, as built (SPEC §19; decision 62).** This is our semantics, not a literature
theorem. SPEC §19 states what is built: "A cancel is not interceptable. The frames of the cancelled
region … are being torn down: nothing in the region resumes, and its handlers are dying, so they
catch nothing"; "An error raised by a finaliser during a cancel is re-raised at the canceller, after
every frame of the region has finalised"; "Several failures: the first is re-raised, and the rest
are suppressed"; "An error of a name in `N` … is suppressed"; "Ordinary unwinding … a finaliser's
raise supersedes the pending one and is caught by the live handlers around the finaliser". The
traces below state each of these over A's steps and events.

```lean
/-- SPEC §19's cancel state: the error kept so far. -/
abbrev Err (S) := Option (S.EA.Lab × ℕ × S.Val)

/-- [cfin-raise]: "err′ = err if err ≠ none; none if m ∈ N; (m, v) otherwise"; [cfin-ret] keeps it. -/
noncomputable def keep (N : S.EA.Lab → Prop) : S.Err → S.Err → S.Err
  | some e, _ => some e
  | none, none => none
  | none, some (m, j, w) => by classical exact if N m then none else some (m, j, w)

/-- The region a cancel of `capture l H K` tears down: `l` and every label a handler frame of `K`
catches (SPEC's `N`, "the region's handlers"). -/
def Region (S) (l : S.EA.Lab) (K : S.Kont) (m : S.EA.Lab) : Prop := m = l ∨ S.catches K m = true

/-- The canceller is answered ([cancel], [cancel-raise]): `()`, or the kept error raised at it. -/
def Answered (S) (K₀ : S.Kont) : S.Err → S.Term → Prop
  | none, t => t = S.plug K₀ (S.ret S.unitV)
  | some (m, j, w), t => t = S.plug K₀ (S.raise m j w)

/-- Along `q` from `c`, the term inside the frozen context `Kf` runs alone: each step of the whole
configuration is that term's own step, the context taking no part. -/
inductive Alone (S) (R) (Kf : S.Kont) : S.RConf R → List (S.Ev × S.RConf R) → S.RConf R → Prop
  | nil {c} : Alone c [] c
  | cons {c ev c' t t' q c''} :
      S.term c.1 = S.plug Kf t → S.term c'.1 = S.plug Kf t' →
      S.RStep R c ev c' → S.RStep R (S.setR c t) ev (S.setR c' t') →
      Alone c' q c'' → Alone c ((ev, c') :: q) c''

/-- At `c` the term inside `Kf` has ended: it returned (`none`), or a raise escaped it (`some`). -/
def Ended (S) (Kf : S.Kont) (c : S.RConf R) : S.Err → Prop
  | none => ∃ v, S.term c.1 = S.plug Kf (S.ret v)
  | some (m, j, w) => ∃ K, S.term c.1 = S.plug Kf (S.plug K (S.raise m j w)) ∧
      S.catches K m = false ∧ S.unwindClear K

mutual
/-- **A cancel trace**: from the start of a cancel, `fs` the frozen finalisers not yet fired and
`err` the error kept so far.  Each finaliser fires, innermost first, and runs alone to its end; its
end updates the kept error; last, the canceller is answered.  Prefix-closed: a trace may stop
anywhere, and after the answer anything may follow. -/
inductive CancelTrace (S) (R) (N : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.RConf R → List S.Val → S.Err → List (S.Ev × S.RConf R) → Prop
  | stop {c fs err} : CancelTrace c fs err []
  | answer {c c' err q} : S.RStep R c .tau c' → S.Answered K₀ err (S.term c'.1) →
      CancelTrace c [] err ((.tau, c') :: q)
  | fire {c c₁ D fs err Kf q} : S.RStep R c (.fire D) c₁ →
      S.term c₁.1 = S.plug Kf (S.app D S.unitV) → FinTrace R N K₀ Kf c₁ fs err q →
      CancelTrace c (D :: fs) err ((.fire D, c₁) :: q)
/-- The fired finaliser runs alone; when it ends, the `finEnd` step closes it and the cancel goes on. -/
inductive FinTrace (S) (R) (N : S.EA.Lab → Prop) (K₀ Kf : S.Kont) :
    S.RConf R → List S.Val → S.Err → List (S.Ev × S.RConf R) → Prop
  | running {c fs err q c'} : S.Alone R Kf c q c' → FinTrace c fs err q
  | ended {c fs err q c' r c'' q'} : S.Alone R Kf c q c' → S.Ended Kf c' r →
      S.RStep R c' (.finEnd r) c'' → CancelTrace R N K₀ c'' fs (keep N err r) q' →
      FinTrace c fs err (q ++ (.finEnd r, c'') :: q')
end

/-- **Not interceptable, in order, with the error policy.**  Every run of a typed program from the
start of a cancel of `capture l H K` follows a cancel trace of `fins K` with nothing kept. -/
def NoIntercept (S) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] S.emp e (.comp (S.F ε A)) →
    ∀ c₀ c K₀ l H K q, S.RReach R (S.rinit R e) c₀ →
      S.AtCancel c₀.1 K₀ l H K → S.PureSteps c₀.1 c.1 → c.2 = c₀.2 →
      S.term c.1 = S.plug K₀ (S.cancelOf l H K) →
      S.RPath R c q → S.CancelTrace R (S.Region l K) K₀ c (S.fins K) none q

/-- `K`'s frames that stop a raise are handler frames and finaliser frames. -/
inductive Std (S) : S.Kont → Prop
  | clear {K} : S.unwindClear K → Std K
  | frame {K₁ K₂ F} : S.unwindClear K₁ → ((∃ l H, F = S.handleF l H) ∨ (∃ N D, F = S.thenF N D)) →
      Std K₂ → Std (S.kcomp K₂ (S.kcomp F K₁))

mutual
/-- **An unwind trace**: a raise pending under `K`, inside the fixed outer context `K₀`.  The first
frame of `K` that stops the raise decides.  A handler frame of its label catches it, and the unwind
is over.  A finaliser frame fires its finaliser, which runs alone in a frozen context: if it
returns, the pending raise goes on through the rest of `K`; if a raise escapes it, that raise
supersedes the pending one.  Once the pending raise has left `K`, the unwind is over.
Prefix-closed. -/
inductive UnwindTrace (S) (R) (K₀ : S.Kont) : S.RConf R → S.Kont → List (S.Ev × S.RConf R) → Prop
  | stop {c K} : UnwindTrace c K []
  | out {c K m j w q} : S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) →
      S.catches K m = false → S.unwindClear K → UnwindTrace c K q
  | caught {c c' K K₁ K₂ H m j w q} : K = S.kcomp K₂ (S.kcomp (S.handleF m H) K₁) →
      S.catches K₁ m = false → S.unwindClear K₁ →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.RStep R c (.catch m j) c' →
      UnwindTrace c K ((.catch m j, c') :: q)
  | fire {c c₁ K K₁ K₂ N D Kp m j w q} : K = S.kcomp K₂ (S.kcomp (S.thenF N D) K₁) →
      S.catches K₁ m = false → S.unwindClear K₁ →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.RStep R c (.fire D) c₁ →
      (∀ m', S.catches Kp m' = false) → S.unwindClear Kp →
      S.term c₁.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) (S.app D S.unitV) →
      PendTrace R K₀ K₂ Kp (m, j, w) c₁ q → UnwindTrace c K ((.fire D, c₁) :: q)
/-- The finaliser runs alone in `K₀ ∘ K₂ ∘ Kp`, the frame `Kp` holding the pending raise `p`. -/
inductive PendTrace (S) (R) (K₀ K₂ Kp : S.Kont) (p : S.EA.Lab × ℕ × S.Val) :
    S.RConf R → List (S.Ev × S.RConf R) → Prop
  | running {c q c'} : S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' → PendTrace c q
  | returning {c q c' q₁ c''} : S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.Ended (S.kcomp (S.kcomp K₀ K₂) Kp) c' none → S.PurePath c' q₁ c'' → PendTrace c (q ++ q₁)
  | returned {c q c' q₁ c'' q₂} : S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.Ended (S.kcomp (S.kcomp K₀ K₂) Kp) c' none → S.PurePath c' q₁ c'' →
      S.term c''.1 = S.plug K₀ (S.plug K₂ (S.raise p.1 p.2.1 p.2.2)) →
      UnwindTrace R K₀ c'' K₂ q₂ → PendTrace c (q ++ q₁ ++ q₂)
  | superseded {c q c' K' m' j' w' q₂} : S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.term c'.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) (S.plug K' (S.raise m' j' w')) →
      S.catches K' m' = false → S.unwindClear K' →
      UnwindTrace R K₀ c' (S.kcomp K₂ (S.kcomp Kp K')) q₂ → PendTrace c (q ++ q₂)
end

/-- **The unwind**: every run of a typed program from an uncaught raise through `K` follows an
unwind trace of `K`: `fins K` fire once each, innermost first, until a handler catches the pending
raise or it leaves `K`. -/
def UnwindOrder (S) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] S.emp e (.comp (S.F ε A)) →
    ∀ c K₀ K m j w q, S.RReach R (S.rinit R e) c → S.Std K →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      S.RPath R c q → S.UnwindTrace R K₀ c K q

def Cancellation (S) : Prop := NoIntercept S ∧ UnwindOrder S
```

What each piece carries:

- **The order.** `CancelTrace` fires `fins K` in list order (innermost first), each once. Its only
  `answer` case is at `fs = []`, so a run that reaches the canceller's answer has fired every frozen
  finaliser: the old `CancelOrder` is a corollary (`cancelOrder_of_noIntercept`, to build).
- **Not interceptable.** Between the cancel's start and its answer, every step is either a fire, a
  step of the running finaliser alone (`Alone`: the frozen region takes no part), a `finEnd`, or
  the answer. No code of the region runs and none of its handlers catches. This holds only until the
  answer: `CancelTrace.answer` lets anything follow, which fixes the old `NoIntercept`'s reach past
  the answer.
- **The error policy.** `Region l K` is the region's label set, read from `K`'s handler frames.
  `keep` is [cfin-raise] verbatim, and `Answered` is [cancel] and [cancel-raise].
- **The unwind.** `UnwindTrace` reads `catches K m = false` (the AGREE minor finding) and admits
  handler frames of other labels in `K`. A superseding raise those frames catch ends the unwind
  (`caught`), as SPEC says ("caught by the live handlers around the finaliser"). `Std K` excludes
  contexts with instance frames that stop raises other than handlers and finalisers: at Core, the
  `ccatch` and `cfin` frames of a cancel in progress, which `CancelTrace` covers.
- **Over runs under a runner** (the AGREE minor finding), **at every row the runner answers**:
  `Answers R ε`, as `Safety` reads it. So programs at the platform's row are constrained, not only
  programs at row `0`.

**P11 Handler correctness, unary.**

```lean
/-- A pure step is the only step its configuration has: unique decomposition and determinism of
the steps that change no store. -/
def HandlerRed (S) : Prop :=
  ∀ c ev₁ c₁ ev₂ c₂, S.PureStep c ev₁ c₁ → S.step c ev₂ c₂ → ev₂ = ev₁ ∧ c₂ = c₁
```

With `HandlerSem`, the homomorphism equations then hold as observational equalities: Plotkin–Pretnar
§1.3, "computations are interpreted in the free model and handling constructs are interpreted by the
induced homomorphisms". At our instance this is unique decomposition and the determinism of
non-allocating head steps (`plug_cmp`, `plug_decomp`, `head_det_eff`, `Core/Steps.lean`). The
semantic form (the `[handle]` rule sound in a logical relation) is a proof-device fact (§3.4,
`HandleCompat`), not an A property.

**The first pass, together.**

```lean
def Props₁ (S) : Prop := Admissible S ∧ EffSafe S ∧ Safety S ∧ Cancellation S ∧ HandlerRed S
```

### 1.5 Beside the first pass: the continuation's use count (P8.b)

```lean
/-- An observation of continuation use (Tang et al.'s tagged semantics, or a one-shot cell): along
a run of the machine, tags are created, resumed and cancelled, each naming a continuation. -/
structure UseObs (S : EffectSystem) where
  Tag : Type
  cls : Tag → OpClass
  val : Tag → S.Val
  created resumed cancelled : S.Conf → List (S.Ev × S.Conf) → ℕ → Tag → Prop

/-- **Tied to A's steps.**  Every catch of a resuming operation creates a tag of its class, naming
the continuation the clause is handed; every resume and every cancel of a captured continuation
consumes a tag naming it; nothing else creates or consumes. -/
def UseObs.Sound (U : UseObs S) : Prop :=
  (∀ c q j K₀ l H K i v o, S.MPath c q → S.AtCatch (q.cfg c j) K₀ l H K i v → (S.sig l)[i]? = some o →
     o.cls ≠ .abortive → ∃ t, U.created c q j t ∧ U.cls t = o.cls ∧ U.val t = S.capture l H K) ∧
  (∀ c q j K₁ l H K w, S.MPath c q → S.term (q.cfg c j) = S.plug K₁ (S.resume (S.capture l H K) w) →
     ∃ t, U.resumed c q j t ∧ U.val t = S.capture l H K) ∧
  (∀ c q j K₁ l H K, S.MPath c q → S.AtCancel (q.cfg c j) K₁ l H K →
     ∃ t, U.cancelled c q j t ∧ U.val t = S.capture l H K) ∧
  (∀ c q j t, U.created c q j t → ∃ K₀ l H K i v, S.AtCatch (q.cfg c j) K₀ l H K i v) ∧
  (∀ c q j t, U.resumed c q j t → ∃ l H K, S.AtResume (q.cfg c j) l H K) ∧
  (∀ c q j t, U.cancelled c q j t → ∃ K₁ l H K, S.AtCancel (q.cfg c j) K₁ l H K)

/-- **P8.b**: each linear κ is resumed exactly once and never cancelled; each affine κ is resumed
or cancelled exactly once. -/
def ContUse (S) (U : UseObs S) : Prop :=
  ∀ e A q, S.der [] S.emp e (.comp (S.F S.EA.unit A)) → S.MComplete (S.init e) q →
    ∀ j t, U.created (S.init e) q j t →
      (U.cls t = .linear → (∃! j', U.resumed (S.init e) q j' t) ∧ ¬ ∃ j', U.cancelled (S.init e) q j' t) ∧
      (U.cls t = .affine → ∃! j', U.resumed (S.init e) q j' t ∨ U.cancelled (S.init e) q j' t)

def P8b (S) : Prop := ∃ U : UseObs S, U.Sound ∧ ContUse S U
```

`Sound` excludes `created := ⊥`: every catch creates a tag. It also excludes over-creation, and
consumption matched against the wrong continuation: a tag names the κ it was created for, and a
resume consumes one naming the resumed κ. What it leaves to the instance is which tag a step uses
among those naming equal continuations. That is OQ-50's question: instrumented tags (OQ-50 (a)) or a
one-shot cell, whose location is the tag (OQ-50 (b)). Source: Tang Thm 3.6 ("ℒ(M) ∪ S = ℒ(N) ∪ T"),
and its gloss "no linear value is ever discarded or duplicated during evaluation". Done holds the
resource half (B5 at the runs that cancel, §2.4) and A-LIN's typing.

### 1.6 A₂: binary, out of the first pass

The user, 2026-10-02: binary laws are "optional and don't get pursued unless they become necessary
for safety". Stated over A's own contextual approximation:

```lean
/-- `t₁ ≼ t₂` at `U C`: every typed closing context at a data answer observes no more of `t₁`. -/
def CtxApprox (S) (R : S.Runner) (C : S.CTy) (t₁ t₂ : S.Val) : Prop :=
  ∀ f ε A, S.Data A → S.Answers R ε → S.der [] (S.one (S.U C)) f (.comp (S.F ε A)) →
    ∀ tr v, S.Obs R (S.subst0 f t₁) tr v → S.Obs R (S.subst0 f t₂) tr v
```

| target | statement | source |
|---|---|---|
| `Laws S` (T2) | return, operation, forwarding, the tail-resumptive law, algebraicity at linear and affine operations, capture β and η, hiding, fusion (at a composite-handler parameter, OQ-49), as `CtxApprox` both ways | Plotkin–Pretnar §1.1 ("return V handled with {raise_e () ↦ N_e} to x : A. N(x) = N(V)"), Def. 4.5 |
| `EffDepLaws S` | Discard, Copy, Swap, each graded by the operations a row may perform | Kammar thesis (11.1): "Γ ⊢_ε M : F_ε A, Γ ⊢_ε′ N : B (ε ⊆ ε′) ⟹ ⊨ coerce_{ε⊆ε′} M to x : A. N = N", "if N does not directly depend on the result of the returner M, then the computation M may be discarded"; Thm 12.5: "the theory Th_Ax satisfies the Discard optimisation if and only if for every op : n in σ, op(x, …, x) = x"; "Copy corresponds to a global idempotency law, and … Swap corresponds to commutativity" |
| `Abstraction S` (T3) | `Tunnel` (Zhang–Myers Example 1 at A-ROW's row variable), `RepInd`, `Encap` | Zhang–Myers: "it is impossible for higher-order, effect-polymorphic code to accidentally handle effects raised by functions passed in"; Thm 1, Thm 3 ("t1 ≼log t2 … ⇒ t1 ≼ctx t2") |

The Kammar–Plotkin POPL 2012 PDF could not be retrieved (both known links return 404); its
statements are quoted from Kammar's thesis, which extends it. Our signatures carry no equations
(OQ-22), so absorption `op(x, …, x) = x` holds of no operation, and `EffDepLaws` reduce to the pure
row until equations are added.

### 1.7 A₃: the erased lowering, cross-language, out of the first pass (finding #4)

```lean
/-- What a target run pays for. -/
inductive ObjKind | data | closure | cont        -- a heap object: data, a closure, a reified continuation
inductive CallKind | direct | indirect | search  -- a call: to a known address, through a code pointer, by handler search
inductive TEv | alloc (k : ObjKind) | call (k : CallKind)

/-- **A target language**: programs; their complete runs under a platform, observed in A's terms
(the `io` trace and the answer) with the cost events they pay; and its state machines, a finite
state type each, embedded as programs. -/
structure Target (S : EffectSystem) where
  Tm    : Type
  run   : S.Runner → Tm → List (S.EA.Lab × ℕ × S.Val × S.Val) → S.Val → List TEv → Prop
  SM    : Type
  St    : SM → Type
  fin   : ∀ m, Fintype (St m)
  embed : SM → Tm

/-- No handler runtime: no run reifies a continuation or searches for a handler. -/
def Target.HandlerFree (T : Target S) (R) (t : T.Tm) : Prop :=
  ∀ tr v evs, T.run R t tr v evs → TEv.alloc .cont ∉ evs ∧ TEv.call .search ∉ evs

def cost (evs : List TEv) : ℕ × ℕ :=
  ((evs.filter (· matches .alloc _)).length, (evs.filter (· = .call .indirect)).length)

inductive LowClass | answering | abortive | control

/-- A tail-resumptive clause: given its argument and κ, it reaches `resume κ w` by pure steps, in
tail position. -/
def TailResumptive (S) (H) (i) : Prop :=
  ∀ v κ, ∃ w c, S.PureSteps (S.init (S.app (S.opC H i) (S.pair v κ))) c ∧ S.term c = S.resume κ w

/-- **The lowering classes, read off A's runs.**  Abortive: no run catches a resuming operation.
Answering: every resuming operation a run catches is caught by a tail-resumptive clause.  Control:
neither. -/
def OfAbortive (S) (e : S.Term) : Prop :=
  ∀ c, S.Reach (S.init e) c → ∀ K₀ l H K i v, ¬ S.AtCatch c K₀ l H K i v
def OfAnswering (S) (e : S.Term) : Prop :=
  ∀ c, S.Reach (S.init e) c → ∀ K₀ l H K i v, S.AtCatch c K₀ l H K i v → S.TailResumptive H i
def Of (S) : LowClass → S.Term → Prop
  | .abortive, e => S.OfAbortive e
  | .answering, e => S.OfAnswering e
  | .control, e => ¬ S.OfAbortive e ∧ ¬ S.OfAnswering e

structure Lowering (S) where
  T     : Target S
  lower : S.Term → T.Tm
  ref   : LowClass → S.Term → Option T.Tm      -- the code a C or Rust programmer writes by hand

-- `Typed R e` abbreviates: `∃ ε A, R.Respects ∧ S.Answers R ε ∧ S.Data A ∧ S.der [] S.emp e (.comp (S.F ε A))`.

/-- The target observes exactly what the source does (A's `Obs`). -/
def LoweringCorrect (S) (L : Lowering S) : Prop :=
  ∀ R e tr v, Typed R e → (S.Obs R e tr v ↔ ∃ evs, L.T.run R (L.lower e) tr v evs)

/-- **Effect handling is erased**: resume-once is a call and abort a branch (no handler runtime),
and suspension a state machine. -/
def Erased (S) (L : Lowering S) : Prop :=
  (∀ R e, Typed R e → (S.Of .answering e ∨ S.Of .abortive e) → L.T.HandlerFree R (L.lower e)) ∧
  (∀ R e, Typed R e → S.Of .control e →
     ∃ m : L.T.SM, L.lower e = L.T.embed m ∧ L.T.HandlerFree R (L.lower e))

/-- **Zero cost**: every answering or abortive program has a correct, handler-free reference, and the
lowering pays no more than it. -/
def ZeroCost (S) (L : Lowering S) : Prop :=
  (∀ c R e, c ≠ .control → S.Of c e → Typed R e → ∃ t, L.ref c e = some t ∧ L.T.HandlerFree R t ∧
     ∀ tr v, S.Obs R e tr v ↔ ∃ evs, L.T.run R t tr v evs) ∧
  (∀ c R e t tr v evs evs', L.ref c e = some t → L.T.run R (L.lower e) tr v evs → L.T.run R t tr v evs' →
     cost evs ≤ cost evs')
```

The finding's degenerate instances are excluded. The source side is A's `Obs`, both ways, not a
field. The classes are A's, read off its runs and clauses. References must exist for every
answering and abortive program, must compute the same observations, and must be handler-free.
`HandlerFree` is defined from the target's own run events, and a control program must lower to an
embedded state machine. What remains the instance's is the target language itself: its runs and the
events they are labelled with. That is the backend's definition, as `W` is I's. It is reviewed, not
audited, and nothing in A can pin a target's cost model from the source side. Sources: Ma–Ge–Jung–Zhang,
OOPSLA 2025, Cor. 1: "if a closed, well-typed SL program terminates with a value, then its
translation in TL also terminates and produces the expected result"; the zero-overhead principle,
"what you don't use, you don't pay for … code should not pay for exceptions unless they are actually
raised". Whether lowering correctness is a theorem, and the control class's cost model, are OQ-23
(the user). For our backend, `Tm` is the flat IR, `run` its fuel-parametric stage interpreter with
`FState.allocs`/`FState.indirect` as events, and `ref` is defined for the answering and abortive
classes (§4.1).

### 1.8 Every decided feature, and where A requires it

| decided feature (strength in the brief) | required by |
|---|---|
| rows are sums of signatures; one signature object | `sig`, `has`, `RowSig`: `(l)↑` is exactly `sig l`'s operations, `⊙` is union; `[handle]` removes `(l)↑` from `(l)↑ ⊙ ε` (A-RULES). A part of a signature is a row only where SPEC §19 builds one (`Σ^abort`) |
| row variables in the kernel (decision 62) | `EffAlg.var` with `VarLaws`; `TySubst`; `All` with T_TAbs and T_TApp; the substitution conjunct; `AccRowPoly`, one closed program with one generic `f` at two rows (A-ROW). `audit_J` (§5.2) checks the named kernel's representation |
| handlers are deep (decision 62) | `HandlerSem`'s deep resume; `HndTyped` (κ answers the handling's type; clauses `!`); A-ACC (a): a second catch by the same handler after a resume |
| continuations linear or affine; discard is an explicit cancel; no forget | `OpClass`; A-LIN: `Structural` (`Drop` is exactly what the unit value may be typed beside, `Pers` exactly what may be paired with itself, at every context), κ neither `Drop` nor `Pers`, no κ eliminated twice in sequence, resume and affine cancel typed, no runnable cancel of a linear κ; A-SEM's cancel entry; B5 at the runs that cancel (done); P8.b `ContUse` beside (the run-level count, OQ-50) |
| cancellation as built (SPEC §19; decision 62) | A-CAN: `CancelTrace` (order, error policy, region read from `K`'s handler frames, answer), `NoIntercept` (bounded by the answer), `UnwindTrace` (supersession, handlers of other labels); A-ACC (b), (d) |
| divergence is an effect (codata); totality not a goal | A-DIV: `Data` pinned, every data answer div-free, `Loop` with `next`/`close` and the drive; A1 `Safety` (termination at every div-free answer, a safe drive at `Loop`); A-ACC (e), (f): a driven loop and a loop that never ends |
| errors are abortive operations (`raise`) | `OpClass.abortive`; A-RULES's [raise] at any answer; A-SEM's abortive clause and finaliser firing; `UnwindTrace`. "No sum for failure" is not stated in A: §7 Q5 |
| effect handling is erased at runtime | A₃: `Lowering` over a `Target`, `LoweringCorrect`, `Erased` (no handler runtime; control lowers to a state machine), `ZeroCost` (references required), out of the first pass (OQ-23) |
| multi-shot is ignored (decision 63) | nothing: `OpClass` has no unrestricted class; the Instance reads Core's unr-free fragment (§4.1) |
| higher-order operations: not now | `OpSig`'s arities are value types; scoped operations would extend `OpSig` |
| laws first; binary laws optional | A-SEM states handling as the homomorphism's equations; A₂ states the binary laws, out of the first pass |
| effects are core | the instance's effect formers are kernel primitives; `audit_J` checks that row variables are kernel syntax |
| no step-indexing (decision 7) | not an A property: a property of W's definition (`audit_W`, §5.2) |
| nothing breaks the borrow calculus | B's guarantees in `Combined` (§3.5) |
| handler state passed to each clause (decision 59) | not an A requirement: a stateful handler is a state-passing handler (I4's `ctlForm`) |
| threads required eventually | not a requirement now; A's machine is sequential, and nothing in A excludes a concurrent instance |

---

## 2. System B: the borrow calculus, given

System B is BoLo ([CONF], [TR]) as transcribed in `Paper/` and, at Core's CBPV machine, in `Core/`.
Its guarantees are given. B states them as Props over a typing system `J` and a borrow world `M`,
so that they can be asked of the composite, and proves each at BoLo by citation. "Given" means: at
`coreB`/`tier1`, at the platform with no operation. Under a platform that answers operations, the
same Props are the composite's, and live in done.

### 2.1 B's world

```lean
namespace B

/-- **A borrow world**: BoLo's Kripke world as a parameter.  The lend stack `σ`; the configurations
the world reaches (`TW` at Core); the run-end relation `↭`; the Kripke order; the stack a cell's
stored payload is read at (OQ-46); the relation.  Nothing of effects: no stop condition, no
continuation share, nothing held by suspensions.  `I.SemWorld` extends it with those. -/
structure BWorld where
  Stk    : Type
  nil    : Stk
  Fam    : WRes → List FrameRec → Idx Stk → Prop
  Upd    : Idx Stk → Idx Stk → WRes → WRes → WRes → Prop
  Ext    : Idx Stk → Idx Stk → WRes → Prop
  payStk : Life → Stk → Stk
  val    : Bool → VTy → Idx Stk → LSub → Val → WProp
  comp   : CTy → Idx Stk → LSub → Expr → WProp

/-- Core's relation as a borrow world, the lend stack one point. -/
@[reducible] def coreB : BWorld :=
  ⟨Unit, (), fun fρ ps i => TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1, fun _ _ ρ _ π => ResU.UpdV ρ π,
   fun i i' ρ => Ext i.1 i'.1 ρ, fun _ _ => (), fun b A i δ v => vCE none b A i.1 δ v,
   fun C i δ e => cC C i.1 δ e⟩
```

B owns every definition that reads only these fields: `ptoMutSW`, `ptoImmSW`, `gSepW`, `gDenW`,
`SemWC`, `SemW₀`, `SemW`, `FL`, `AdequateRetAt`, `AdequateDriveAt`, `AdequateAt`, `Adequate`,
`ContractsW`, and the bounds below.

### 2.2 The guarantees

| id | guarantee | Prop (B) | printed | given by | status at BoLo |
|---|---|---|---|---|---|
| B1 | fundamental property | `FL M ⟦J⟧` | [TR] 6.151: "If ∆; Γ ⊢ e ∶ T then ∆; Γ ⊧ e ∶ T." | `fundamentalC` (`Core/Fundamental.lean:434`); `Paper`: `Fig16.LogRel.Typed.fundamentalProperty` | PROVED AT σ=[] (`fl_core_tier1`, `fl_core_tier1NU`, checked; at `coreB`) |
| B2 | adequacy | `Adequate M` | [CONF] Thm 3.2: "If ⊨ wp (e) {⌜P̂⌝} then (∅, e) →∗ (∅, v) and P̂(v) for some v"; Cor. 3.3 | `theorem32D`, `adequacyD` (`Core/Demonic.lean:292,312`) | PROVED AT A RESTRICTION (platform with no operation, data answers: `adequateRetAt_core_none`, checked); every platform and drives: OPEN |
| B3 | no use after free, no double free: no run stuck, under every allocator | `Sound J M`'s `SafeRuns` | [CONF] 415:18, "executions that are safe" | `adequacyD_safe`, `wpTSD_safe`; `Core/Stale.lean` (why every allocator) | PROVED AT A RESTRICTION (`soundRetAt_tier1_none`, checked) |
| B4 | leak freedom: every complete run at a data answer ends with the memory empty | `Sound J M`'s `Terminates` with `Final` | [CONF] 415:23: "the discarded fragment ρ⁺ must not contain any owned cells. This is essential for the memory reclamation component of adequacy" | `adequacyD`, `reclaim` (`Core/Fundamental.lean:534`), `NoOwn` (`Paper/S5_Model/Definitions.lean:1362`) | PROVED AT A RESTRICTION (`soundRetAt_tier1_none`, checked) |
| B5 | exactly-once release, location reuse included | `ReleasedOnceEvery J M` (§2.4) | not printed: our per-allocation reading of B3 with B4 | B3, B4 and the machine lemma `ReuseUnobservable` (OQ-43, §2.4) | OPEN |
| B6 | exclusive mutable borrows | `ExclusiveB M`: every configuration the world reaches is a valid resource | [CONF] 415:21: "in a valid resource, every pair of aliases map to the same object and each has an immutable ancestor" | `TW.valid` (`Core/Invariant.lean:1802`) | PROVED AT σ=[] (`exclusiveB_core`, to build: the validity half of `exclusive_core`, checked) |
| B7 | lifetimes respected | `LifetimeSound M J.out` | [TR] 6.60: "If ∆ ⊢ T ⊐ @a and δ ∈ ⟦∆⟧, and ρ ∈ 𝒱⟦T⟧δ then @ρ ⊐ @aδ" | `vC_outlives`, `vC_outlivesLe` (`Core/RelationFacts.lean:479,575`); `Paper`: `Fig16.LogRel.vDen_outlives` | PROVED AT σ=[] (`lifetimeSound_core`, checked; at `coreB`) |
| — | the bounds that keep B1, B2, B6, B7 from holding of a degenerate world | `WBoundB M` | — | Core's clauses, by unfolding | PROVED AT σ=[] (projections of checked results) |

```lean
/-- **B6**: every configuration the world reaches is a valid resource. -/
def ExclusiveB (M : BWorld) : Prop := ∀ fρ ps i, M.Fam fρ ps i → ResU.Valid fρ

/-- The nil slice's borrow structure is Core's: configurations, order, run end, payload stack. -/
def SliceShapeB (M : BWorld) : Prop :=
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ls ls' ρ ρ' π, M.Upd (ls, M.nil) (ls', M.nil) ρ ρ' π ↔ ResU.UpdV ρ π) ∧
  (∀ b, M.payStk b M.nil = M.nil)

/-- **B's bounds**: data values exactly data, every former's values bounded by their shapes and
eliminations, the empty configuration reached, the order a preorder, the nil slice Core's. -/
def WBoundB (M : BWorld) : Prop := SliceShapeB M ∧ ExtPre M ∧ FamEmpty M ∧ DataVals M ∧ RelLaws M

/-- The externs' contracts, read at the world (finding #7): each extern is persistent, and its
value is in the world's relation at the nil index from the empty resource. -/
def ContractsW (M : BWorld) : Ctx VTy → List Val → Prop
  | [], [] => True
  | ⟨T, true⟩ :: Γ, v :: γ => T.Persistent ∧ (∀ δ, M.val true T ([], M.nil) δ v PMap.empty) ∧ ContractsW M Γ γ
  | _, _ => False

/-- **Soundness (T1) with externs**: under every platform that keeps its protocol, with every extern
meeting its contract at the world, every run of a typed program at a div-free answer at a row the
platform answers is safe (B3) and terminates with the memory empty (B4); a program returning a loop
is safe on every prefix of its drive. -/
def Sound (J : OurTyping) (M : BWorld) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    RowLe S P.ops → ContractsW M Γ γ →
    (DivFree S A → ⟦J⟧.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
       SafeRuns P A (substAll γ e) ∧ Terminates P A (substAll γ e)) ∧
    (∀ B, A.Data → ⟦J⟧.at LifeCtx.empty Γ e (.comp (CTy.effOf S (.thunk (CTy.loopEff S A B)))) →
       SafeDrive P A (substAll γ e))

/-- **B's guarantees, at a typing system and a borrow world.** -/
def Guarantees (J : OurTyping) (M : BWorld) : Prop :=
  FL M ⟦J⟧ ∧ Adequate M ∧ Sound J M ∧ ReleasedOnceEvery J M ∧ ExclusiveB M ∧ LifetimeSound M J.out ∧
  WBoundB M
```

`⟦J⟧ : TypingJ` is the family reading of a typing system with open syntax (§4.2), so the library's
`FL`, `SafeRuns`, `Terminates`, `Final` and `Platform` are used as they are. At `Γ = []`,
`ContractsW M [] [] = True` and `Sound` is the library's `Soundness`.

**B at BoLo, by citation** (`Targets/B/Given.lean`): `B.Given := FL coreB tier1 ∧ AdequateRetAt
coreB Platform.none ∧ SoundRetAt tier1 Platform.none ∧ ExclusiveB coreB ∧ LifetimeSound coreB
OutJ.core ∧ WBoundB coreB`. It is PROVED: each conjunct is a checked result at `coreB`, the world
`coreW` extends, or a projection of one (`exclusiveB_core`, `wboundB_core`, to build). B5 at BoLo is
OPEN, on the machine lemma alone (§2.4). B5 is the one guarantee in B that is neither printed nor
given by citation. Finding #2 asks for a release statement with content in done, and B is where a
release guarantee belongs, so it is here, marked as ours, with its dependency stated (§2.4, §7 Q4).

### 2.3 The effect vocabulary B keeps, and what B does not contain

B's statements mention effect constructs in three places. Each is Core's machine, which is the
machine BoLo's guarantees are proved about. None is a requirement on an effect system (A), and none
is a rule for how an effect is read in the borrow world (I).

- **Runs.** `SafeRuns`, `Terminates`, `Final`, `PRun` range over runs of Core's `Step1`. Its `Prim`s
  include the kernel's effect primitives (`perform`, `raise`, `hnd`, `ubind`, `ccatch`, `cfin`) and
  `boundedFix`, and `adequacyD` is proved over exactly that machine. B states no handler semantics.
- **Types and rows.** `Sound` and `Adequate` quantify over closed programs at `CTy.effOf S A`, with
  `RowLe S P.ops` (the rows the platform answers), `DivFree S A` (`= A.Data`), and `CTy.loopEff`
  answers. These are Core's types, the ones `fundamentalC` covers, read as syntax. B states no row
  algebra, no typing rule for effects and no continuation discipline: those are A's, through the
  instance.
- **Platforms.** `Sound` and `Adequate` quantify over Core's `Platform`s. A platform is the
  machine's outside: a state-access comodel answering Core operations at the top, with
  `Platform.Respects` a protocol on Core's rows. BoLo's guarantees are stated under every platform as
  Core states them under every allocator. The correspondence with A's `Runner` is the Instance's
  (§4.1).

**What B does not contain.**

- **No interaction rule.** How a row is read in the borrow world (`EffInterp`: the relation at
  `F_S` is W's runs through the row's protocol), what a stop owes its continuation (`share`,
  `ShareMono`), the stop condition (`Stop`), what suspensions hold (`held`), and adequacy at stops
  from every index (`AdequateEvery`): all of these are I's (§3.1). B's world has none of those
  fields, so B can state none of them.
- **No step-indexing statement.** Decision 7 is a property of the world's definition (§5.2).
- **Exclusivity and lifetimes have no program-level form.** The machine sees locations, not
  lifetimes or aliasing ("Aliasing-xor-mutation is an invariant of the model, not an observable
  property of a sequential run", notebook P1). B6 and B7 are stated at the world, and the world is
  bounded (`WBoundB`) so that they cannot hold vacuously. B6 is validity, which is the paper's
  statement. The typed invariant with what suspensions hold counted is the interaction's `Exclusive`
  (P10, §3.3), and it implies B6.

### 2.4 B5: exactly-once release with content (finding #2)

`ReleasedOnceAll J` (the library's conjunct of done) holds at every typing system (`releasedOnceAll`,
checked). Its premises are `NoReuse`, the empty memory at the start and `Final` at the end. On any
run of this machine a location alternates between allocated and free (an allocation takes a free
location, `free` needs an allocated one), so those premises already give its conclusion. It is a
lemma about runs. It stays in `Targets/B/Release.lean` under its own name, beside the occupancy
lemmas (`releasedOnce_of_ends` and the rest) that B5's proof uses, and leaves done.

**The content that matters** is at-most-once *per allocation* on runs that reuse locations. A stale
reference to a released cell must not release (or read) the cell a later allocation put at the same
location. The machine cannot see provenance. A run that reuses no location can, since each allocation
there has its own location. So B5 says every run is the image of one that reuses nothing, under one
location map. A location's provenance is its preimage, the same at every step.

```lean
/-- `R` is the step-wise image of `F` under one location map `f`: injective on the locations each
configuration of `F` has allocated, affine on every array block it names (`ℓ + i ↦ f ℓ + i`), and
carrying terms (`Expr.rename`), heaps (`Heap.push`) and the platform state.  Dead locations (values
that name a released cell) may be merged with live ones; live ones may not.  `F` reuses nothing, so
one `f` serves the whole run. -/
def RunImage (F R : List (Conf P)) : Prop :=
  F.length = R.length ∧ ∃ f : Loc → Loc, ∀ k c c', F[k]? = some c → R[k]? = some c' →
    Set.InjOn f {ℓ | (c.μ ℓ).isSome} ∧ BlockAffineOn f c ∧
    c'.e = c.e.rename f ∧ c'.μ = Heap.push f c.μ ∧ c'.s = c.s

/-- **B5.**  Every complete run, under every allocator, of every program `Sound` covers is the image
of a complete run that reuses no location, and on that run every allocated cell is released exactly
once.  At-least-once is `Final`'s empty memory; at-most-once per allocation is the image. -/
def ReleasedOnceEvery (J : OurTyping) (M : BWorld) : Prop :=
  ∀ P, P.Respects → ∀ Γ γ S A e, DivFree S A → RowLe S P.ops →
    ⟦J⟧.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) → ContractsW M Γ γ →
    ∀ cs, PRun P (init P (substAll γ e) :: cs) → Final P A (lastOf cs) →
      ∃ fs, PRun P (init P (substAll γ e) :: fs) ∧ NoReuse (init P (substAll γ e) :: fs) ∧
        ReleasedOnce (init P (substAll γ e) :: fs) ∧
        RunImage (init P (substAll γ e) :: fs) (init P (substAll γ e) :: cs)

/-- **The machine lemma** (generic, no typing): a run of a program none of whose runs gets stuck is
the image of a run that picks a never-used location at every allocation. -/
def ReuseUnobservable : Prop :=
  ∀ P e cs, PRun P (init P e :: cs) → (∀ c, PSteps P (init P e) c → ¬ Stuck P c) →
    ∃ fs, PRun P (init P e :: fs) ∧ NoReuse (init P e :: fs) ∧ RunImage (init P e :: fs) (init P e :: cs)
```

**Why it has content.** B5 fails at a typing system that types a stale free (`staleFree`, §6.3):
under reuse the run ends empty, and its non-reusing image has no step at the second free. So it is
not a tautology. Its typing content is B3 and B4. Its machine content is `ReuseUnobservable`.

**What its proof needs, and what that picks (OQ-43).** `ReuseUnobservable` is TwoRun's two-run fact
(`experiments/TwoRun`): every run follows a fresh run along a function. TwoRun proves it for runs
with no array step and no capture step: `head_rename` (`TwoRun/Rename.lean:359`), `run_sim`
(`TwoRun/Sim.lean:253`), `fresh_run_image` (`TwoRun/Sim.lean:274`). Its README says the array steps
(`tab`, `idx`, `split`, `drop`) compute locations (`ℓ + i`). The extension to them "under a renaming
of blocks rather than of single locations, I have not derived and have not checked". `head_rename`
also lacks the capture, `count`, `countTry` and `boundedFix` steps. TwoRun does not build on main
(BRIEF §4). That is OQ-43 ("Extend `head_rename` and leave arrays unproved (a), prove block
renamings (b), or route array laws through a binary FP (c)?"), classed "CONSTRAINED by U22 (binary
half optional); EVIDENCED. Deferrable", with (b) "a real unknown, but optional" (05b).

**B5's statement picks no OQ-43 option.** Its proof does depend on OQ-43. It needs (a)'s mechanical
extension of `head_rename`, and, for programs with array steps, (b) (block renamings, which is why
`RunImage` asks `BlockAffineOn`) or (c) (a binary FP). Under (a) alone, B5 stays open for programs
with array steps, and done is not met. So B5 in done makes OQ-43 non-deferrable, at (b) or (c). That
is the user's to accept: §7 Q4. The builder builds `ReuseUnobservable` from `run_sim` and
`fresh_run_image` once TwoRun is repaired (TwoRun lives outside `experiments/Targets`), not from
scratch. **Not taken:** a statement on a
provenance-instrumented machine, each allocation carrying an id, would make at-most-once per id
direct and keep OQ-43 out of B5's proof. But it needs a second machine over tagged locations, a twin
of `Step1` (BRIEF §10: no twin constants or side mechanisms), and its adequacy would have to be
re-proved over that machine or reached through the same renaming. §7 Q4 offers it.

**Why not `ReleasedOnceReuse`** (the library's statement beside done, which finding #2 suggests
moving in). Its sibling run is related at every step by one **bijection** applied to the whole
configuration. A configuration can hold a value naming a released location: a closure loaded through
an `Imm` borrow is viewed at `Unk` ([CONF] Fig. 8: "Imm 'b (T1 ⊸ T2) ≜ Unk"; "Unk, for which the only
operation that is defined is forget"), holds nothing (`𝒱⟦Unk⟧ = emp`), and outlives every lifetime.
If the location it names is reused, no bijection relates the two configurations at that step. I have
not checked whether a typed program can hold such a value across a reuse, and I claim no obstruction.
`RunImage` asks injectivity on the live heap only, so B5 does not depend on the answer.
`ReleasedOnceReuse` is retired in favour of B5 (§4.5).

**P8.a is B5 at the runs that capture a continuation.** The cells a cancelled continuation holds are
released once: the memory is empty at the end (B4), and no release is stale (B5).

---

## 3. The interaction

The interaction is the only place A and B meet. It consists of the extension of B's world by what
effects add (the device's carrier), the rules for how suspensions, handlers and drops behave in it
(I1–I5), the side conditions, the routes from B to A's properties, and the combined theorem.

### 3.1 The world, extended: the proof device, carried over

The fields of `DESIGN.md` §1.3's `SemWorld` and `FIX-RUN-END.md` are unchanged. They are split
between B's world and I's extension of it:

```lean
namespace I

/-- **The semantic world**: a borrow world, with what the suspended computations at an index hold
(OQ-9 lives here), the stop condition (Core's is R-T1), and what a stop at a resuming operation owes
its continuation (Core's `contShare`; OQ-8 lives here). -/
structure SemWorld extends B.BWorld where
  held  : Idx Stk → List FrameRec × List SRec
  Stop  : List FrameRec × Idx Stk → List FrameRec × Idx Stk → Expr → Prop
  share : OpTabI (Idx Stk) → OpEntI (Idx Stk) → UInt32 → Idx Stk → Kont → (Idx Stk → Expr → WProp) → WProp

@[reducible] def coreW : SemWorld := { B.coreB with held := …, Stop := …, share := … }   -- as at `938d280`
```

Everything else moves to `Targets/I/World.lean` unchanged: `wpGW` (ending every run under `M.Stop`
and `M.Upd`), `ewpW`, `opTabW`, `cancelTabW`, `rowTabW`, `OpTabI`, `OpEntI`, `TableI`, and the
transports (`wpGW_core`, `ewpW_core`, …). The run-end laws (`UpdRefl`, `UpdOwn`, `UpdSeq`,
`UpdReclaim`, `UpdFrame`, `UpdOutlives`, `UpdLendBack`) stay beside done, and
`Restricted/RunEnd.lean` moves in full to `Targets/I/RunEnd.lean`. That file holds AT02's ends
(`at02_held_end`, `at02_unfolded_end`, `at02_held_end_core`, `at02_imm_end`), the witness worlds
`leakW` and `carryW`, and the printed forms' exclusions (`not_updOutlives_of_opened`,
`not_updMutBack_of_closed`). Every existing proof reads its fields by name (`M.Fam`, `M.Upd`,
`M.held`), and `extends` keeps those names.

**I's bounds (in done).**

```lean
/-- The nil slice's stop and holdings are Core's. -/
def SliceShapeI (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔
     (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls))

/-- **How effects are read in the borrow world**: an unr-free row through its protocol
(`EffInterp`), the share monotone in what it owes (`ShareMono`), every run from every configuration
the world reaches continuing to a value or a stop of the row (`AdequateEvery`), the nil slice's stop
and holdings Core's. -/
def WBoundI (M : SemWorld) : Prop := SliceShapeI M ∧ EffInterp M ∧ ShareMono M ∧ AdequateEvery M
```

`SliceShape M ↔ SliceShapeB M.toBWorld ∧ SliceShapeI M`, and `WLaws M ↔ WBoundB M.toBWorld ∧
WBoundI M ∧ Mono M` (both to build, by reordering). Together the two bounds hold W's relation from
above by W's runs at every index and type former, and pin the nil slice to Core's structure.

### 3.2 I1–I5: what done holds, and what is device

| | statement | in done | device (beside done) | beside / named-only |
|---|---|---|---|---|
| **I1** a suspension is a value of the resource world | the share a stop owes, closed by the handler, is a value of `kTy` | `I1Prog J` (stored suspensions typed and safe: `storeCancel`, `at17`), a corollary of `Pins` at `.any` and `Sound` | `I1 M` (W-form) | — |
| **I2** capture and resume preserve the invariant | every configuration W's runs reach arises in `TW`, the frames suspensions hold counted, so `TW.inv` holds of it | **`Arises M`**; `I2Prog J` (AT02, AT04, AT12 typed and safe), a corollary at `.any`; the spanning rules in `Pins` | `StopVisible`, `ShareResume`, `FramesW` (6.64/6.65 at W in the printed shape), `SpanBorrows` (redundant: FL with the spanning rules gives it) | `FreezeBinder` (available, beside done); `NotVDenNaturalArises` (its first check, OPEN) |
| **I3** drop finalises exactly once | a cancel runs every frozen finaliser once, LIFO, and releases what the continuation holds | A-CAN `Cancellation` at the instance; B5 at the runs that cancel | `ShareCancel` (I3.a at W, with its closing clause) | `CancelCloses` (named-only, OQ-57: "ends every lend it holds") |
| **I4** answering effects are borrows | an answering handler lends its state as `Mut 'h S`; an operation is a `withswap` on it | `I4a ⟦J⟧ Adm c` in `Pins` | — | `I4Typing` (OQ-1); `I4c` (binary) |
| **I5** the capture laws | β, η, hiding | A-SEM's deep resume (β, operationally) | `I5 M`: `I5beta` (generic, checked), `AntiFrameW` ([TR] 6.66 at W), `FrameW` | η and hiding as equations are A₂ (`Laws`) |

**I2 as preservation.** `Arises M` is "every wp run ends in a `TW` world plus `TW.inv`", extended to
W: every configuration in `M.Fam` is a tagged `TW` world over the visible frames and the held ones. It
reads `M.Fam` and `M.held`, which carry OQ-9 as fields, and asserts nothing about where lends are
kept. With `TW.inv` and `TW.valid` it gives P10's `Exclusive` (`exclusive_of_arises`, to build), and
so B6.

### 3.3 The side conditions

| | statement | in done | device / beside |
|---|---|---|---|
| **P9** lifetime soundness | 6.60 at every type, suspension types included, every index | B7 `LifetimeSound M J.out`, at the typing system's own outlives judgements (OQ-28) | — |
| **P10** exclusivity across the handler | every configuration W reaches satisfies the aliasing invariant, counting what suspensions hold | **`Exclusive M`** (I, in `Interface`), which `Arises M` gives by `TW.inv` and `TW.valid`; it implies B6 | — |
| **P14** well-bracketing conservativity | Core's proofs survive where callbacks perform only `{fn, abort}` operations | **`EmbedsNil M`**: Core's relation at row-abortive types embeds into W at σ = [] itself | `ConservativeWB M` (the embedding at every `M.Ext`-future index: needs `Mono`, so it is device); `Conservative M` (every type, beside done); `WBCore` (Core-only, checked, a companion of tier 1) |

```lean
/-- **P14.b at the nil index**: a value Core proves valid at a row-abortive type is valid in W at
the same record list and the empty lend stack. -/
def EmbedsNil (M : SemWorld) : Prop :=
  ∀ b A ls δ v ρ, A.AbortRows → vCE none b A ls δ v ρ → M.val b A (ls, M.nil) δ v ρ

/-- **P10**: every configuration W reaches is valid and satisfies the typed invariant, counting the
frames and records suspensions hold. -/
def Exclusive (M : SemWorld) : Prop :=
  ∀ fρ ps i, M.Fam fρ ps i → ResU.Valid fρ ∧
    ∃ ps₀ ls₀, (∀ p, p ∈ ps₀ ↔ p ∈ ps ∨ p ∈ (M.held i).1) ∧
      (∀ x, x ∈ ls₀ ↔ x ∈ i.1 ∨ x ∈ (M.held i).2) ∧ TI fρ ps₀ (rsOf ls₀)
```

`ConservativeWB M` is `EmbedsNil M` carried to every `M.Ext`-future, which `Mono` gives. Under OQ-8's
placement at the binder clauses, a value is re-quantified where it is used, so the nil-index form is
what both placements share. Done therefore holds less than the old done at a Core-proved value used
inside a lend that spans a stop: §4.5 lists the change. Core's relation stays pinned by hash
(`Targets/Audit.lean`), so neither form can be met by redefining Core.

### 3.4 The device: the printed route, beside done

```lean
/-- The lemmas FL's effect cases consume along the printed route, at a world with Core's placement
of the future-world quantifier.  A route to done, not a part of it. -/
def Device (J : OurTyping) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  Mono M ∧ ShareResume M ∧ ShareCancel M ∧ StopVisible M ∧ FramesW M c ∧
  SpanBorrows M J.out Adm c ∧ I1 M ∧ I5 M ∧ HandleCompat M ∧ RedLaws M ∧ ConservativeWB M
```

Plus the run-end laws (`UpdSeq`, `UpdReclaim` for `AdequateOfLaws`; `UpdRefl`, `UpdOwn`, `UpdFrame`,
`UpdOutlives`, `UpdLendBack` for FL's printed route), all as before. `Device` at Core (the typing
`tier1NU`, the world `coreW`, `admClosedOp`, `.abortive`) is PROVED AT A RESTRICTION from checked
results (`mono_core`, `shareResume_core`, `i3_core`, `stopVisible_core`, `framesW_core_abortive`,
`spanBorrows_core_abortive`, `i1_core`, `i5_core`, `handleCompat_core`, `redLaws_core`,
`conservativeWB_core`).

### 3.5 The combined theorem, done, tier 1

```lean
namespace I

/-- The interaction's option-neutral rules at the world: how effects are read in it, I2 as
preservation, exclusivity across the handler, and P14 at σ = []. -/
def Interface (M : SemWorld) : Prop := WBoundI M ∧ Arises M ∧ Exclusive M ∧ EmbedsNil M

/-- The spanning rules at the rows of class `c`: each of `SpanRules`' six rules with its row also of
class `c` (`c.Admits (S η)`).  `RowSpan` already excludes resuming `unr` operations, so
`SpanRulesAt J Adm .any ↔ Tier2Pinned ⟦J⟧ Adm` (to build). -/
def SpanRulesAt (J : OurTyping) (Adm : OpAdm) (c : RowClass) : Prop := …

/-- What the composite's typing must contain: Core's unr-free rules over open rows, the outlives
judgements extending Core's, the admissibility containing R-CLOSEDOP, the spanning rules at the
class, the tier-2 acceptance programs at `.any`, and answering effects typed as borrows. -/
def Pins (J : OurTyping) (Adm : OpAdm) (c : RowClass) : Prop :=
  ExtendsNUo J ∧ OutExtends J.out ∧ AdmExtends Adm ∧ SpanRulesAt J Adm c ∧
  (c = .any → AcceptsTier2 ⟦J⟧) ∧ I4a ⟦J⟧ Adm c

def Combined (J : OurTyping) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  A.Props₁ (ourInst J) ∧ B.Guarantees J M.toBWorld ∧ Interface M ∧ Pins J Adm c
```

**Done.** `theorem combined_W : Combined J₂ W Adm .any` at the kernel's named tier-2 typing system
`J₂` and a named world `W`, with `audit_W` and `audit_J₂` passing, at the `Adm` OQ-56 settles. OPEN.
`∃ J M, Combined J M Adm .any` follows from done and is not done: an existential has no definition to
audit.

**"Nothing breaks the borrow calculus"** is the conjunct `B.Guarantees J₂ W.toBWorld`: BoLo's
guarantees hold in the composite, at the composite's typing and world. **Its counterpart, "nothing
breaks the effect algebra"**, is `A.Props₁ (ourInst J₂)`: the composite is an admissible effect system
with A's first-pass properties. A₂, A₃ and P8.b are the rest of the counterpart, beside the first
pass. **Externs** enter as a hypothesis, never as a proof obligation: `Sound` and B5 assume
`ContractsW M Γ γ` (§5.3).

**Tier 1.** `Tier1 := Combined J₁ coreW admClosedOp .abortive`, with `audit_J₁` passing. `J₁` is
Core's unr-free rules over open rows with a rank-1 row `∀` (§4.2), and lends span abortive rows only.
It is literally done's definition at another typing system and class. `WBCore` (checked, `wbCore`) is
a Core-only companion result, not a conjunct. OPEN. What it needs beyond checked results:

1. **`J₁`** (to build): the open-row syntax with `.rall`, the rules, `ExtendsNUo J₁` (from
   `extendsNU_tier1NU`), and the denotation lemma. Together these give `FL coreB ⟦J₁⟧` from
   `fl_core_tier1NU` (§4.2).
2. **A at Core**, the requirements:
   - `MachShape`: `ConfLaws` and `NoIO` by definition; `KontLaws` by `Kont` lemmas; `Congr` from
     `Step1`'s definition and `plug_decomp`.
   - `RowAlgebra` and `RowSig` at `orowAlg`: laws and safety checked; `VarLaws` and `RowSig` to build.
   - `TySubst`.
   - `RowPoly` at `J₁`: T_TAbs, T_TApp, the substitution lemma on `J₁` derivations, and
     `AccRowPoly`'s program and its run.
   - `EffRules`: Core's rules at `J₁`, with `[handle]` at handler values by substitution.
   - `HandlerSem` with `K₀`: the `Head` steps and `Congr`, with `kappa`'s administrative steps for
     the deep resume and the cancel entry.
   - `ContDiscipline`: `Structural` by inversion at the unit value and the self-pair (`unitI` with
     `Ctx.DeadP`; `tensorI` and `var` with `Ctx.SplitP.dup`); dereliction is `bangE`; `kTy` is a
     thunk, so not persistent; no κ eliminated twice, since the split cannot copy a κ; resume and
     affine-cancel typing from `[handle]`'s clause types; a linear κ's cancel only at `⊤`.
   - `DataDiv`: `VTy.Data` facts, `DivFree` by definition, and `next`/`close` typing from Core's `ν`
     rules.
   - `Acceptance`: the event sequences of existing programs (§4.4), plus three to build — a linear
     program that performs twice under one handler, a program returning a loop that the runtime
     drives, and a loop that never ends.
3. **A₁ at Core**, the properties:
   - `EffSafe (ourInst J₁)`: the bridge from Core's `EffSafe ⟦J₁⟧`, which `effSafeOfFL` (I/Routes,
     restated over `FamEmpty` and `AdequateEvery`) gives from `FL coreB ⟦J₁⟧` and
     `adequateEvery_core`.
   - `Safety (ourInst J₁)`: the runner–platform correspondence (§4.1) and B's `Sound` under every
     platform, which needs `Adequate coreB` at platforms with operations and for drives (OPEN, as
     before).
   - `NoIntercept (ourInst J₁)`: Core's syntactic `NoInterception ⟦J₁⟧` (to build, by
     `noInterception_tier1`'s induction, checked at `tier1`, over `J₁`'s rules), and the bridge from
     the shape of Core's `CancelRun` to `CancelTrace`.
   - `UnwindOrder (ourInst J₁)`: `FinaliserOrder` at Core (OPEN, as before) and the bridge from
     Core's `UnwindRun` to `UnwindTrace`.
   - `HandlerRed (ourInst J₁)`: the A form of unique decomposition and determinism of pure head steps
     (`plug_cmp`, `plug_decomp`, `head_det_eff`).
4. **B at `coreB`**: `Adequate coreB` (above), B5 (`ReuseUnobservable`, on OQ-43, §2.4),
   `exclusiveB_core` and `wboundB_core` (projections).
5. **I at `coreW`**: `EmbedsNil coreW` (the nil index of `conservativeWB_core`, a projection); the
   rest checked (`sliceShape_core`, `effInterp_core`, `shareMono_core`, `adequateEvery_core`,
   `arises_core`, `exclusive_core`).
6. **`Pins J₁ admClosedOp .abortive`**:
   - `SpanRulesAt` from Core's `*U` constants and `rowSpan_abortive_iff_unwind`.
   - `I4a ⟦J₁⟧ admClosedOp .abortive`: `i4a_tier1` builds `CDerives` (`tier1`) derivations, not
     `J₁` ones. To build: its borrow forms are unr-free, so `J₁`'s copy of Core's rules types them.

**Corollaries** (`Targets/I/Combined.lean`):

- `combined_prog`: the program-level conjuncts, which do not mention the world.
- `i1Prog_of_combined : Combined J M Adm .any → I1Prog ⟦J⟧`.
- `i2Prog_of_combined : Combined J M Adm .any → I2Prog ⟦J⟧`.
- `p8a_of_combined` (B5 at the runs that capture).
- `effSafe_of_combined` (a projection of `A.Props₁`).
- `exclusiveB_of_combined`.
- `soundnessContractsAR_of_combined : Combined J M Adm c → SoundnessContractsAR ⟦J⟧`, from `Sound`,
  `EmbedsNil` and `contractsW_of_meets` (§5.3): done states the SPEC externs' guarantee at Core's
  fixed contract.

### 3.6 OQ-8 and OQ-9 stay unpicked (finding #5)

Each W-level conjunct of done, read under both placements of OQ-8's future-world quantifier (at
`U`/`share`/`KapRel`, Core's; at the binder clauses, GhostEnd's `vRLk`) and every option of OQ-9 ((a)
frames carried open in σ, the cell kept or unfolded; (b) ghost-end; (c) R-T1):

| conjunct of done | reads `M.Ext`-futures? | asserts a printed frame shape at resuming tables? | why neutral |
|---|---|---|---|
| `FL M ⟦J⟧` (B1) | no: `SemW` quantifies every index | no | a statement about the world's relation, whatever its placement |
| `Adequate M` (B2) | no: closed programs at `([], M.nil)` | no | bounds `Upd` at a reachable leak only (FIX-RUN-END §3) |
| `ExclusiveB M` (B6), `Arises M`, `Exclusive M` (I2, P10) | no | no | read `Fam` and `held`, where OQ-9 lives as fields |
| `LifetimeSound M J.out` (B7) | no | no | every index, every type, both modes |
| `WBoundB M` | `ExtPre` asks a preorder, which both placements have; `SliceShapeB`'s `Ext` pin is between nil indices; `RelElim` is at the same index | no | `Mono` is removed |
| `WBoundI M` | no | no | `ShareMono` is monotonicity in what the share owes, not in the index; `EffInterp` reads the share as a field; `SliceShapeI` is at the nil index |
| `EmbedsNil M` | no: the nil index itself | no | the future-index form needs `Mono`, so it is device |
| `ContractsW M Γ γ` (a hypothesis) | no: the nil index | no | — |

The conjuncts that fixed a placement or an OQ-9 shape are all device. `Mono` excludes a binder-clause
placement unless `EwpMono` holds, which nothing proves. `ShareResume` and `ShareCancel` place the
quantifier in the share. `FramesW` in the printed shape can decide OQ-9 for (a). `StopVisible` fixes
where a carried 6.64 frame is accounted (`AGREE.md` minor finding). Done can be met by a world built
under any option, `coreW` itself included if the ghost-end route (OQ-9 (b), `GFPA`) proves FL for
`J₂`. `SliceShapeB`'s `Upd` pin constrains OQ-44, not OQ-8 or OQ-9, and stays as `AGREE.md` decision
10 leaves it.

### 3.7 Beside done, and named-only

- **Beside done (stated, OPEN):**
  - `Device` (the printed route).
  - `FreezeBinder`, `BinderMachine`, and `CombinedBinder := Combined ∧ FreezeBinder W act ∧
    BinderMachine`.
  - `Conservative W` (every type) and `ConservativeWB W` (futures).
  - `SoundnessContracts J`: externs whose contracts are stated at Core's relation, at any persistent
    type. Its route is through `Conservative` (`soundnessContractsOfFL`, checked, in I/Routes), an
    optional bridge (§5.3).
  - P8.b `P8b` (A, OQ-50), `AdequateOfLaws`, `I4Typing`, and the run-end laws.
- **Named-only:** `CancelCloses` (OQ-57); T3's proof device `AbstractionOfFL₂` (a binary world).
- **Out of the first pass:** A₂ (`Laws`, `EffDepLaws`, `Abstraction`), A₃ (`LoweringCorrect`,
  `Erased`, `ZeroCost`), `I4c`, the AT-rejects.

---

## 4. The Instance: our calculus as one instance of A

The Instance imports A, `Core` and base, and nothing of B or I. Its results are about our calculus
as an effect system. Where one of A's properties at our instance needs a borrow fact (FL, adequacy),
the route is in `I/Routes.lean` (§4.3).

### 4.1 `ourInst`: A's fields from Core

`OurTyping` carries its effect context: `J.Ξ : EffCtx`, with no resuming `unr` operation
(`Ξ.NU`, decision 63). Every row in a derivable judgement is well formed at `J.Ξ` (`orowAlg`'s
`WF`), so one global `sig = J.Ξ` agrees with Core's inline signatures: an operation `Row.find` finds
in such a row has `J.Ξ`'s arity and qualifier.

| A field | our calculus | note |
|---|---|---|
| `EA` | `orowAlg J.Ξ`, with `var ρ := ⟨[], some ρ⟩` (`VarLaws` by unfolding `subst`); `closedRowAlg Ξ` for Core today (`Var := Empty`) | the algebra moves Core-free to `Targets/A/EffAlg.lean`; its instances to `Instance/Rows.lean` |
| `sig`, `has` | `sig n := J.Ξ n.1`, each `(q, A, B)` classed abortive iff `B = 0 ∧ q ≠ lin`, linear iff `q = lin`, affine otherwise; `has ε n i := i < 2 ^ 32 ∧ (Row.find ε.ops n.1 i.toUInt32).isSome` | Core's per-operation lookup; the bound keeps `UInt32` from wrapping (`Lab` already bounds a signature's length by `2 ^ 32`) |
| `Ty`, `CTy` | `J`'s open-row syntax `OVTy`, `OCTy` (§4.2) | |
| `UnitT`, `Tensor`, `Sum`, `U`, `Bang`, `kTy` | `.unit`, `.tensor`, `.sum`, `.thunk`, `.bang`, Core's `kTy S R q B` | SPEC §19's `K_i` |
| `F`, `Arr`, `Loop`, `All` | `CTy.effOf`, `.arr`, `CTy.loopEff`, `.rall` (`J₁`'s row `∀`) | |
| `Drop`, `Pers` | `VTy.Persistent`, both | Core weakens only at persistent slots (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`) and contracts only there (`Ctx.SplitP.dup`). `VTy.Drop` (no owned cell) is Core's side condition on what a cancel or unwind abandons (`[let]`, `[raise]`), an instance fact B4 reads |
| `Data`, `DivFree` | `VTy.Data`; `DivFree C := ∃ S A, C = CTy.effOf S A ∧ A.Data` | base's `DivFree`, decision 35 |
| `substTy`, `substCTy`, `substC` | `orowAlg.subst` at every row of a type | |
| `Term`, `Val`, `Hnd`, `Kont` | `Expr`, `Val`, `Val × Val` (`h_ret`, the clause tuple), `Kont` | |
| `val`, `ret`, `seqT`, `letv`, `app`, `var0`, `subst0` | `.val`, `.val`, `(λ_. N) M` (`bind` under a dead binder), `(λ. M) V`, `.app` (in Core's A-normal form, the argument let-bound), `.var 0`, `Expr.subst 0` | Core's thunk of an arrow is the λ itself (`thunkV`), so `app` needs no force |
| `unitV`, `pair`, `inl`, `inr` | `Val.unit`, `Val.pair`, `Val.inj₁`, `Val.inj₂` | |
| `genV`, `instV` | `genV ρ v := v`, `instV v ε := v` | Curry-style, as Core's lifetime `∀` (`allI`, `allE`) |
| `next`, `close` | `nextE l = l (inj₁ ())`, `l (inj₂ ())` | |
| `perform`, `raise`, `handle`, `retC`, `opC` | `performE (opArgE …)`, `raiseE`, `hndE (hndVal n hr hs)`, `hr`, the `i`-th clause of `hs` (`clauseAt`) | |
| `capture`, `resume`, `cancel`, `cancelOf` | `kappa n H K`; `κ (inj₁ ()) w`; `κ (inj₂ ())`; `cancelOf n H K` | |
| `thenT`, `thenF`, `handleF`, `kcomp`, `hole`, `plug` | `ubindE (λx.N, D) M`; its frame; the `hnd` frame; `Kont.comp`; `.hole`; `Kont.plug` | |
| `catches`, `unwindClear`, `fins` | `Kont.HasHnd`; no `ubind`, `cfin` or `ccatch` frame; `Kont.fins` | |
| `Conf`, `init`, `term`, `setT` | `Heap × Expr`; `(emptyMem, e)`; `.2`; `(·.1, t)` | |
| `step` | `Step1` (every allocator), labelled by its head step: `catch` at `hop`/`hunwind`, `fire D` at `ufin`/`ufinC`, `finEnd none` at `cfret`, `finEnd (some (m, j, w))` at `cferr`, `tau` otherwise | a definition over Core's relations, no Core edit |
| `RKind`, `admits` | `RowCon`; `Θ ⊢ ε : k`: `ε`'s operations admitted by `k`, its tail a variable of `Θ` whose constraint `k` contains | |
| `Ctx`, `emp`, `ext`, `split`, `der` | `LifeCtx × OCtx`; …; `Ctx.SplitP`; `J.der` | |
| `Runner` | `runnerOf`, `platformOf` (below) | |
| `Lowering` (A₃) | `Target` = the flat IR after `Backend.closTypesOfExpr`, its runs and `FState.allocs`/`FState.indirect` as events; references for the answering and abortive classes | named-only until the backend exposes a fuel-parametric stage interpreter |

**Runner and platform** (`Instance/Core.lean`, to build). `runnerOf P := ⟨⟨P.ops, none⟩, P.St, P.s₀,
fun s n i v => P.co s n.1 i.toUInt32 v⟩`, and `platformOf R` back. `respects_runnerOf : P.Respects →
(runnerOf P).Respects`, through `typed_data_iff : A.Data → (J derives v : A ↔ DataVal A v)`.
`rstep_runnerOf`: A's `RStep (runnerOf P)` is `PStep P` on configurations. A's `Safety` at our
instance is then B's `Sound` read through them (`safety_of_sound`, I/Routes).

**Core's `unr` fragment** stays a Core fact outside the instance. `tier1` (with `unr`) keeps its
checked results (`fl_core_tier1`, `effSafe_tier1`, `noInterception_tier1`), and the instance reads
`CDerivesNU`. Nothing in A mentions it.

### 4.2 Core today, `J₁`, `J₂`

- **Core today is the tier-1 instance at a restriction.** It is `ourInst` at `closedRowAlg Ξ` and the
  typing `tier1NU` at the empty row context, at the platform with no operation. It fails A-ROW: its
  algebra has no row variable and its types no `∀ρ`. That is current state, not design (decision 62).
  Every other requirement is the tier-1 list of §3.5 at closed rows. `closedCore_of` (§4.5) records
  them as `Props₁₀`, which is `Props₁` with `RowPoly` dropped.
- **`J₁`** (to build, `Instance/Typing.lean`). Core's unr-free rules over the open-row syntax
  `OVTy`/`OCTy`. Those are Core's types with a row variable allowed at the tail of a row, and one more
  former, `.rall ρ k C`. `.rall` is J₁'s rank-1 row `∀`: `J₁` admits a `.rall` type only as the type
  of a value it generalises and of a let-bound variable. T_TAbs and T_TApp are A-ROW's, with
  `genV`/`instV` erased.
  - **The family reading** `⟦J₁⟧ : TypingJ` maps an open judgement to its closed instances by
    `orowRF.den`.
  - **The denotation lemma** is `J₁ Θ Γ e j → tier1NU Θ ⟦Γ⟧ (inline e) ⟦j⟧`. `inline` substitutes each
    let-bound generic value at its uses: decision 57's "Instances per assignment of names are typing
    artefacts", and decision 8's monomorphisation. `RowLink orowRF` (checked) is its row half.
  - **FL.** `FL coreB ⟦J₁⟧` follows from `fl_core_tier1NU` with one more fact: the relation is closed
    under β-expansion at a `let` of a value, in any context. `let f = V in M` steps to `M[V/f]` by a
    pure head step, and a value under a λ is read at each argument.
  - **Pins.** `ExtendsNUo` (the pin over open syntax) replaces `ExtendsNU`'s family form, which stays
    as the instance reading's closure (`rulesClosed_tier1NU`).
- **`J₂`**: `J₁` with the spanning rules at class `.any` (`SpanRulesAt`, OQ-56's `Adm`). It is the
  kernel's tier-2 judgement, a named definition when the kernel adopts it (SPEC entry). Whether `J₂`'s
  row `∀` is rank-1 or rank-n is OQ-13's remaining question (§7 Q2). At rank n, `FL` for `J₂` needs a
  relation clause for `∀ρ`, since inlining no longer applies.

### 4.3 Optional borrow-derived routes (never requirements)

"There might be a way to get some effect properties we want by leaning on borrow properties but it's
not necessary." (the user, 2026-10-05). They are recorded here. Any Lean for them is in
`I/Routes.lean`, because there A and B meet.

| A property | borrow-derived route | evidence | status |
|---|---|---|---|
| P2 effect safety, for answering effects | handlers as lends: an answering handler lends `Mut 'h S`; an operation after the handler's extent would use a borrow past its lifetime, which 6.60 excludes | HandlersAsBorrows `effect_safety`, `handle_is_shift`, `translate_typed` [PAPER]; `I4a tier1` (checked, abortive rows) | optional realisation |
| no accidental handling (P12/T3's `Tunnel`) | lexical capabilities and second-class values: a callback's operations reach the capability it was handed | `experiments/SecondClass` `handleAt_compatC` [Core σ=[]]; decision 57's site freshness | optional realisation |
| P8.a, finalisation exactly once | linearity: a linear or affine κ is not `Drop`; leak freedom (B4) releases what a cancelled κ holds; B5 forbids a stale release | B4, B5; A-LIN | optional realisation of the resource half |
| capability escape (A4) | lifetimes: a stored continuation's bound is an outlives judgement (OQ-28) | 6.60, `Row.Unwind`, `ewp_box_end` | optional realisation |
| P2 and A1, at our instance | the semantic route: FL and adequacy, with the rows read through their protocol | `effSafeOfFL`, `safety_of_sound` | the route this design takes for the instance's proof, still not a requirement of A |

### 4.4 Every proved result, and its new home

This covers every theorem of the library at `938d280` (464 in `Targets/`) and the 17 of the
untracked verifier check `Targets/Checks/RunEnd.lean`. "Kept" means moved with its statement and
proof unchanged, and the definitions it reads unchanged or moved with it. "Kept at `coreB`" means the
statement's world is now `coreB`, which is `coreW.toBWorld` by `rfl`. §4.5 lists the restated ones.

| file at `938d280` | theorems | new home | change |
|---|---|---|---|
| `Defs/Typing.lean` | `ctxOutlivesJ_core`, `unwindJ_core`, `CDerivesNU.toCDerives` | `Base/Typing.lean` | kept |
| `Defs/Binder.lean` | `isVal_renameLoc` (and the proof-carrying `pmapRekey`, `Restrat.Emb.comp`) | `I/Binder.lean` (beside done) | kept |
| `Defs/Programs.lean` | `size_shift` (and `capPass`'s termination proof) | `Instance/Programs.lean` | kept |
| `Restricted/Acceptance.lean` | `at02_eval`, `at04_eval`, `at12_eval`, `at17_eval` | `Instance/Programs.lean` (the tier-2 acceptance programs) | kept |
| `Restricted/AcceptedT1.lean` | `flag_data`, `err_data` | `Base/Machine.lean` (data facts) | kept |
| | `acceptedT1_prog`, `acceptedT1_progC`, `acceptedT1_logOutside`, `acceptedT1_failOutside`, `acceptedT1_reborrowRaise`, `acceptedT1_nLogOutside`, `acceptedT1_nFailOutside`, `acceptedT1_logInBorrow`, `acceptedT1_tickProg`, `acceptedT1_takeProg`, `acceptedT1_storeCancel`, `acceptedT1_tickAnsProg` | `B/Programs.lean`: B3/B4 at Core's effect programs. The same programs are A's acceptance witnesses in `Instance/Programs.lean` (`takeProg`: deep, two catches by one handler; `progC`, `storeCancel`: affine, cancelled, finaliser fired; `failOutside`, `reborrowRaise`: raise caught), whose event sequences are to build | kept |
| `Restricted/Answering.lean` | `sIdx_zero_succ`, `sIdx_succ`, `sIdx_at_zero`, `var_shift`, `shift_closed0`, `forceE_var_shift`, `absurdE_shift`, `withPair_shift`, `hndTerm_shift`, `deadP_prepend`, `deadP_insert`, `splitP_prepend`, `splitP_insert`, `soloP_prepend`, `soloP_insert`, `live_insert`, `CDerives.insert_dead`, `deadP_selfSplit`, `deadP_splitKill`, `meetOfDomL_not_mentions`, `i4a_tier1` | `I/Answering.lean` (I4, with its helpers) | kept |
| `Restricted/Composition.lean` | `models_nil`, `gDenW_nil`, `semWC_of_FL`, `comp_of_FL`, `soundRetAt_of_FL`, `soundDriveAt_of_FL`, `soundnessOfFL`, `gDenW_of_meets` | `B/Composition.lean` (the routes from B1, B2 to `Sound`; they read only borrow fields) | kept |
| | `soundnessContractsOfFL`, `soundnessContractsOfFLWB` | `I/Routes.lean` (the extern routes, through I's `Conservative`/`ConservativeWB`) | kept; role changes (§5.3) |
| | `effSafeOfFL` | `I/Routes.lean` | **restated** (§4.5): over `FamEmpty M ∧ AdequateEvery M`, what its proof uses |
| `Restricted/CoreLaws.lean` | `dataB_rename`, `dataB_subst`, `data_inst`, `dataB_cl`, `dataB_noMut`, `vC_data_mp`, `vC_of_dataVal`, `vC_data` | `B/World.lean` (Core's relation at data types, read by `DataVals`) | kept |
| | `extPre_core`, `famEmpty_core`, `dataVals_core`, `relElim_core`, `relShape_core`, `relLaws_core` | `B/World.lean` (`WBoundB coreB`) | kept at `coreB` |
| | `sliceShape_core` | `I/World.lean`; its halves `sliceShapeB_core` (B) and `sliceShapeI_core` (I) to build, as projections | kept |
| | `effInterp_core`, `shareMono_core` | `I/World.lean` (`WBoundI coreW`) | kept |
| | `mono_core`, `stopVisible_core`, `shareResume_core`, `handleCompat_core`, `conservativeWB_core` | `I/Device.lean` | kept |
| | `fl_core_tier1`, `fl_core_tier1NU` | `B/Given.lean` (B1 at BoLo) | kept at `coreB` |
| | `lifetimeSound_core` | `B/Given.lean` (B7 at BoLo) | kept at `coreB` |
| | `exclusive_core` | `I/Interface.lean` (P10 at Core); `exclusiveB_core` (B6) to build as its validity half | kept |
| | `arises_core` | `I/Interface.lean` (I2's done part at Core) | kept |
| | `wbCore` | `I/Interface.lean` (P14.a, a companion of tier 1) | kept |
| | `conservative_core` | `I/Device.lean`, beside done (P14 at every type) | kept |
| | `admExtends_closedOp`, `rowSpan_abortive_iff_unwind` | `I/Interface.lean` (`Pins`) | kept |
| | `coreW_upd`, `wpGW_of_wpG_nil`, `updRefl_of_core`, `updOwn_of_core`, `updSeq_of_core`, `updReclaim_of_core`, `updFrame_of_core`, `updOutlives_of_core`, `updMutBack_of_core`, `updImmBack_of_core`, `updLendBack_of_core`, `updRefl_core`, `updOwn_core`, `updSeq_core`, `updReclaim_core`, `updFrame_core`, `updOutlives_core`, `updLendBack_core` | `I/World.lean` (the pin and the embedding) and `I/Device.lean` (the run-end laws): FIX-RUN-END carried over | kept |
| `Restricted/Corollaries.lean` | `typedSound_of_soundness` | `B/Composition.lean` | kept |
| | `nu_susp`, `d_performerNU`, `d_hrSNU`, `d_clSNU`, `d_storeCancelNU` | `Instance/Programs.lean` | kept |
| | `i2Prog_of_endState`, `i1Prog_of_endState`, `p8a_of_endState`, `endState_prog` | `I/Combined.lean` | **restated** (§4.5) |
| `Restricted/EffectSafety.lean` | `opPlug_no_step`, `stop_irreducible`, `arun_rest_irr` | `Base/Machine.lean` (a stop is irreducible) | kept |
| | `adequateEvery_core` | `I/World.lean` (`WBoundI coreW`) | kept |
| | `wlaws_core` | `I/Device.lean`, with `wboundB_core`, `wboundI_core` (to build, projections) for done | kept |
| | `effSafe_tier1` | `I/Routes.lean`: Core's P2 from FL (a route through B); the bridge to A's `EffSafe` at the restricted instance is `Instance/Core.lean`'s | kept |
| `Restricted/Handlers.lean` | `arun_first`, `wpGW_strip`, `plug_not_post`, `redLaws_of_mono`, `opTabW_mono_core`, `redLaws_core`, `p11_core` | `I/Device.lean` (P11's semantic form) | kept |
| `Restricted/Interface.lean` | `wpGW_mono`, `wpGW_step`, `ewpW_fold`, `ewpW_unfold`, `ewpW_step`, `mutView_core`, `tableI_down_mono`, `tableI_down_abortive`, `opTabW_core_empty`, `resuming_abortive_empty` | `I/World.lean` | kept |
| | `i5beta` | `I/Device.lean` (generic, every world); its operational twin is A-SEM's deep resume at Core (to build) | kept |
| | `i1_core`, `mutFrameUW_core`, `immFrameUW_core`, `mutFrameW_core_abortive`, `immFrameW_core_abortive`, `framesW_core_abortive`, `spanBorrows_core_abortive`, `i2_core_abortive`, `i3_core`, `antiFrameW_core`, `frameW_core`, `i5_core` | `I/Device.lean` (`I1`, `I2`, `I3`, `I5` keep their definitions, as device bundles) | kept |
| `Restricted/NoInterception.lean` | `okE_sound`, `okE_app`, `okE_lam`, `okE_travK`, `okE_travO`, `okE_travR`, `okE_selfV`, `okE_foldImmV`, `okE_foldOwnV`, `okE_foldReuseV`, `okE_mapV`, `okE_nodeV`, `okE_unfoldV`, `okE_forceE_var`, `okE_withPair`, `okE_withborUE`, `okE_of_derives`, `models_empty`, `noInterception_tier1` | `Instance/Core.lean`: Core's syntactic `NoInterception`, the instance's route to A-CAN's `NoIntercept` | kept |
| `Restricted/NonVacuity.lean` | `platformNone_respects`, `platformPing_respects` | `Base/Machine.lean` (two platforms that respect their protocol) | kept |
| | `rowSpan_failSig`, `rowSpan_fooSig`, `rowSpan_suspSig`, `resuming_fooSig`, `resuming_suspSig`, `d_forgetBody`, `i4a_witness`, `d_ansRun_witness` | `I/NonVacuity.lean` | kept |
| `Restricted/Release.lean` | `not_occ_vac`, `getElem?_pred`, `rise_between`, `fall_between`, `releasedOnce_of_ends`, `init_vacant`, `final_vacant`, `releasedOnceOfSound` | `B/Release.lean` (run lemmas; `releasedOnce_of_ends` is used by B5) | kept |
| | `releasedOnceAll` | `B/Release.lean`, documented as a tautology about runs | kept; leaves done (§5.1) |
| `Restricted/RowAlg.lean` | `rowEq_refl`, `rowEq_symm`, `rowEq_trans`, `rowEq_equiv`, `rowEq_append`, `rowEq_of_eq`, `find_nil`, `find_ofEff_zero`, `ofEff_wf`, `find_ofEff_other` | `Base/Rows.lean` (Core's rows) | kept |
| | `rowEq_lift_absorb`, `closedRowAlg_laws`, `closedRowAlg_safe`, `orow_comp_none`, `orow_comp_some`, `orow_ext`, `orowAlg_laws`, `orowAlg_safe`, `rowAlgSafe_orowRF`, `closedRowAlg_lawsSafe`, `orowRF_den`, `rowLink_orowRF` | `Instance/Rows.lean`: A-ROWS at the instance's two algebras, and the denotation's row half. `EffAlg` gains the field `var`, so the two instances gain one line each; the statements and proofs of these theorems are unchanged | kept |
| `Restricted/RunEnd.lean` | `wpGW_iff_runFrame`, `not_flatAt_empty`, `not_updV_empty_of_held`, `noOwn_mutCell`, `not_post_of_step`, `at02_eq`, `fooSig_lin`, `at02StopK_hasHnd`, `at02Body_run`, `at02Stop_irr`, `at02_runEnd`, `at02_runEnd_nil`, `wpGW_at02`, `held_arises`, `at02_held_end`, `flatAt_single_own`, `updV_empty_single_own`, `at02_unfolded_end`, `at02_held_end_core`, `not_sliceShape_of_updTop`, `upd2Reclaim_excludes_held`, `leakProg_step₁`, `leakProg_step₂`, `leakProg_run`, `no_pstep_val`, `not_adequateRetAt_of_leak`, `not_adequate_of_leak`, `effOf_inj`, `sliceShape_leakW`, `effInterp_leakW`, `dataVals_leakW`, `leakAt_leakW`, `not_adequate_leakW`, `not_updReclaim_leakW`, `delDom_empty`, `restrictDom_empty`, `empty_get_ne`, `empty_isSome`, `sliceShape_carryW`, `updReclaim_carryW`, `mutOnly_heldRes`, `upd_held_carryW`, `upd_close_carryW`, `compS_get_of_left_ne_imm`, `mut_ne_imm`, `carriedIn_of_fam`, `updRefl_carryW`, `compS_delDom`, `delDom_of_disjoint`, `own_not_carried`, `updOwn_carryW`, `updSeq_carryW`, `at02_held_end_carry`, `heldRes_get`, `fam_nil_held_carryW`, `not_close_from_nil_carryW`, `not_updOutlives_of_opened`, `not_updMutBack_of_closed`, `not_updOutlives_carryW`, `not_updLendBack_carryW`, `immRec_noDesc`, `admWf_flag`, `vShape_flag`, `immRes_hash`, `immRes_valid`, `own_arises`, `imm_arises`, `imm_tagged`, `immAt_immRes`, `not_updV_empty_immRes`, `at02_imm_end`, `not_stop_imm_of_stopVisible` | `I/RunEnd.lean` | kept |
| | `not_endState_of_leak` | `I/RunEnd.lean` | **restated** (§4.5) |
| `Restricted/Soundness.lean` | `every_alloc_of_wpTS`, `no_infinite_of_wpTS`, `row_nil_of_le`, `pstep_none`, `psteps_none`, `psteps_of_steps` | `B/Given.lean` (helpers of the citations) | kept |
| | `adequateRetAt_core_none`, `soundRetAt_tier1_none` | `B/Given.lean` (B2, B3, B4 at BoLo) | kept at `coreB` |
| | `acceptedT1_of_derives` | `B/Programs.lean` | kept |
| `Restricted/Transport.lean` | `idx_unit`, `ptoMutSW_core`, `ptoImmSW_core`, `gSepW_core`, `gDenW_core`, `semWC_core`, `semW₀_core`, `ptoMutSW_core_eq` | `B/World.lean` (read only borrow fields) | kept at `coreB` |
| | `wpGW_core`, `ewpW_core`, `opTabI_down_some`, `opTabW_core`, `opTabW_core_down`, `errOkW_core`, `cancelTabW_core`, `rowTabW_core`, `wpGW_core_eq`, `ewpW_core_eq` | `I/World.lean` | kept |
| `Restricted/Typing.lean` | the 48 `rc_*_tier1`, the 48 `rc_*_tier1NU`, `rulesClosed_tier1`, `rulesClosed_tier1NU`, `tier1Sub_tier1`, `tier1SubNU_tier1`, `extends_tier1`, `extendsNU_tier1`, `extendsNU_tier1NU`, `outExtends_core` | `Base/Typing.lean`: the family reading's closure; ingredients of `ExtendsNUo J₁` | kept |
| `Restricted/Unwind.lean` | `twoFrames_fins`, `raiseE_subst`, `raiseFin_steps`, `unitFin_steps`, `two_frame_steps`, `two_frame`, `one_frame` | `Instance/Core.lean`: Core's `UnwindRun` at two frames, A-ACC (d)'s witness and an instance of the bridge to `UnwindTrace` | kept |
| `Status.lean` | the 43 `status_*` | the new `Status.lean`, each re-pointed at its new home | kept, except the six restated in §4.5; `status_releasedOnceAll` re-labelled |
| `Checks/RunEnd.lean` (untracked) | 17 theorems: the verifier's check, stated against `wpGW` with `↭` fixed | not in the build; each already restated in `Restricted/RunEnd.lean` (FIX-RUN-END §8) | left untracked and unchanged |

**The definitions, and where they move.**

| at `938d280` | moves to |
|---|---|
| `Defs/Effects.lean` | `A/EffAlg.lean`: `EffAlg` (with `var` added), `EffAlg.SubstOK`, `EffAlg.Laws`, `EffAlg.Sub`, `EffAlg.Safe` (from `Statements/EffectSafety.lean`), `EffAlg.VarLaws` added. `Base/Rows.lean`: `RVar`, `Row.NU`, `RowClass`, `RowCon`, `RowCtx`, `RowEnv`, `RowCtx.Models`, `EffCtx`, `RowEq`, `Row.Has`, `ORow`, `Kont.fins`, `cancelOf`. `Instance/Rows.lean`: `orowAlg`, `closedRowAlg`, `RowForm`, `RowLink`, `orowRF` |
| `Defs/Typing.lean` | `Base/Typing.lean`, with `OVTy`, `OCTy`, `OurTyping` and `⟦·⟧` added (to build) |
| `Defs/Runs.lean` | `Base/Machine.lean`, with Core's `EffSafe`, `StopsIn`, and Core's `CancelRun`, `UnwindRun`, `CancelOrder`, `UnwindOrder`, `FinaliserOrder`, `NoInterception`, `Kont.NoCtl`, `Expr.HasPrim`, `Expr.HndNamesNZ` from `Statements/Interface.lean`; `PRun`, `Allocated`, `Released`, `NoReuse`, `ReleasedOnce` to `B/Release.lean` |
| `Defs/World.lean` | `B/World.lean`: `Idx`, `BWorld` (the borrow fields), `coreB`, `ptoMutSW`, `ptoImmSW`, `gSepW`, `gDenW`, `SemWC`, `SemW₀`, `SemW`. `I/World.lean`: `SemWorld extends BWorld` (`held`, `Stop`, `share`), `coreW`, `TableI`, `OpEntI`, `OpTabI`, `wpGW`, `valPostI`, `ewpW`, `ewpPostW`, `opTabW`, `errOkW`, `cancelTabW`, `entW`, `rowTabW`, the `down` maps |
| `Defs/Binder.lean` | `I/Binder.lean` |
| `Defs/Ctx.lean` | `Instance/Ctx.lean` (A₂'s `CtxApprox` at Core) |
| `Defs/Programs.lean` | `Instance/Programs.lean` |
| `Statements/Soundness.lean` | `B/Guarantees.lean` (`SoundRetAt`, `SoundDriveAt`, `SoundnessAt`, `Soundness`, `SoundnessContracts`, `TypedSound`; `Sound`, `ReleasedOnceEvery`, `ReuseUnobservable`, `RunImage` added); `B/Release.lean` (`ReleasedOnceOfSound`, `ReleasedOnceAll`) |
| `Statements/Composition.lean` | `B/Composition.lean` (`SoundnessOfFL`); `I/Routes.lean` (`SoundnessContractsOfFL`, `SoundnessContractsOfFLWB`, `SoundnessContractsAR`, `EffSafeOfFL` restated); `I/Device.lean` (`AdequateOfLaws`) |
| `Statements/Device.lean` | `B/World.lean` (`FL`, `AdequateRetAt`, `AdequateDriveAt`, `AdequateAt`, `Adequate`, `ExtPre`, `FamEmpty`, `DataVals`, `RelElim`, `RelShape`, `RelLaws`; `SliceShapeB`, `WBoundB` added); `I/World.lean` (`SliceShape`, `EffInterp`, `ShareMono`, `AdequateEvery`, `VTy.AbortRows`; `SliceShapeI`, `WBoundI` added); `I/Device.lean` (`Mono`, `WLaws`, `EwpMono`, the run-end laws) |
| `Statements/Interface.lean` | `I/Interface.lean` (`Arises`, `OpAdm`, `admClosedOp`, `AdmExtends`, `RowSpan`, `OpTabI.Resuming`, the `SpanRule*`, `SpanRules`, `Tier2Pinned`, `AcceptsTier2`, `ImplTyped`, `I4a`, `I4Typing`, `I4c`; `SpanRulesAt` added); `I/Device.lean` (`StopVisible`, `ShareResume`, the frames, `FramesW`, the `Span*` cases, `SpanBorrows`, `I1`, `I2`, `ShareCancel`, `I3`, `I5beta`, `mutView`, `antiFW`, `AntiRelendW`, `AntiFrameW`, `FrameW`, `I5`); `Base/Machine.lean` (the run shapes listed above) |
| `Statements/Handlers.lean` | `I/Device.lean` (`HandleCompat`, `RedLaws`, `P11`); `Instance/Laws.lean` (`tailClause`, `Expr.renameOp`, the `Law*`, `CapBeta`, `CapEta`, `fwdClause`, `fwdH`, `AnsSim`, `ctlObs`, `Hiding`, `LawFusion`, `LawNuOp`, `Laws`: A₂ at the instance) |
| `Statements/Abstraction.lean` | `Instance/Laws.lean` (A₂'s `Abstraction` at the instance) |
| `Statements/ZeroCost.lean` | `A/Lowering.lean` (`LowClass`) |
| `Statements/Conservativity.lean` | `I/Interface.lean` (`WBCore`; `EmbedsNil` added); `I/Device.lean` (`ConservativeWB`, `Conservative`) |
| `Statements/Lifetimes.lean` | `B/World.lean` (`LifetimeSound`) |
| `Statements/Exclusivity.lean` | `I/Interface.lean` (`Exclusive`, P10); `B/World.lean` (`ExclusiveB` added) |
| `Statements/EffectSafety.lean` | `A/EffAlg.lean` (`EffAlg.Safe`), `Instance/Rows.lean` (`RowAlgSafe`); Core's `EffSafe` to `Base/Machine.lean` |
| `Statements/Binder.lean` | `I/Binder.lean` (`BinderMachine`, `FreezeBinderLoc`, `FreezeBinderLife`, `FreezeBinder`, `NotVDenNaturalArises`); `ReleasedOnceReuse` retired (§4.5) |
| `Statements/Linearity.lean` | retired (`P8a`, §4.5) |
| `Statements/EndState.lean` | `I/Combined.lean` (`I1Prog`, `I2Prog`); `Guarantees`, `EndStateAt`, `EndState`, `Tier1End`, `EndStateBinder` retired (§4.5) |
| `Audit.lean`, `AxiomCheck.lean`, `Status.lean` | stay; extended (§5.2, §5.4) |

### 4.5 Retired statements, restated results, and changed conjuncts of done

Nothing below is false. Each depends on a definition this design retires or narrows, so its
statement no longer says what it said. Its proof idea carries over to the new statement.

| retired definition | why | replaced by |
|---|---|---|
| `Guarantees`, `EndStateAt`, `EndState`, `Tier1End` | they held the device's option-sensitive conjuncts in done (finding #5), the tautology `ReleasedOnceAll` (finding #2), and `SoundnessContracts`, whose route at W was through `Conservative` (finding #7) | `Combined`, done, `Tier1` (§3.5) |
| `EndStateBinder` | defined from `EndStateAt` | `CombinedBinder` |
| `P8a` (`:= ReleasedOnceAll`) | it named a tautology as the resource half of continuation linearity | B5 at the runs that capture (`p8a_of_combined`) |
| `ReleasedOnceReuse` (an OPEN statement) | its per-step bijection reads dead locations (§2.4); I have not checked that typed programs avoid them | B5 `ReleasedOnceEvery` |
| `SoundnessContracts` as a conjunct of done (the definition stays, beside done) | its route at a world needs `Conservative` (finding #7) | `Sound` with `ContractsW`; `soundnessContractsAR_of_combined` |

| conjunct of done that changed | old | new | why |
|---|---|---|---|
| P14 | `ConservativeWB M`: Core-valid values at row-abortive types stay valid at every index reachable from σ = [] | `EmbedsNil M`: at the nil index itself | the future-index form needs `Mono`, which fixes OQ-8 (finding #5, §3.3). Done holds less for a Core-proved value used inside a lend that spans a stop. `ConservativeWB` stays beside done, in `Device`. `AGREE.md` decision 2 (§7 Q7) |
| B6 | `Exclusive M` (validity and the typed invariant with what suspensions hold) | `ExclusiveB M` (validity) in B; `Exclusive M` in `I.Interface` | `held` is the interaction's field (§2.1); done holds both |
| the bounds | `WLaws M` | `WBoundB M` (B) and `WBoundI M` (I) | `Mono` to the device (finding #5); the effect bounds out of B (§2.3) |
| tier 1 | `Tier1End` with `WBCore` | `Combined J₁ coreW admClosedOp .abortive` | `WBCore` is Core-only and checked, a companion result; tier 1 is now done's definition |

| restated theorem | new statement | proof |
|---|---|---|
| `endState_prog`, `status_endState_prog` | `combined_prog`: done's program-level conjuncts, for every world | projection, as before |
| `i1Prog_of_endState`, `status_i1Prog_of_endState` | `i1Prog_of_combined : Combined J M Adm .any → I1Prog ⟦J⟧` | as before: `Pins` at `.any` (`AcceptsTier2`, for `at17`), `Sound`, `d_storeCancelNU` |
| `i2Prog_of_endState`, `status_i2Prog_of_endState` | `i2Prog_of_combined : Combined J M Adm .any → I2Prog ⟦J⟧` | as before: `AcceptsTier2` (`at02`, `at04`, `at12`), `Sound` |
| `p8a_of_endState`, `status_p8a_of_endState` | `p8a_of_combined : Combined J M Adm c → ReleasedOnceEvery J M.toBWorld` | projection |
| `not_endState_of_leak`, `status_not_endState_of_leak` | `not_combined_of_leak` | as before: `Combined` holds `WBoundI` (`EffInterp`), `WBoundB` (`DataVals`) and `Adequate` |
| `status_tier1End_of` | `tier1_of`: `Tier1` from the to-build items of §3.5's tier-1 list, each a hypothesis; and `closedCore_of`, the same with `RowPoly` dropped (`Props₁₀`), at the closed-row restriction | the old term with the new conjuncts added |
| `effSafeOfFL` | `effSafeOfFL : ∀ M J, FL M J → FamEmpty M.toBWorld → AdequateEvery M → EffSafe J` | unchanged: its proof read only `FamEmpty` and `AdequateEvery` out of `WLaws`. P2 in done is a projection of `A.Props₁`; this is the instance's route to it |
| `status_releasedOnceAll` | re-labelled "a tautology about runs, a run lemma" | unchanged |

---

## 5. Findings #2, #6, #7 (and where #3–#5 are resolved)

### 5.1 #2: exactly-once release had no content

- **In done:** B5 `ReleasedOnceEvery` (§2.4). Every complete run, reuse included, is the image of a
  non-reusing run that releases each cell once. It fails at a typing that types a stale free
  (`not_releasedOnceEvery_staleFree`, §6.3), so it is not a tautology. Its typing content is B3 and
  B4; its machine content is `ReuseUnobservable`, whose proof depends on OQ-43 (§2.4, §7 Q4).
- **`ReleasedOnceAll`** is documented as a tautology about runs and kept as a run lemma
  (`B/Release.lean`), out of done. `ReleasedOnceOfSound` likewise: it does not use its `SafeRuns`
  and `Terminates` premises.
- **Doc claims to fix** (the builder applies these with the restructure):

| where | the claim | the fix |
|---|---|---|
| `DESIGN.md` §1.0 l.138 (`Guarantees`); §1.5 l.664; §1.6 l.725 (P8.a as a corollary); D9 l.1164–1175, l.1193–1195; §3 T1 (a) l.1579–1580; §5 I3 (a) l.2886–2887; §6 P8 (a) l.3388–3391, (c) l.3398, (e) l.3419–3420, (g) l.3425; §7 rows A6, T4, T6 (l.3682, 3688, 3690); §9 second wave l.3782; §10 rows OQ-44/57 and OQ-50 (l.3822, 3828); Builder's notes l.3957 | `ReleasedOnceAll` carries "every owned resource … finalised exactly once"; P8.a "holds wherever `ReleasedOnceAll` does" | superseded by this file; where `DESIGN.md` stays as history, each line points to B5 and calls `ReleasedOnceAll` a run lemma |
| `README.md` l.64–67 (definitions), l.90 (status row), l.110 (corollaries), l.123–125, l.147, l.153, l.155 (survey rows A6, T4, T6) | the same | "Exactly once: B5 `ReleasedOnceEvery` (every run is the image of a non-reusing run; its proof waits on OQ-43); `ReleasedOnceAll` is a lemma about no-reuse runs"; A6/T4/T6 rows read B5 |
| `AGREE.md` l.67–73, l.141–142, l.192, l.245–246 | major 2 open | answered by §2.4, with §7 Q4 |
| `Targets/Status.lean` l.44, l.53–55, l.89, l.207, l.272–279, l.395, l.433 | `ReleasedOnceAll` as a conjunct and as P8.a | "a tautology about runs (run lemma)"; B5's row added, OPEN on OQ-43 |
| `Statements/Soundness.lean` l.20–21 (docstring), l.69–82 | "Every complete run that reuses no location releases every cell …" listed among T1's guarantees | moved to `B/Release.lean`'s run lemmas |
| `Statements/Linearity.lean` l.14–17, l.34–35 | "P8.a … is T1's `ReleasedOnceAll`" | P8.a is B5 at the runs that capture; `P8a` retired |
| `Statements/EndState.lean` l.25, l.41 | `ReleasedOnceAll` in `Guarantees`; P8.a corollary | retired with `Guarantees` |
| `Restricted/Corollaries.lean` l.12, l.113–124 | `p8a_of_endState` | restated (§4.5) |
| notebook `properties/i3-drop.md` (Lean target paragraph) | "`ReleasedOnceAll` releases its memory once" | B5 |
| notebook `properties/continuation-linearity.md` (Lean target paragraph) | "every complete run"; `P8a` "PROVED at every typing system" as the resource half | "B5, every run, reuse included; OPEN on `ReuseUnobservable` (OQ-43)" |
| notebook `register.md` rows P1 and P8 | `ReleasedOnceAll` proved at every typing system, as status | B5's status, with OQ-43 as its dependency; `ReleasedOnceAll` not a target |
| `FIX-RUN-END.md` l.540, l.681, l.1067 | `ReleasedOnceAll J` among done's program-level conjuncts | B5 |

### 5.2 #6: the step-index audit, extended; and `audit_J`

**Which:** extend the audit. **Why:** decision 7 constrains how W is *defined*. No Prop over the
world can see a counter hidden in `Stk` and read by the relation, because such a world can meet every
extensional law (`DESIGN.md` §4.4). A structural requirement strong enough to exclude it would fix the
representation of `Stk` (OQ-44) or of the relation (OQ-8), which done must not pick. Lifetime
well-foundedness is not a separable structural requirement either. `Life = ℕᵒᵈ`, and the
stratification `BoCa.Fig16.Cell` is well-founded recursion on a natural number (`invImage
OrderDual.ofDual`), the same shape a step index has. So the audit treats lifetime recursion as one
justification category, entry by entry, and reports every use of it whose argument comes from the
world's index.

**The extended audit** (`Targets/Audit.lean`, `audit_W`). `closure` walks the constants W's fields
use, transitively, within our modules (`Paper`, `Support`, `Core`, `Targets`), as today.

1. **Step shapes in our definitions.** Report every definition in the closure whose value uses a
   step shape: `Nat.rec`, `Nat.recOn`, `Nat.brecOn`, `Nat.below`, `Nat.iterate`, `Nat.repeat`,
   `Nat.fold`, `Nat.strongRecOn`, `Fin.induction`, `WellFounded.fix`, `WellFounded.fixF`. This is
   today's check.
2. **Counter-indexed predicates.** Report every `Prop`- or `WProp`-valued inductive family in the
   closure with an index of a **counter type**. The counter types are `ℕ`, `Fin n`, `Life`,
   `OrderDual ℕ`, the world's `Stk` when it is one of these, and any recursive inductive type that is
   not on the syntax list (`VTy`, `CTy`, `Expr`, `Val`, `Kont`, `Row`, `OpSig`, `Ctx`, `Jdg`, and
   lists of these). Report also the recursors (`.rec`, `.brecOn`, `.below`) of reported families,
   wherever they occur. Report every `Prop`- or `WProp`-valued *definition* in the closure that
   takes a parameter of a counter type, or that binds (by `∀`, `∃` or `λ`) a predicate variable
   whose domain contains one. Data structures with such fields (`UInt32`, `Loc`, `SRec`) are not
   reported: only predicates are. This catches `SafeN : ℕ → …` (finding #6's first hole) and the
   impredicative encoding `∀ P : ℕ → Conf → Prop, (closure) → P n c`, which uses no recursor.
3. **Recursion fed by the index.** In our definitions, report every use site where a recursion
   receives an argument computed from the world's index, its `Stk` component, or a counter-typed
   bound variable of a `Prop`/`WProp`-valued definition. A recursion here is a library constant whose
   value uses a step shape (`List.range`, `List.replicate`, `List.iterate`, `Nat.iterate`, `Nat.fold`,
   `Nat.sub`, `Array.range`, …) or an allow-listed entry of ours (`Cell` included). A use site is
   reported even when the constant itself is pinned, so a generic fold over `List.range n`, or the
   lifetime stratification read at a stratum computed from `Stk`, cannot hide behind the pin.
4. **Pin the report.** Each entry is on an allow-list with one justification:
   - recursion on syntax (types, terms, de Bruijn indices);
   - recursion on data (an array's length: `sepRange`, `tabFill`, `dropFill`);
   - recursion on a lifetime stratum (`Cell`, and the lifetime-indexed predicates step 2 reports).

   Step 3's use sites are never pinned by category: each is pinned by name, with a sentence saying
   why its argument is not a step count. `coreW`'s pinned list grows accordingly, and the build fails
   if the report changes.
5. **Negative tests** (`Targets/AuditTests.lean`, outside done). Six toy worlds the audit must
   reject, each a `run_meta` asserting that the report contains the offending constant or use site.
   The positive control is `coreW`, whose report is the pinned list.
   - `stepW₁`: `Stk` is `ℕ` and `val` recurses on it.
   - `stepW₂`: `val` reads `inductive SafeN : ℕ → Conf → Prop`.
   - `stepW₃`: `val` uses a library function wrapping `Nat.iterate`.
   - `stepW₄`: `val` is `(List.range n).foldl (fun R _ => F R) ⊤`, with `n` from the index.
   - `stepW₅`: `val` reads an impredicative ℕ-indexed least fixed point, built from `n + 1` and
     `n - 1` only.
   - `stepW₆`: `Stk := Life`, and `val` reads `Cell` at a stratum computed from the `Stk` component,
     using it as a counter.

**What the audit cannot do.** The audit is a syntactic check, and these encodings are known to get
past it. A counter can be carried in a type it does not recognise as one: a function type used as a
Church numeral, or a structure whose meaning is a count. A counter can be passed to an allow-listed
recursion through an argument that is not syntactically computed from the index. Decision 7 is about
how W is defined. So its enforcement is the audit together with a review of W's relation, as for any
definition that the audit cannot read semantically. The pinned report keeps the review incremental:
any change to W's closure that adds a reported entry fails the build until it is justified.

**`audit_J` (row variables are kernel syntax).** A-ROW (§1.3) is where the requirement lives: an
instance without row variables, or with only closed-instance typing, fails A (§6.2). `audit_J` checks
how the named kernel `J` represents them. Its judgement must unfold to an inductive family over a type
syntax with a row-variable constructor and a row-`∀` constructor, each with an `RVar` argument. No
constructor of that family may have a premise that quantifies over `RowEnv`, over closed rows, or
over the algebra's effects (an ω-rule reading `∀ρ` as every instance). Negative tests: `tier1` (the
`∀ η` reading) and `wrapInst` (an inductive whose one constructor wraps the `∀ η` reading) are
rejected. Positive control: `J₁` once built.

### 5.3 #7: externs carry their contracts as a hypothesis

Externs and unsafe code are outside the proofs by design (the brief, §6). So the combined theorem
proves nothing about extern implementations. It assumes their contracts, read in the composite's
semantics:

- **`Sound J M`** (B3, B4) and **B5** take `ContractsW M Γ γ` as a hypothesis (§2.2): each extern is
  persistent, and its value is in W's relation at the nil index from the empty resource. Their proof
  at W is FL and adequacy alone (`soundnessX_of_FL`, generic, to build from `gDenW_of_meets`'s
  shape): one proof method, with no route through `Conservative`.
- **At Core**, `ExternsMeet Γ γ → ContractsW coreB Γ γ`, taking the record list `[]`
  (`contractsW_core_of_meets`, to build, by unfolding). `Sound` needs only the nil index. The converse
  fails: `ExternsMeet` (`Core/Stdio.lean:597`) asks `∀ ls δ, vC true T ls δ v PMap.empty`, at every
  record list.
- **For the SPEC's externs** (`mk_input`, `take_input`, …: `!U(…)` thunks of first-order computations
  with no row, so row-abortive), `EmbedsNil M` (in done) gives `contractsW_of_meets : EmbedsNil M →
  (∀ s ∈ Γ, s.ty.AbortRows) → ExternsMeet Γ γ → ContractsW M Γ γ` (to build, in I/Routes). This is
  `soundnessContractsOfFLWB`'s route (checked, through `ConservativeWB` and `ExtPre`), now needing
  only the nil index. Done therefore states the SPEC externs' guarantee at Core's fixed contract:
  `soundnessContractsAR_of_combined : Combined J M Adm c → SoundnessContractsAR ⟦J⟧` (§3.5).
- **At other persistent types** (an extern at `!U(C)` with a resuming row, which `ExternsMeet`
  admits: Correction C2), the contract is given at W, by whoever provides the extern. Nothing bounds
  W from below at those types, so this hypothesis is only as strong as the world it is read in (§7
  Q6). `SoundnessContracts` keeps its name and definition, beside done, with its `Conservative`
  route (`soundnessContractsOfFL`, checked, in I/Routes). Its contracts are stated at Core's
  relation, at any persistent type.

### 5.4 #3, #4, #5, and the `AGREE.md` minor findings

- **#3** (row variables required by nothing): A-ROW (§1.3) makes them a requirement of every
  admissible instance, with content. They are elements of the algebra and carried by the types; the
  binder `All` has T_TAbs and T_TApp; and one program binds a generic `f` once and uses it at two
  rows. The closed-instance reading fails it (§6.2). `audit_J` (§5.2) checks the representation.
  Core today fails A-ROW and is recorded as such (§4.2).
- **#4** (T4 unstated): A₃ (§1.7) states `LoweringCorrect`, `Erased` and `ZeroCost` over a `Target`.
  The classes are read off A's runs, the source side is A's `Obs`, references are required, and
  control lowers to a state machine.
- **#5** (done constrained OQ-8/9): §3.2–§3.6.
- **`AGREE.md` minor findings:**
  - `status_I3_core`'s label becomes PROVED AT σ=[] (device).
  - `AxiomCheck` also checks proof-carrying definitions (`capPass`, `pmapRekey`, `Restrat.Emb.comp`)
    by `collectAxioms` on definitions.
  - `UnwindOrder` reads `catches` and handles superseding raises caught inside `K` (§1.4).
  - Both orders are over runs under a runner, at every row the runner answers (§1.4).
  - η has no unary form and lives in A₂ (recorded, §3.2).
  - `StopVisible` moves to the device (§3.6).
  - "No forget" is pinned by A-LIN's `Structural` with `¬ Drop (kTy …)` (§1.3).
  - `DivFree`'s dependence on decision 35 is A-DIV's requirement (§1.3).
  - `ImplTyped`'s dead hypothesis in `I4a`, the missing tier-1 rejections and the unwitnessed
    reachability premises are unchanged and recorded.
  - The notebook P1's narrowing to data answers is `AGREE.md` decision 7, unchanged.

### 5.5 The review of this file's first version, finding by finding

| # | severity | finding | resolution |
|---|---|---|---|
| 1 | blocker | A did not require row variables: no `var`, free `substJ`/`substC`, no generalisation rule, `AccRowPoly` unwritable, the requirement moved to `audit_J` | `EffAlg.var` with `VarLaws` (§1.2); `substTy`/`substCTy`/`substC` with `TySubst`, `substJ` defined (§1.3); `All` with T_TAbs, T_TApp; `AccRowPoly` as one closed program binding `f` once and using it at `0` and `(l)↑`; the closed-instance reading fails it (§6.2); rank 1 is the floor, rank n OQ-13's (§7 Q2) |
| 2 | major | "linear or affine; no forget" not required: `Drop`/`Pers` untied to `der`; duplication unconstrained; `UseObs` vacuous | `Structural` ties `Drop` and `Pers` to `der` both ways, at the unit value and the self-pair, in every context; κ neither `Drop` nor `Pers`; no κ eliminated twice in sequence; no runnable cancel of a linear κ; `UseObs.Sound` ties tags to A's catch, resume and cancel steps (§1.3, §1.5). The finding's form ("every term typed with an unused variable") is not taken: `⊤`-introduction and `0`-elimination absorb any context, so Core (`topI`, `zeroE`) would fail it (§1.3, check `absurd_absorbs`) |
| 3 | major | `HandlerSem` only at top level | every conjunct holds in an outer context `K₀`, and `Congr` lifts every step through `plug` (§1.3) |
| 4 | major | A₃ trivially satisfiable | `Target` with run events; A's `Obs` both ways; `Of` read off A's runs and clauses; references required, correct and handler-free; control lowers to a state machine (§1.7) |
| 5 | major | divergence as an effect not required | `DataDiv`: `Data` pinned, every data answer div-free, `Loop`'s `next`/`close` typed, the drive; A-ACC (e), (f) (§1.3) |
| 6 | major | A-CAN's definitions unwritten; `NoIntercept` unbounded; `CancelOrder` vacuous; only row `0` | `CancelTrace`, `FinTrace`, `UnwindTrace`, `PendTrace`, `Alone`, `Ended`, `Region`, `keep`, `Answered` written out; bounded by the answer; A-ACC (b) has a complete cancel; quantified at every row the runner answers (§1.4) |
| 7 | major | A-ACC prose only; `Forwarding`, `ThenRule` unspecified | `Witness`, `Acceptance` (a)–(f), `AccRowPoly`, `ThenRule` as definitions; forwarding is `KontLaws`' handler-frame clause; the derived run predicates one line each; a non-vacuity lemma per decided feature (§1.2, §1.3, §6.1) |
| 8 | minor | `lift` and `sig` unconnected | `has` with `RowSig`: `(l)↑` is exactly `sig l`'s operations, `⊙` is union; why not "every row is a sum of lifts" (`Σ^abort`) (§1.3) |
| 9 | minor | no `ret` | `ret : Val → Term`, used in `HandlerSem`, `IsVal`, `Structural`, `Answered`, `Ended` (§1.2) |
| 10 | minor | "no sum for failure" dropped by the design | §7 Q5 |
| 11 | minor | A-CAN cited Voigt as its shape; `io` ambiguous | A-CAN is ours, Voigt and Ahman–Bauer possible routes (§1.1, §1.4); `NoIO` (§1.3) |
| 12 | major | A and B met outside I: B imported I's world, `WBound` in B held effect content, base imported A | `B.BWorld` with borrow fields only; `I.SemWorld extends` it; `WBoundB` in B, `WBoundI` in `I.Interface`; base imports no A; `orowAlg`/`closedRowAlg` in Instance; Instance imports no B; §2.3 rewritten (§0, §2, §3.1) |
| 13 | major | B5 silently depends on OQ-43 (b); per-step maps incoherent | OQ-43 and TwoRun cited; the dependency stated; §7 Q4; one location map for the run; built from `run_sim`/`fresh_run_image` (§2.4) |
| 14 | major | the audit extension does not close the holes | predicates only; use sites fed by the index; `stepW₄`–`stepW₆`; the residual stated, review part of decision 7's enforcement (§5.2) |
| 15 | minor | `ContractsW coreW ↔ ExternsMeet` false; `SoundnessContractsAR` not a corollary | the `→` direction only; `soundnessContractsAR_of_combined` (§3.5, §5.3) |
| 16 | minor | the tier-1 list omitted obligations | `HandlerRed`, the `NoIntercept` and `EffSafe` bridges, the runner–platform correspondence, `I4a ⟦J₁⟧`, `ContDiscipline` at `J₁`, and the new requirements, each listed (§3.5) |
| 17 | minor | `i1Prog_of_combined`, `i2Prog_of_combined` need `c = .any` | restated at `Combined J M Adm .any` (§3.5, §4.5) |
| 18 | minor | `EffSafeOfFL` took `WLaws` | restated over `FamEmpty ∧ AdequateEvery` (§4.5) |
| 19 | minor | `ConservativeWB → EmbedsNil` not listed as a change | §4.5's changed-conjuncts table; §7 Q7 |
| 20 | minor | `ourInst` without `Ξ`; no runner–platform map; `SpanRulesAt` undefined; `WBCore` in `Tier1` | `J.Ξ` in `OurTyping`; `runnerOf`/`platformOf` (§4.1); `SpanRulesAt` defined (§3.5); `WBCore` a companion, `Tier1` done's definition (§3.5) |

---

## 6. Non-vacuity

### 6.1 A₁ is not met trivially

A₁ has lower bounds and upper bounds. The lower bounds are `EffRules`' closure, `HandlerSem`'s steps,
`RowPoly`'s program and `Acceptance`'s witnesses. The upper bounds are `Structural`, `EffSafe`,
`Safety` and `Cancellation`. A degenerate instance breaks one side. To build, in
`Targets/A/NonVacuity.lean`, each a short proof from the named conjunct:

```lean
theorem not_props₁_of_noLabels (h : IsEmpty S.EA.Lab) : ¬ Props₁ S            -- A-ACC (a) catches a label
theorem not_props₁_of_noSteps (h : ∀ c ev c', ¬ S.step c ev c') : ¬ Props₁ S    -- A-ACC (a)'s run has a catch step
theorem not_props₁_of_emptyTyping (h : ∀ Θ Γ e j, ¬ S.der Θ Γ e j) : ¬ Props₁ S -- no witness is typed
theorem not_props₁_of_noVars (h : IsEmpty S.EA.Var) : ¬ Props₁ S               -- AccRowPoly binds a variable
-- one per decided feature
theorem not_props₁_of_noLinear (h : ∀ l o, o ∈ S.sig l → o.cls ≠ .linear) : ¬ Props₁ S       -- A-ACC (a)
theorem not_props₁_of_noAffine (h : ∀ l o, o ∈ S.sig l → o.cls ≠ .affine) : ¬ Props₁ S       -- A-ACC (b)
theorem not_props₁_of_noAbortive (h : ∀ l o, o ∈ S.sig l → o.cls ≠ .abortive) : ¬ Props₁ S   -- A-ACC (c)
theorem not_props₁_of_noFinalisers (h : ∀ K, S.fins K = []) : ¬ Props₁ S                    -- A-ACC (b), (d)
/-- Shallow: no pure run from a resume reaches the frozen context under its handler. -/
theorem not_props₁_of_shallow
    (h : ∀ c c' K₀ l H K w, S.term c = S.plug K₀ (S.resume (S.capture l H K) w) → S.PureSteps c c' →
      S.term c' ≠ S.plug K₀ (S.handle l H (S.plug K (S.ret w))))
    (hn : Nonempty S.EA.Lab) (hH : Nonempty S.Hnd) (hK : Nonempty S.Kont) (hv : Nonempty S.Val) :
    ¬ Props₁ S                                                                                 -- HandlerSem's deep resume at `init`
/-- A typing that weakens a κ before the unit value (a weakening rule at thunk types, say). -/
theorem not_props₁_of_forget (h : ∃ Θ Γ c B C, c ≠ .abortive ∧
    S.der Θ (S.ext Γ (S.kTy c B C)) (S.val S.unitV) (.val S.UnitT)) : ¬ Props₁ S              -- Structural, ¬ Drop (kTy …)
/-- A typing that pairs a κ with itself (a contraction rule at thunk types, say). -/
theorem not_props₁_of_copy (h : ∃ Θ Γ c B C, c ≠ .abortive ∧
    S.der Θ (S.ext Γ (S.kTy c B C)) (S.val (S.pair S.var0 S.var0))
      (.val (S.Tensor (S.kTy c B C) (S.kTy c B C)))) : ¬ Props₁ S                              -- Structural, ¬ Pers (kTy …)
/-- A typing that resumes one κ twice. -/
theorem not_props₁_of_twoShot (h : ∃ Θ Γ c B ε w₁ w₂, c ≠ .abortive ∧
    S.der Θ (S.ext Γ (S.kTy c B (S.F ε S.UnitT))) (S.seqT (S.resume S.var0 w₁) (S.resume S.var0 w₂))
      (.comp (S.F ε S.UnitT))) : ¬ Props₁ S                                                     -- ContDiscipline
theorem not_props₁_of_total (h : ∀ e A B, S.der [] S.emp e (.comp (S.F S.EA.unit (S.U (S.Loop S.EA.unit A B)))) →
    ∃ n, ∀ d, S.DPath S.R₀ (S.rinit S.R₀ e, .main) d → n ≤ d.length → ∃ j, S.FinalDrive (d.cfg _ j)) :
    ¬ Props₁ S                                                                                 -- A-ACC (f)
theorem not_safety_of_divergentReturner (h : ∃ e A, S.Data A ∧ S.der [] S.emp e (.comp (S.F S.EA.unit A)) ∧
    ∃ f : ℕ → S.RConf S.R₀, f 0 = S.rinit S.R₀ e ∧ ∀ n, ∃ ev, S.RStep S.R₀ (f n) ev (f (n + 1))) :
    DataDiv S → ¬ Safety S                                                                     -- DivFree is pinned
-- `not_noIntercept_of_regionCatch`: a typed program, a path from the start of one of its cancels,
-- and on it, before the answer, a `catch` step that is not a step of the running finaliser alone,
-- refute `NoIntercept` (no `CancelTrace` constructor admits that step).
/-- A typing that types a resuming operation at the empty row, where the machine gives an unhandled
operation no step, fails `EffSafe`: `StopsIn 0` is empty by `RowSig`. -/
theorem not_effSafe_of_typesUnhandled (hs : RowSig S) (l i v A)
    (ht : S.der [] S.emp (S.perform l i v) (.comp (S.F S.EA.unit A)))
    (hno : ∀ ev c, ¬ S.step (S.init (S.perform l i v)) ev c) (hc : ConfLaws S) : ¬ EffSafe S
```

For A₃: `not_erased_of_contAlloc` (a lowering whose answering program's target run allocates a
continuation object fails `Erased`) and `not_zeroCost_of_noRef` (`ZeroCost`'s first conjunct asks a
reference for every answering and abortive program).

Consistency (A₁ is satisfiable) is the tier-1 instance once `J₁` is built: every A₁ conjunct holds at
`ourInst J₁` from checked results and the to-build items of §3.5. A second, independent instance would
also check A₁ against a calculus that is not ours. EffModelRel [SIB], which has row abstraction and
proves every algebraic law, is the natural candidate, as an optional instance.

### 6.2 A-ROW is not met by closed-instance typing

```lean
/-- `instReading tier1NU`: Core's unr-free typing over `orowAlg`'s open rows.  A judgement at a row
context reads "every admissible closed instance is derivable", `All ρ k C` reads as `C`, and `genV`,
`instV` are erased.  It meets T_TAbs, T_TApp and the substitution conjunct by its definition, and
fails `AccRowPoly`. -/
theorem not_accRowPoly_instReading : ¬ AccRowPoly (ourInst (instReading tier1NU))
```

Proof (to build; D21's inversion cost). At a closed program, `tier1NU`'s rule for `let` gives `f` one
closed type. `!U(U(A ⊸ F_r B) ⊸ F_r 1)` is that type at one row `r`. The first use is sequenced
before the handler in a program at row `0`, so its result row `r` is below `0` (`[sub]` only
enlarges): `r` admits nothing. The second use passes `g₁`, whose body performs an operation of `l`,
at `U(A ⊸ F_r B)`. By inversion `[perform]` needs `has r l i`. Contradiction. The theorem is finding
#3's check turned around. A rejects the closed-instance reading, and `audit_J` is left to check that
the named kernel represents its row variables as syntax.

### 6.3 Done does not hold for free

1. **The program level is asserted of `J₂`, not of `W`** (`combined_prog`). No choice of world makes
   `A.Props₁ (ourInst J₂)`, `Sound J₂ W` at `Γ = []`, B5 or `Pins J₂` easier.
2. **The pins and A's lower bounds hold `J₂` from below.** `ExtendsNUo J₂` makes `J₂` type every
   program Core's unr-free rules type. `SpanRulesAt` and `AcceptsTier2` make it type AT02, AT04, AT12
   and AT17. `AccRowPoly` makes it type a generic function bound once and used at two rows, and
   `Acceptance` makes it type programs that run every effect form. With `Sound` (an upper bound),
   each of these programs must run safely and end with the memory empty. A typing system that types
   nothing fails the pins; one that types an unsafe program fails `Sound`.
3. **B5 is not a tautology** (to build):

   ```lean
   /-- `staleFree := let x = alloc () in free x; let y = alloc () in free x`.  Under an allocator
   that gives `y` the location `x` had, the run ends at `()` with the memory empty; no run that
   reuses nothing is its image, since there the second `free x` has no step. -/
   theorem not_releasedOnceEvery_staleFree (J M) (h : ⟦J⟧.closed staleFree (.ret .unit)) :
       ¬ ReleasedOnceEvery J M
   ```

4. **A world cannot make its guarantees vacuous.** `WBoundB` and `WBoundI` bound the relation by W's
   runs at every index and type former. `Adequate` with `EffInterp` and `DataVals` excludes a world
   whose `Upd` admits a reachable leak (`not_combined_of_leak`, restated from `not_endState_of_leak`;
   the witness `leakW`, checked). `Arises`, `Exclusive`, `ExclusiveB` and `LifetimeSound` do not read
   `Upd` (FIX-RUN-END §3, Layer 1b).
5. **The audits read definitions.** `audit_W` rejects the six step-indexed toy worlds, with the
   residual of §5.2 left to review. `audit_J` rejects the instance reading.

---

## 7. Questions for the user

1. **Tier 1 now requires row variables, and the row `∀`.** A-ROW is a requirement of A, so the
   tier-1 milestone needs `J₁`: Core's unr-free rules over open rows, with a rank-1 row `∀` whose
   generic values are only let-bound, denoted into Core by erasure and inlining. Today's Core meets A
   at the closed-row restriction only (`closedCore_of`). Is `J₁` the intended tier-1 milestone, or
   should tier 1 be the closed-row restriction?
2. **Rank.** A requires Yoshioka's T_TAbs and T_TApp with a `∀` former, and a generic value bound by
   `let` and used at two rows. It requires nothing of a generic value passed as an argument, stored,
   or returned. PR #233's closing comment names "callbacks taking callbacks, stored or returned
   callbacks, policies as values". Does decision 62 mean rank n now, which would make it a
   requirement of A and give `J₂` a relation clause for `∀ρ`? Or is rank 1 the floor, with rank n
   left to OQ-13?
3. **`audit_J`.** Row variables "in the kernel" are now required by A, and checked on the kernel's
   definition as no step-indexing is. Is a definitional audit the right second check?
4. **B5 and OQ-43.** B5's proof needs a two-run fact with array steps: OQ-43 at (b) block renamings
   or (c) a binary FP, both classed deferrable and optional under U22. Keep B5 in done, making OQ-43
   (b) or (c) required? Or move B5 beside done, so that done's release content is B3 under every
   allocator with B4? Or state B5 on a provenance-instrumented machine? That would be a twin of
   `Step1`, which the brief excludes unless you ask for it.
5. **"No sum for failure."** A carries "errors are abortive operations" (`raise`, abortive clauses,
   unwinding). It does not carry "no primitive returns a sum for failure": A cannot see an instance's
   primitives, and A's runner either answers or does not. Should A require that a runner's
   co-operation never answers a sum for failure? Failures would then be raised as abortive operations,
   which needs runners that raise (Ahman–Bauer's runners with exceptions). Or is #168 a library
   convention outside A?
6. **Externs at resuming rows.** Their contracts are given at the composite's world, by whoever
   provides them, and nothing bounds that world from below at those types (§5.3). Is that the intended
   reading of "outside the proofs by design"?
7. Unchanged from `AGREE.md`:
   - decision 1 (the σ = [] reading);
   - decision 2 (conservativity's scope: done now holds `EmbedsNil` at the nil index, row-abortive
     types; §4.5's changed-conjuncts table);
   - decision 3 (the freeze binder beside done);
   - decision 7 (T1's scope);
   - decision 8 (the survey);
   - decision 9 (`UpdReclaim` in done?);
   - decision 10 (the `Upd` pin's `→` half, now in `SliceShapeB`).

   Decisions 4, 5 and 6 are answered by §5.3, §2.4 (with Q4) and §3.5.

---

## 8. Build order (when told)

1. `Targets/A/*` with no Core import: `EffAlg` with `var` and `VarLaws`; `EffectSystem`; the derived
   run predicates; the requirements; A₁, A₂, A₃ as `def … : Prop`; `A/NonVacuity.lean`.
2. File moves to `Base/`, `B/`, `I/`, `Instance/` with no statement change but the `BWorld`/`SemWorld`
   split. `lake build Targets` green before any new Lean. Check the import discipline: base and B
   import nothing of A or I, and Instance imports nothing of B or I.
3. `ourInst` at Core's closed-row restriction; `runnerOf`/`platformOf`; A-MACH, A-SEM and A-ACC at
   Core; the bridges for `EffSafe`, `NoIntercept` and `UnwindOrder`; `WBoundB`, `WBoundI`,
   `EmbedsNil`, `ContractsW`, `Combined`, the restated corollaries.
4. B5: `RunImage`, `ReleasedOnceEvery`, `ReuseUnobservable` (stated); `staleFree` and its
   non-vacuity lemma. TwoRun's repair waits on the user's answer to §7 Q4.
5. The extended audit with `stepW₁`–`stepW₆`; `audit_J` with its negative tests.
6. `J₁` (when the user confirms §7 Q1–Q2), with `not_accRowPoly_instReading`.
7. `Status.lean`, `AxiomCheck.lean` (definitions included), `README.md`; the doc fixes of §5.1; the
   notebook's register and the A/B/I pages.

Targeted builds only (`lake build Targets` and module targets); no Core edits; no commits until told.

---

## Sources

**Repository** (`~/repos/borrow-core-targets`, branch `targets` at `938d280`):

- `docs/effects-state/`: `BRIEF.md` (all); `04-decisions.md` (header, summary, K1–K18, C1–C10);
  `05a-open-questions-1-34.md` (OQ-8, OQ-9, OQ-10–OQ-13, OQ-23, OQ-31); `05b-open-questions-35-68.md`
  (U22, OQ-43, OQ-44, OQ-50, OQ-51, OQ-57, OQ-58, OQ-64).
- `docs/decisions.md`: decisions 8, 35, 48–63.
- `research/effects/src`: `SUMMARY.md`, `intro.md`, `system-a.md`, `system-b.md`, `interaction.md`,
  `register.md`, `decisions.md`, `method.md`, `literature.md`, `foundations/*`, `properties/*`,
  `design-space/axes.md`, `side/multi-shot.md`, `tracks/*`. `research/effects/survey.md` (TL;DR,
  §1.1–§1.11, B2).
- `experiments/Targets`: `README.md`, `AGREE.md`, `DESIGN.md` (all), `FIX-RUN-END.md` (all),
  `Targets.lean`, `Targets/Defs/*`, `Targets/Statements/*`, `Targets/Restricted/Composition.lean`,
  `Targets/Restricted/EffectSafety.lean`, `Targets/Restricted/AcceptedT1.lean`,
  `Targets/Restricted/Soundness.lean`, `Targets/Status.lean`, `Targets/Audit.lean`,
  `Targets/AxiomCheck.lean` (header and check); every theorem name of `Targets/Restricted/*` and
  `Targets/Checks/RunEnd.lean`.
- `experiments/TwoRun/README.md`.
- The verifier findings `findings2-7.json`, and the review of this file's first version.
- `SPEC.md` §19 (*Cancels*, *Types*, *Typing*, *Semantics*).
- `Core/`:
  - `Fundamental.lean`: `CDerives` (`allI`, `allE`, `bangThunkF`, `bangThunkV`, `bangE`, `effThen`,
    `effHandle`), `SemJ`, `fundamentalC`, `reclaim`, `theorem32`, `adequacyC`.
  - `Demonic.lean`: `wpTS_demonic`, `wpTSD_safe`, `theorem32D`, `adequacyD`, `adequacyD_safe`,
    `adequacyD_val`.
  - `EffPrograms.lean`, `EffExamples.lean`: `prog`, `progC`, `takeProg`, `storeCancel`,
    `failOutside`, `tickProg`, `tickAnsProg`, `adequacyD_obs`.
  - `Totality.lean`: `total_every_run`, `total_no_infinite_run`.
  - `Invariant.lean` (`TW.valid`, `TI`, `TW.inv`); `World.lean` (`TW`, `Tagged`).
  - `RelationFacts.lean` (`vC_outlives`, `vC_outlivesLe`); `Relation.lean` (`forceE`, the `unk`
    clause).
  - `Persistent.lean`: `VTy.persistent`, `Ctx.SplitP.dup`, `Ctx.DeadP.drop`, `Ctx.SoloP.skip`.
  - `EffRules.lean`: `VTy.Drop`, `kTy`, `clauseTy`, `retTy`, `hndTerm`, `thenE`.
  - `Types.lean`: `VTy`, `CTy`, `CTy.loop`, `CTy.loopEff`, `CTy.effOf`. `Nu.lean`: `unfold`.
  - `Stdio.lean`: `ExternsMeet`, `gDenC_of_meets`, `externs_every_run`.
  - `Stale.lean` (header, `Alloc.atCount`); `Alloc.lean` (`Alloc`).
  - `Steps.lean`: `plug_cmp`, `plug_decomp`, `head_det_eff`, `step1_plug_inv`.
- `Paper/S3_Dynamics/Definitions.lean`: `kappa`, `cancelVal`, `errNext`, `Kont.HasHnd`,
  `Kont.Catches`, `Head`'s constructors (`hop`, `hunwind`, `ufin`, `ufinC`, `cfret`, `cferr`,
  `cancel`, `creraise`). `Paper/INDEX.md` (6.60, 6.151);
  `Paper/S6_8_FundamentalProperty/Lemmas.lean` (header).

**Paper.** [CONF] `~/repos/borrow_lang/3764117.pdf` via `pdftotext`: Lemma 3.1, Theorem 3.2,
Corollary 3.3 and 415:17–18, Fig. 8 and its text (Unk), 415:21, 415:23. [TR]
`3764117-supplement.pdf`: 6.60, 6.151, the `Unk` rows.

**Primary literature, read at the cited statements:**

- Plotkin–Pretnar, *Handling Algebraic Effects*, LMCS 9(4:23) 2013: §1.1–§1.3, Def. 4.2, Prop. 4.3,
  Def. 4.5.
- Bauer–Pretnar, *An Effect System for Algebraic Effects and Handlers*, LMCS 10(4:9) 2014, arXiv
  1306.6316: §2, Thm 4.1, Cor. 4.2, Thm 5.1.
- Yoshioka–Sekiyama–Igarashi, *Abstracting Effect Systems for Algebraic Effect Handlers*, arXiv
  2404.16381: Fig. 1, Fig. 2 (K_Var), Def. 3.4, 3.5, Fig. 4 (E_Eval, R_Handle2), §4.3 and Fig. 5
  (T_TAbs, T_TApp, T_Handling), Def. 5.1, Lemma 5.4–5.7, Thm 5.8, 5.9.
- Tang–Hillerström–Lindley–Morris, *Soundly Handling Linearity*, POPL 2024: Def. 3.1, Thm 3.2–3.4,
  Fig. 7, Def. 3.5, Thm 3.6.
- van Rooij–Krebbers, *Affect*, POPL 2025: Thm 2.1, §3.1–3.2, §7.
- Kammar, *An Algebraic Theory of Type-and-Effect Systems*, PhD thesis 2014: abstract, (11.1), §11.2,
  Thm 12.5. It is the source for Kammar–Plotkin POPL 2012, whose PDF could not be retrieved.
- Zhang–Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019: abstract, Thm 1–3,
  Example 1.
- Brachthäuser et al., System C (TR): Lemma 7, Def. 8, Cor. 9.
- Ahman–Bauer, *Runners in Action*, ESOP 2020: Def. 1, Thm 7.
- Voigt–Schuster–Brachthäuser, OOPSLA 2025: Thm 3.6.
- Congard–Munch-Maccagnoni–Douence, ESOP 2026: §3.
- Ma–Ge–Jung–Zhang, *Zero-Overhead Lexical Effect Handlers*, OOPSLA 2025: abstract, §1, Thm 1,
  Cor. 1.
- Timany–Guéneau–Birkedal, POPL 2024: abstract.
