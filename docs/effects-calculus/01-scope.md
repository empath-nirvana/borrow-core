# 01 · Scope, foundations and the user's decisions

This section says what the effect calculus is and what it is not; what it is built on; what is
in the kernel, what is derived, and what is outside the proofs; the user's decisions that bound
it, each at the strength the user gave it; and what "tier 1" and "tier 2" mean as properties of
the calculus. It ends with the checklist against which 08 validates that the specification is
the calculus and not an approximation of it.

It owns no K, D, L or T id (00 §8). Every object is 00 §1's, cited by id; every construct, law
and theorem is cited by the id of the section that owns it. Marks follow 00 §0.1: **[Lean]**
for a declaration cited `file:line`, **[read]** for a reading of a document, **[via X]** for a
literature claim taken from the report X, **[user]** for a user decision with its source.

---

## 1. The calculus in one page

### 1.1 What it is

The effect calculus is BoLo's linear calculus with borrowing, extended by algebraic effects and
handlers, in the kernel, over BoLo's own semantic model. Its spine is one chain of objects:

```
  Sig            one signature of operations                     O-SIG, K-SIG
   ⊕             rows are finite sums of named signatures        O-ROW, K-ROW
  ⟦Σ⟧δ           the interpretation of a row                     O-INT, K-INT
  opTable ⟦Σ⟧δ   the one protocol table of a row                 O-TAB, D-OPTAB
  ewp_W          least fixed point of wpG_W into "value in Q,
                 or a stop the table allows"                     O-EWP, D-EWP
  𝒱 𝒞 𝒢 ⟦·⟧_W    the relation, one clause per former, at W        O-REL, D-REL
  Δ; Γ ⊨ e : C   semantic typing at every world                  D-SEM
```

and two implementations of a signature: a **model** (a handler, K-MODEL, D-MODEL) and a
**comodel** (a capability lent by a borrow, K-COMODEL, D-COMODEL), checked against the same
table. Every construct enters the relation only through `opTable ⟦Σ⟧` and the world `W`
(00 §6, "The spine").

The structure is the one the user signed off on (memory record `effect-calculus-spec-first`,
2026-10-03; tracking issue #290), taken from the audit (`docs/effects-audit.md` §3) with the
corrections of 00 §0.3.

### 1.2 Judgement forms

```
  Δ ⊢ Σ row                     Σ is a sum of named signatures with distinct names   (02)
  Δ; Γ ⊢ e : C                  CDerives; the row is a meta-index of C = F_Σ A, …     (03, O-JDG)
  (μ, e) ↦ (μ', e')             a head step under an evaluation context              (04)
  ARun A k μ e k' μ' t          an allocator run, A any allocator                    (04, K-RUN)
  W ⊑ W'                        the world preorder                                   (05, D-ORD)
  ewp_W(e){Tb}{Q}               the effectful weakest precondition                   (05, D-EWP)
  v ∈ 𝒱⟦A⟧_W δ,  e ∈ 𝒞⟦C⟧_W δ   the relation                                          (05, D-REL)
  Δ; Γ ⊨ e : C                  ∀ δ W γ, γ ∈ 𝒢⟦Γ⟧_W δ → e[γ] ∈ 𝒞⟦C⟧_W δ                (05, D-SEM)
  e ≡ e'  /  e ≈_W e'           contextual equivalence / the binary relation          (06, O-EQ; OQ-4)
```

`Today` for each: `CDerives` (`Core/Fundamental.lean:60`), `wpG` (`Core/EffDefs.lean:27-40`),
`ewpTS` (`Core/EffDefs.lean:73-75`), `vCE`, `cC`, `cB`, `SemC` (`Core/Relation.lean:119, 154,
192, 228`) [Lean]. The relation at `W` equals `vC`/`cC` at `σ = []` by T-NIL: by definition at
the clauses that read no extension of the world, and by a per-row proof at `U`, `share` and
`KapRel`, which is unknown (O-REL, OQ-58).

### 1.3 Syntax at a glance

A summary, so that the scope can be read; 02, 03 and 04 define every form.

```
  signatures   E  ::= { op_i : A_i ↠^{q_i} B_i }_{i∈I}  (+ optional equations, OQ-22)   K-SIG
  qualifiers   q  ::= lin | aff | unr                   (grades [1,1] [0,1] [0,∞])        O-QUAL
  rows         Σ  ::= ∅ | Σ ⊕ n:E                       (distinct names)                  K-ROW
  types        C  ::= F_Σ A | A ⊸ C | C & D | ⊤ | ∀'x ⊏ c. C | νX. C                       K-FTY
               A  ::= … | U C | !A | [@a] A | Ref A | Imm a A | Mut a A | μ | fam           O-TY
  terms        e  ::= … | perform_{n,i} V                                                 K-OP
                    | raise_{n,i} V                     (abortive: B_i = 0, q_i ≠ lin)    K-RAISE
                    | M to x. N                         (sequencing at a row)             K-LET
                    | M then x. N unwind D              (the finaliser frame)             K-THEN
                    | hnd_n H M                         (a deep handler; H a model)       K-HND
                    | κ = ⟨resume, cancel⟩              (the static continuation)         K-KONT
                    | withswap                          (the comodel carrier)             K-SWAP
                    | bor_k[Σ]                          (one per printed borrow constant) K-BOR
                    | bounded_fix[A, C]                 (fixed point of a generator)      K-FIX
                    | ν-introduction, observations      (effectful codata, Loop_Σ)        K-NU
  steps            [ret] [op] [unwind] [then] [finalise] [finalise-cancel]
                   [cfin-ret] [cfin-raise] [cancel] [cancel-raise] [boundedFix]          K-STEP
```

The kernel's effect rules today are `effSub`, `effPerform`, `effRaise`, `effLet`, `effThen`,
`effHandle` (`Core/Fundamental.lean:340, 343, 348, 353, 360, 367`) [Lean]; the effectful returner
is `CTy.eff` (`Core/Types.lean:92`), with `F_Σ R` as `CTy.effOf` (`Core/Types.lean:155-157`)
[Lean].

### 1.4 What the calculus must satisfy

The scope is fixed by the metatheorems it is built to have. Each is owned by 05 or 07; this is
their quantifier shape, so that the scope is a statement and not a list of features.

```
  T-FP     ∀ Δ Γ e C.  Δ; Γ ⊢ e : C  →  Δ; Γ ⊨ e : C
           (at every W; fundamentalC is the σ = [] instance)

  T-ADEQ   ∀ e.  ∅; ∅ ⊢ e : F 1  →  ∀ allocator A, ∀ (μ₁, e₁) reachable from (∅, e) under A,
           (μ₁, e₁) is not stuck, and reaches (∅, ()) under A

  T-SAFE   ∀ e.  ∅; ∅ ⊢ e : F 1  →  no run of e stops at an operation no handler receives

  T-LEAK   ∀ e.  ∅; ∅ ⊢ e : F 1  →  every run that ends, ends with no owned resource

  T-FIN    every finaliser runs exactly once, innermost first, on return, unwind and cancel

  T-LIN    a linear κ is consumed exactly once; an affine κ at most once, and if not
           resumed then cancelled, running its destructor
```

These hold for every program of the calculus, which includes effectful closures, generators,
recursions, stored continuations and continuations that hold borrows (§3.2). Where the
specification cannot yet state a construct in full, the construct is still in the calculus,
and the place where a default would narrow it is a named restriction (§6).

Today: `fundamentalC` (`Core/Fundamental.lean:434`), `adequacyC` (`Core/Fundamental.lean:590`),
`adequacyD` (`Core/Demonic.lean:312`, every reachable configuration reaches `()` at empty memory)
[Lean]; `ewp_bot` (`Core/EffWp.lean:772`) for effect safety; `wpTS`'s `NoOwn` leftover
(`Core/World.lean:186`) for leak freedom [Lean].

### 1.5 What the calculus is not

- **Not a fragment.** Not first-order effects only, not "effects but no borrows across
  suspension", not "handlers but no stored continuations". A construct the specification
  cannot finish is a boxed question with a default, never an omission.
- **Not an encoding.** Effects are not defined by elaboration into effect-free core terms.
  Decision 48's "handlers are defined by elaboration … effect rows never enter the core"
  (`docs/decisions.md:604-608`) is superseded by the user's decision that effects are core
  (§4, row U3). The elaborator's schemas are a surface over the kernel (08), each with its
  T-ELAB obligation.
- **Not a set of per-feature mechanisms.** Errors, generators, async, state and cancellation are
  instances of one mechanism; none is recognised by name in the kernel or the elaborator
  (C-7). The user rejected "a fixed set of built-in control constructs (exceptions,
  generators) as language features" (§4, row U4).
- **Not a sibling calculus.** Laws are proved over the kernel relation (00 §4). The standalone
  carriers of `experiments/EffModelRel` have no resources, no machine and unmoded contexts
  (`docs/effects-audit.md` §1, item 3); their status is OQ-5.
- **Not step-indexed, and no new relation family.** No step index (00 §0.2 item 2); the only
  world is `W`, and a new relation family, twin constant or side mechanism beside it is a defect
  to report (00 §0.2 item 1). The relation families `vRL`, `vRLg`, `vRLs`, `vRLa`, `vRLk` built
  beside `vC`/`cC` are retired into `W` (08).
- **Not a run-time handler mechanism.** Effect handling is erased at run time (§4, row U6): the
  calculus has a lowering for every construct (T-LOWER), and no construct requires a run-time
  handler stack or handler search.
- **Not the current code.** How the kernel is built today is evidence and a baseline (T-CONS),
  not a design constraint (§4, row U14).

---

## 2. The carrier

### 2.1 BoLo's resource world

The calculus is BoLo's (SPEC §1: "The calculus is BoCa with the logic BoLo", `SPEC.md:18`)
[read]. Its semantic objects are BoLo's: the resource algebra of `[TR]` §5, the `wp` of `[TR]`
p.6, and the frame rules `[TR]` 6.64 (immutable lend), 6.65 and 6.66 (mutable lend, fold and
unfold), and the reborrow 6.150. Separating conjunction and the magic wand `─⋆` are BoLo's,
and `─⋆` is the future-world quantifier over resource extensions, as in BoLo.

**Lifetimes are `Life = ℕᵒᵈ`** (`Paper/S5_Model/Definitions.lean:104`) [Lean], with
`⊑ ≜ >`, `⊔ ≜ min`, `⊓ ≜ max`, `⊤ ≜ 0` (`Paper/S5_Model/Definitions.lean:100`) [Lean]. A fresh
lifetime is below every live one: a borrow opened later ends earlier. Cells are stratified by
lifetime (`CellU.InStratum`, `Paper/S5_Model/Definitions.lean:578`) [Lean]; well-founded
recursion on strata runs along the paper's `⊏` (memory record `boca-life-is-nat-dual`). Every
raw `<` or `≤` written at `Life` is read in this order; the specification never writes the
`ℕ` order at `Life`.

### 2.2 Resources that arise

The lemmas of `[TR]` §6 quantify over resources **of the linear calculus**, the resources that
arise from its programs, not over every inhabitant of the carrier type. This reading is settled
(memory record `resources-are-of-the-calculus`, marked SETTLED) [user]. In the kernel it is the
typed world `TW` (`Core/World.lean:110`), whose docstring calls it "the configurations §6
quantifies over, as a family" [Lean]: an inductive family over `(W, ps, rs)` with one
constructor per operation that changes the world: `alloc`, `free`, `store`, `immFrame`/`immEnd`
(6.64's entry and exit), `mutFold`/`mutUnfold` (6.65, 6.66), `reb`/`rebDeep` with their ends
(6.150) (`Core/World.lean:96-109`) [Lean]. `wpG` quantifies over frames `fρ` with
`TW fρ ps (rsOf ls)` and `Tagged fρ ps ls` (`Core/EffDefs.lean:29`) [Lean]. Its invariant and
its preservation by every step are `Core/Invariant.lean` [Lean].

The effect calculus uses the same reading. A table guard (`TabAtS`) is stated as a `TW`
invariant (D-ARISE, T-ARISE), never as a conjunct added to a printed definition to exclude a
resource that does not arise. A counterexample to an effect lemma is evidence only if its
witness arises (memory records `counterexamples-must-arise`, `stop-manufacturing-refutations`).

### 2.3 The world

The one world is `W = (ρ, ls, σ)` (O-W, D-W):

- `ρ : WRes`, BoLo's resource;
- `ls : List SRec`, the records of open `[TR]` 6.64 frames tagged with their frame lifetime
  (`SRec := FrameRec × Life`, `Core/FrameRecords.lean:159`), ordered by `Ext`
  (`Core/FrameRecords.lean:172`) [Lean];
- `σ`, the lends open around the current term, innermost first (05 D-W). Its `imm` entries are a
  selection of `TW`'s own `ps`/`rs`, the open 6.64 frames and their lineages; it is not a new index
  for them, and today it exists only inside `wpG`'s quantifier (`Core/EffDefs.lean:29`) [Lean].
  A 6.65 lend leaves `ps` unchanged (`TW.mutFold`, `Core/World.lean:135-144`) [Lean], so what a
  `mut` entry records is OQ-44.

At `σ = []` the definitions of 05 that read no extension of the world reduce to today's kernel by
definition; at `U`, `share` and `KapRel` they equal it only by T-NIL's per-row proof, which is
unknown (OQ-58). The frames a resumed run must close are an index `τ` beside `W` (OQ-57). Making
`σ` a component is the one structural change of the model; whether `σ` is ever non-empty at a
stop is the tier question (§5).

### 2.4 What keeps the relation step-free

The relation is defined by structural recursion on types and well-founded recursion on strata
and least fixed points (T-DEF), with no step index and no recursive domain. That rests on the
cut-offs of OQ-31: bounded recursion (`bounded_fix`, `Core/Fundamental.lean:196`) [Lean],
positive `μ`/`ν`, strict strata, operation types closed in lifetimes, and the relation never
stored in the typed world. Decision 7, "recursion without step-indexing"
(`docs/decisions.md:19-21`) [read], is kept.

---

## 3. What is in the kernel

### 3.1 The kernel

The kernel is `Core/`, `Paper/` and `Support/` (00 §0.1). A construct is **in the kernel** when
it has a `CDerives` rule or a machine step and a clause or obligation in the relation; it is
**derived** when it is a kernel term whose typing and laws follow from kernel rules; it is
**host** when it is a hypothesis of the end-to-end theorem.

Effects are in the kernel (§4, row U3). The kernel status of each construct:

| status | ids |
|---|---|
| kernel, as built | K-OP, K-RAISE, K-LET, K-THEN, K-HND, K-KONT, K-FIX, K-NU, K-DIV (as codata), K-CTX, K-STEP, K-CANCEL, K-RUN, K-SWAP (pure) |
| kernel, changed | K-SIG (grouped per effect), K-ROW (sum with distinct names), K-BOR (one constant per printed constant, at every `TableOK` row), D-W, D-ORD, D-ARISE, D-STOP, D-REL, D-SEM |
| kernel, new | K-THEORY, K-REN, K-COMODEL (as a kernel object, OQ-1), D-TABLEOK, D-MODEL, D-COMODEL, D-BIN (conditional, OQ-4) |
| derived | K-CAP (a comodel lent by a borrow; kernel status OQ-1), K-GRADE (explicit in `experiments/Grades`) |
| host | K-HOST (host-provided outermost handlers; OQ-30) |

A change to a kernel **definition** of ours (D-STOP above all) is a SPEC change, written as a
SPEC entry before kernel work. It is not "an added hypothesis": CLAUDE.md §4 governs printed
BoLo statements, not our own kernel definitions (00 §0.1, §0.3 item 4).

### 3.2 In the calculus by design

Each of the following is in the calculus, with its syntax, statics, dynamics, model clause,
laws and compatibility obligation. None is a later extension.

| construct | where it lives | what can narrow it, by default |
|---|---|---|
| **Effectful closures**: `U(F_Σ A)`, `A ⊸ F_Σ B`, functions passed and stored | K-FTY; D-REL's `U` and `⊸` clauses; K-ROWABS (03 §9.6) for row-generic ones | OQ-8 (quantifier placement); OQ-13 (R-NOROWVAR: a stored or passed callback has one fixed row; no first-class row-generic value, no polymorphic recursion across rows) |
| **Effectful generators**: `Yield` as a control effect handled by a site, stored generators as `ν` codata | K-HND, K-NU, L-YIELD; K-SHALLOW (03 §9.7) | OQ-26 (shallow handlers, R-DEEP) |
| **Effectful recursion**: a recursive group as the bounded fixed point of a generator, at a row | K-FIX, L-FIX | OQ-14 (recursion through a site, R-STATIC), OQ-15 and OQ-67 (a recursion whose body loops is handled by K-HDIV, whose lift R-HDIV defers), OQ-31 (bounded recursion, R-NONEGREC) |
| **Effectful iteration over finite data**: folds over `μ` data and counted loops whose algebra or step performs, resuming operations included | K-FOLDΣ (03 §9.13), L-FOLD | OQ-62 (R-PUREFOLD: algebras and steps pure); `foldImm[Σ]` also R-T1, R-CLOSEDOP |
| **Stored continuations**: `κ` stored, resumed later, cancelled | K-KONT, K-GEN, K-CANCEL, L-W, L-C | OQ-28 (how a stored `κ` is bounded, K-GEN's two options); OQ-31 (a handler storing its own continuations, R-NONEGREC) |
| **Continuations that hold borrows**: `κ` captured while a lend opened inside it is open | D-STOP, D-W's `σ`, T-FRAME, L-BOR's resuming half | OQ-2, OQ-9, OQ-10 (R-T1); OQ-56 (an operation whose type mentions the lend, R-CLOSEDOP) |
| **Several effects at once**: nested handlers of different effects, the reconciler chain `timeout \|> retry \|> log \|> kube` with a fallible `kube` | K-ROW (sums), L-SUM, L-HFWD, K-HDIV; the chain as a program, 08 §9.1 | R-HDIV defers the lift of a handler spanning observations of the reconcile loop (OQ-67); R-NOROWVAR makes the generic `timeout`/`retry` separately checked copies per row (OQ-13); R-PURESWAP with OQ-20 makes a fallible `kube` a handled control effect rather than a capability (OQ-1, OQ-19). Per-observation handling is not restricted (§4, row U5) |
| **Asynchrony**: `suspend`, `spawn`, a scheduler | L-ASYNC (06 §4); the async program, 08 §9.2 | OQ-61 (R-NOSELFROW: `spawn`'s parameter names the `Async` row); OQ-7 (R-FINAB: a scheduler cannot finalise its parked queue around an outer affine or abortive operation); OQ-60 (a deep-handler scheduler stores its own continuations, R-NONEGREC); OQ-27, OQ-28, OQ-46 |
| **Operations that perform their own effect**: `spawn`, `fork`, an `ask` answering a computation of the same effect | K-SELFROW (03 §9.12) | OQ-61 (R-NOSELFROW) |
| **Cancellation**: uninterceptable, finalising the cancelled region LIFO | K-CANCEL, L-SIGNAL, L-W, T-FIN | OQ-21 (finaliser policy) |
| **Errors as an abortive effect**: `raise`, ordinary handlers, no second error path | K-RAISE, L-EXC, L-ALG0 | OQ-24 (owned payload, R-NOOWNERR) |
| **Borrows across effects**: a borrow whose callback performs, at every `TableOK` row | K-BOR, L-BOR | R-T1, R-FINAB |
| **Answering effects as comodels**: capabilities, state access, fallible capabilities | K-COMODEL, K-CAP, K-SWAP, K-SWAPΣ (03 §9.11), L-STATE, L-TENSOR | OQ-1, OQ-19, OQ-20 (R-PURESWAP: a capability's callee is pure, so a capability cannot fail) |
| **Divergence**: any function may diverge, if its type says so; handled around, per observation or across observations | K-DIV, K-NU, K-HDIV (03 §9.2), L-DIV | OQ-15 (its kernel reading); OQ-63 (under (b), `ewpP_W` as a second wp family); OQ-67 (K-HDIV's obligation, R-HDIV) |
| **Multi-shot**: the `unr` qualifier | K-KONT, L-P | OQ-16 (kept only if free) |
| **Host effects**: I/O as per-effect capabilities, allocation as an effect | K-HOST, K-ALLOC (03 §9.5) | OQ-30 (row entry or capability); OQ-68 (K-ALLOC's obligations; R-ALLOCORACLE defers the lift) |
| **Operations that take computations** (scoped, higher-order operations) | K-SIG (thunk parameters, as built), K-SCOPE (03 §9.1, scoped) | OQ-12 (decision 57 puts scoped operations out of scope; R-FO), OQ-59 |
| **Handlers into any computation type** | K-CARRIER (03 §9.3) | OQ-37 (R-RETCARRIER) |
| **Answers that borrow handler state** | K-BORANS (03 §9.4) | OQ-29 (R-NOBORANS) |

### 3.3 Outside the proofs

Outside the proofs **by design** (§4, row U12):

- **Externs.** An extern is a named hypothesis with a semantic-type contract: "a value `v` at
  resource `ρ` implements `extern name : A` when `vC true A ls δ v ρ`. Externs are named
  hypotheses, not rules" (`SPEC.md:746-748`) [read]. Their end-to-end theorem quantifies over
  every implementation meeting the contracts (`externs_every_run`, `Core/Stdio.lean:622`;
  `io_every_run`, `:694`) [Lean]. In the effect calculus an extern is a host co-operation of a
  host comodel (K-HOST); its contract is its entry in `opTable` (OQ-30).
- **`unsafe`.** "`unsafe` is an extern whose body we compile" (decision 27,
  `docs/decisions.md:94-101`) [read]: safe code meets unchecked code only at a trusted boundary
  with a semantic-type contract. At the surface the user marks the smallest subterm the checker
  cannot type with `trust e`, read as "`e` is in the every-allocator relation at the expected
  type", a named hypothesis (memory record `trust-not-assurance-ceremony`) [user].
- **The allocator and the compiled code.** "The allocator is not an extern: it is part of the
  compiled runtime, trusted against its written specification" (`SPEC.md:753-754`); "That the
  compiled lowering behaves as the model is tested, not proved" (`SPEC.md:885`) [read]. Whether
  the effect lowering's correctness is a theorem is OQ-23.
- **Host handles** (file descriptors, streams): not memory, so adequacy says nothing about them
  (`SPEC.md:883-885`) [read].

Nothing else is outside the proofs. In particular no effect, handler or continuation construct
is trusted.

---

## 4. The user's decisions, at their strength

Each row records the user's position in the user's words, its source, and its strength as the
user gave it. A preference stated as "not without a good reason" is a default, not a ban
(memory record `defaults-not-prohibitions`); "not now" is not "never" (memory record
`not-now-is-not-never`). Rows marked **decided** are recorded as decided by the user; the rest
are defaults or preferences, and even decided rows are open to the user.

| row | position | the user's words and source | strength | how the specification applies it |
|---|---|---|---|---|
| U1 | **The actual calculus, a full specification first** | "Make sure the agents are building the actual effects calculus not an approximation of it." "We need a full specification before we start any kernel work, with any open questions carefully called out and boxed." (2026-10-03; memory record `effect-calculus-spec-first`; #290) | decided | this specification; §1.5; §7; no kernel effect work before the specification is complete |
| U2 | **The structure** | sign-off of the audit's structure (`Sig`, models and comodels, kernel handler laws, one world `W`, row-generic borrows) with the critic's corrections (2026-10-03; memory record `effect-calculus-spec-first`) | decided | 00 §1, §3, §6; 00 §0.3 |
| U3 | **Effects are core** | "I want effects to be core to the language, we aren't going to be able to implement them correctly with sugar, and we need to build them on a mathematical foundation backed by the literature." (2026-09-30; memory record `effects-are-core`) | decided; supersedes decision 48's elaboration-only reading | §3.1: effects have kernel formers, rules and relation clauses |
| U4 | **All or nothing; no built-in control constructs** | rejected "capabilities as the only extensible mechanism, plus a fixed set of built-in control constructs (exceptions, generators)": "i hate sort of version B, that just ends up with us in the 'Exceptions suck and are hard to reason about' territory"; half-implemented user-definable effects would be "constant friction" (2026-10-02; memory record `effects-are-core`) | decided (rejection) | §1.5; §7 item 7 |
| U5 | **Several effects at once** | nested handlers for different effects, the reconciler chain `timeout \|> retry \|> log \|> kube`, "need to work, full stop" (2026-09-30; memory record `effects-are-core`) | decided | K-ROW, L-SUM, L-HFWD, K-HDIV; the chain is a program (08 §9.1), written with fallible Kubernetes calls. A reconciler is a long-running loop, a div computation, read as `Loop_Σ` codata (K-DIV). Handling each reconcile pass, one observation, is unrestricted. A handler that spans observations (a timeout over the whole loop, a retry that restarts it) is K-HDIV, in the calculus; its lift is deferred by R-HDIV until OQ-67's obligation is proved. The R ids that restrict U5 by default: R-HDIV (OQ-67), R-NOROWVAR (OQ-13: `timeout`, `retry` separately checked per row), R-PURESWAP (OQ-20: a fallible `kube` is a handled control effect, so it appears in the row, OQ-1). OQ-15, OQ-67 and OQ-20 are raised in priority for that reason |
| U6 | **Effect handling is erased** | "Part of 18 needs to be effect handling is erased." Refinement: the criterion is cost parity with the hand-written direct-style program, "never 'always a direct call'" (2026-09-30; memory record `effect-handling-is-erased`; #18) | decided (requirement) | T-LOWER, L-TAIL, L-ALG0; OQ-23 for whether it is a theorem; OQ-42's default (three constructs of the calculus not lowered) restricts it, recorded as such |
| U7 | **No function colouring is the lead axis** | the one axis on which borrow-core should be clearly better than Rust: "async, errors, generators and other control effects as one mechanism" (2026-09-28; memory records `lead-axis-no-coloring`, `no-function-coloring`) | decided (priority) | one mechanism; higher-order code generic in its callbacks' rows (K-BOR, OQ-13) |
| U8 | **Laws first** | "I think we basically need to find the laws that we have to implement instead of trying to wing it." (2026-10-02; memory record `laws-first`) | standing instruction | 00 §0.2 item 4; 06; every construct has a law entry |
| U9 | **Errors are a control-flow effect** | "error is a control flow effect full stop" (2026-09-30; memory record `errors-are-control-flow-effect`; #168) | decided | K-RAISE, L-EXC; no value-level error path |
| U10 | **Cancellation is not interceptable** | user decision after the machine-checked `prog_stuck` (#191): "handlers inside the cancelled continuation are dead"; interceptable cancels rejected (2026-09-30; memory record `errors-are-control-flow-effect`) | decided | K-CANCEL, L-SIGNAL |
| U11 | **Multi-shot only if free** | "we also don't need multishot unless we get it for free"; "it's worth pursuing why we can't have multishot, but it's not a blocker" (2026-10-02; memory record `multishot-only-if-free`) | priority, not a ban | OQ-16; laws proved at `lin` and `aff`; `unr` kept only at no cost; the reason is a side question off the critical path |
| U12 | **Externs and `unsafe` outside the proofs** | decision 27 (`docs/decisions.md:94-101`); `trust e` at subterm granularity (2026-09-28; memory record `trust-not-assurance-ceremony`) | decided | §3.3 |
| U13 | **Div is an effect; totality is not a goal** | "Div should be an effect." (memory record `div-is-an-effect`); "i don't really care about totality in general unless we need it for something specific, it's really just an artifact of the borrow calculus that we can do it at all." (2026-10-01; same record); decision 35 (`docs/decisions.md:174-184`) | decided (div); preference (totality) | K-DIV, OQ-15; T-TOTAL kept, not a design driver |
| U14 | **Current state is not design** | "just because we have done something a certain way, that does not mean it was the result of a careful design decision, or that it is locked in." (2026-09-30; memory record `current-state-is-not-design`) | standing instruction | §1.5; no construct scoped to today's limits without a named restriction |
| U15 | **Mechanism before syntax** | "i don't want to do any sugar right now because i feel like starting with surface syntax caused the agent to think the syntax was what we wanted." (2026-09-30; memory record `mechanism-before-syntax`) | standing instruction | surface spellings only in 08, as the elaboration's source, provisional |
| U16 | **Threads are required eventually** | "we obviously need them", not now; never call them out of scope (2026-09-29; memory record `threads-are-required`) | requirement, later | OQ-18: each thread-facing choice (sum or tensor, handler state, cancellation) records what threads would change |
| U17 | **Our names, not Rust's** | "As an aside i don't like using the rust names for these things." (2026-10-02; memory record `own-names-not-rust`) | preference | constructs named from modes and structure; Rust only as comparison |
| U18 | **Deep before shallow; unknowns first** | "I just don't want to get in the trap of implementing shallow solutions and thinking we can patch them later" (2026-10-01; memory record `deep-before-shallow`); "I'd like to focus on the hard/unknown parts first" (2026-10-02; memory record `unknowns-first`) | standing instruction | 00 §0.2 item 5; OQ-9's probe first; laws stated over `W` (OQ-11) |
| U19 | **Recursion is the fixed point of a generator** | "recursion is an effect was more a pretty idea than a hard req." (2026-10-01; memory record `structured-recursion-only`); decision 59 (`docs/decisions.md:744-772`) | decided (current) | K-FIX, L-FIX; layers transform the generator |
| U20 | **Alloc and I/O are effects** | "alloc _is_ an effect, we already talked about that" (memory record `alloc-is-an-effect`); I/O a bundle of per-effect linear capabilities, ambient only in `main` (memory record `io-is-a-bundle-of-effects`; decision 30, `docs/decisions.md:121-130`) | decided (alloc as an effect; tracking unbuilt) | K-ALLOC (03 §9.5) in the calculus; OQ-30 the presentation (row or capability); its lift waits on OQ-68, R-ALLOCORACLE until then, a restriction of this decided position |
| U21 | **Runners: not the user-facing mechanism; the BoLo-world-as-runner architecture open** | "Runners (Ahman & Bauer) are OUT" as the user-facing effect mechanism; revisited 2026-10-02: "a whole BoLo world is one big comodel, a runner, inside a lawful local effect calculus" called "kind of genius", "promising, not yet decided"; "Don't cite 'runners are a dead end' against it." (memory record `effects-are-core`) | decided (no user-facing runners); open (architecture) | OQ-19; OQ-34 |
| U22 | **Kernel-level equations** | "Out of scope: kernel-level *equations* (a binary relation on BoLo's carrier, ν/op over moded contexts, η as an equation, optimiser correctness). They are optional and don't get pursued unless they become necessary for safety." (2026-10-02; memory record `effects-are-core`). The sign-off of 2026-10-03 asks for handler laws "stated and proved over the KERNEL relation" (U2) | the binary half: optional; the unary half over the kernel: decided | OQ-4, whose default (b) agrees: every law stated, its unary half proved over D-EWP, its binary half marked |
| U23 | **The hard stop on tier-2 regress** | "My concern is going to be that one of that finite lists itself has a regress so we should make that a hard stop." Refinement: "If the new work is n+1 and we are done, it's fine. If it's 3 and then 4 and then 5, no." (2026-10-02; memory record `hard-stop-on-regress`). The sign-off's correction: #285 and #287 were user-directed continuations, so tier 2 did not halt by rule (00 §0.3 item 2) | standing rule; its application under this specification is OQ-33 | §5.4; T-FRAME's "depth handled by one induction" |
| U24 | **The paper is not wrong** | CLAUDE.md §2; memory record `the-paper-is-not-wrong` | standing rule | 00 §0.2 item 3 |

**Hardened text to avoid.** Decision 48 records "Effect rows never enter the core" as the
user's decision (`docs/decisions.md:604-608`). The user: "I never said, btw that row doesn't
enter core. You have a habit for turning not now into never." (2026-10-02; memory record
`not-now-is-not-never`). Rows enter the kernel in this calculus (K-ROW). Decision 57's "no row
variables in the kernel (Option 2)" (`docs/decisions.md:707`) is recorded as the user's decision
of 2026-10-01 and is the default of OQ-13, not a ban.

---

## 5. Tier 1 and tier 2 as properties of the calculus

"Tier 1" and "tier 2" are not feature sets. They name one property of the model, and the
calculus is stated in full under either; what differs is whether a named restriction (R-T1) is
in force.

### 5.1 Stops and the lends open at a stop

A **stop** of a table `Tb` is a final non-value term `t` that `Tb` admits. For `opTable T`
(`Core/EffDefs.lean:157-167`) [Lean] the stops are

```
  t = K[perform_{n,i} v]   with  K.HasHnd n = false,  T n i = some en,  en.abort = false   (resuming)
  t = K[raise_{n,i} v]     with  K.Catches n = false, T n i = some en,  en.abort = true    (abortive)
```

`wpG ls e Q` runs `e` from a frame `fρ` with `TW fρ ps (rsOf ls)` to a final term `t` with
`TW fρ'p ps' (rsOf ls')` (`Core/EffDefs.lean:27-40`) [Lean]. The **lends opened by the run and
open at `t`** are

```
  open(t) ≜ (ps' \ ps, ls' \ ls)
```

the 6.64 frames the run created and did not end, and the tagged records of their lineages in `ls`
(05 §0). A 6.65 lend open at `t` leaves no trace in `ps` (`TW.mutFold`, `Core/World.lean:135-144`)
[Lean]; how it is recorded is OQ-44.

### 5.2 The property T1

```
  Definition (T1 at a stop).    A stop t of a run satisfies T1  iff  open(t) = (∅, ∅).

  Definition (T1 for the calculus).
    The calculus has property T1  iff  for every Δ; Γ ⊢ e : F_Σ A, every W, every allocator,
    every stop t that a run of e reaches satisfies T1.
```

T1 says: **no lend opened inside a computation is open at any stop of that computation.** An
abortive operation still crosses a borrow's scope under T1, because it crosses by unwinding:
the unwinding form of the borrow catches the `raise`, ends the lend (6.64's `immEnd`, or 6.65's
unfold), runs the source's finaliser and re-raises, so the stop of the whole has `open(t) = (∅,
∅)` (SPEC §19 *Theorems* item 3, `SPEC.md:2745-2760`) [read].

Today the model **imposes** T1 at every final term, a stop included:
`(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)` (`Core/EffDefs.lean:40`) [Lean]. That
clause is where T1 comes from (`docs/effects-audit.md` §1, item 4) [read]. The typing side meets
it by admitting only rows of abortive, named operations with closed argument types at a borrow's
callback (`Row.Unwind`, `Core/EffBorrow.lean:133-134`) [Lean], and SPEC §19 states that
"non-abortive control operations cannot cross a borrow" within that entry (`SPEC.md:2770-2771`)
[read].

### 5.3 The two tiers

```
  Tier 1  ≜  the calculus with R-T1 in force:
             D-STOP is today's clause; at every stop σ = []; the relation is the σ = [] instance
             at every stop; K-BOR's callback row is restricted to rows whose resuming
             operations do not cross the borrow.

  Tier 2  ≜  the calculus with R-T1 lifted:
             D-STOP relativised; a stop may have open(t) ≠ (∅, ∅); the open lends are σ, handed
             to the table; the table's continuation obligation (D-SHARE, D-KAP, D-OWED) closes
             them on every path the continuation can take: resumed and run to a value,
             cancelled, dropped at an abortive operation, resumed by a handler between lenders.
```

The calculus specified is tier 2. Every construct is stated without R-T1, and R-T1 is marked
where it applies (00 §7.2). Programs that need tier 2, by construction:

- a generator that yields while it holds a view of a buffer it borrowed;
- an asynchronous read into a local buffer: the read suspends while the buffer is lent to it
  (memory record `hard-stop-on-regress`, "self-referential suspension, e.g. an async read into a
  local buffer");
- a stored continuation that captures a borrow and is later resumed or cancelled;
- a handler that sits between two lenders (also OQ-3, R-MID).

The first two also need an operation whose type mentions the lend: the read passes the lent
`Mut 'x Buf` to the operation, and the generator answers `Imm 'x T`. R-CLOSEDOP excludes both
(OQ-56), separately from R-T1; lifting R-T1 alone does not admit them.

Programs that tier 1 already covers: abortive operations inside any number of borrows (errors,
`Exhausted`, cancellation), answering operations inside a borrow (calls on a capability inside
the callback, SPEC §19 *Theorems* item 3), resuming operations whose captured context opens no
lend.

**Equivalence to be shown.** That the model reading (`σ = []` at every stop) and the typing
reading (callback rows restricted) coincide for the kernel's rules is not proved. It is
mechanical in every rule but one; the step most likely not to be mechanical is `[handle]` at a
handler inside a borrow's callback, whose resuming clause's `κ` holds no lend of the borrow
only if the borrow's frame is outside the handler. Not derived; no obstruction verified.

### 5.4 Which tier is implemented first

OQ-2 decides what the first kernel lift implements. OQ-9 (open frames handed to a continuation
that is cancelled, dropped or resumed between lenders) is the first unknown, and its first
probe is one Lean configuration at `[handle]` + cancel. OQ-8 decides where the future-world
quantifier sits. The user's hard-stop rule (U23) bears on this; how it applies under this
specification is OQ-33.

Whatever the tier, one property of the specification holds: **a result over the lend stack is
proved once for every depth**, by one induction from `n` to `n + 1` over `σ`, never one lemma per
depth (U23's refinement; T-FRAME, "depth handled by one induction", 00 §5.1).

---

## 6. Named restrictions as restrictions of the full calculus

Each restriction is the default of an open question (00 §7.2). The construct is in the
calculus in full; the restriction is what holds until the question is settled.

| R | the full construct | the restriction | lifted by |
|---|---|---|---|
| R-T1 | a borrow at any `TableOK` row; a stop with open lends handed to the table | no internal lend spans a stop; only abortive operations cross a borrow's scope | OQ-2, OQ-9, OQ-10 |
| R-MID | a handler at any position relative to lenders | no handler between two lenders | OQ-3 |
| R-FINAB | finalisers and unwinding forms at every `TableOK` table | at abortive rows only | OQ-7 |
| R-FO | operations whose parameters may be computations (scoped operations) | no operation takes a computation | OQ-12 |
| R-NOROWVAR | effect polymorphism as an object of the calculus (K-ROWABS) | rows a meta-index: each copy at each row a separately checked derivation, related by no theorem except a renaming (T-REN relates copies that differ by a permutation of names, not copies at different signatures); no first-class row-generic value; no polymorphic recursion across rows | OQ-13 |
| R-STATIC | names of any kind, including generative instances; recursion through a site | static names per site; no recursion through a site | OQ-14 |
| R-HDIV | a handler around a div computation, per observation and spanning observations (K-HDIV), decided by U5 | the kernel lift implements the per-observation form and defers the spanning form until its obligation is proved | OQ-67 (with OQ-15's reading) |
| R-PURESWAP | a co-operation whose callee performs, including one that fails (K-SWAPΣ) | the callee is pure, so a capability cannot fail | OQ-20 |
| R-NOOWNERR | an abortive payload that owns a resource | the payload owns nothing | OQ-24 |
| R-NOBORANS | an operation that answers a borrow into handler state (K-BORANS) | no operation answers a borrow into handler state | OQ-29 |
| R-RETCARRIER | a handler into any computation type (K-CARRIER: `S ⊸ F_Σ R`, `C & D`) | carrier `F_Σ R`; other carriers by encoding | OQ-37 |
| R-CLOSEDOP | a borrow callback whose operations' types mention the lend or the site's lifetimes | closed operation types, free of the lend's variable | OQ-56 |
| R-ALLOCORACLE | allocation as an effect (K-ALLOC), as the user decided (U20) | the kernel lift keeps allocation the machine's oracle until K-ALLOC's obligations are proved | OQ-68 (presentation OQ-30) |
| R-NONEGREC | stored continuations of every shape, including a handler that stores or returns its own | no negative recursion through a stored continuation; bounded recursion; positive `μ`/`ν` | OQ-31 |
| R-DEEP | shallow handlers | deep handlers; step-wise handling by `ν` codata | OQ-26 |
| R-NOREL | a relevant qualifier (K-RELQ) | no relevant continuation qualifier | OQ-17 |
| R-EXACTQ | qualifier subsumption in `[sub]` | exact qualifiers | OQ-39 |
| R-NOSELFROW | operation types that perform their own effect (K-SELFROW) | no operation type mentions its own signature's row | OQ-61 |
| R-PUREFOLD | folds and counted loops whose algebra or step performs (K-FOLDΣ) | pure algebras and steps | OQ-62 |

The restrictions of the equational theory and the metatheory (R-ETALIN, R-INTERLIN, R-FUSETAIL,
R-LINRES, R-ADEQF1, R-ALGPLAIN) are listed in 00 §7.2; they narrow which laws and theorems are stated, not
which programs exist.

A section never writes the restricted form as the construct.

---

## 7. The checklist: not an approximation

08 validates the specification against these items, id by id (08 §8). Each item is a property
of the specification text and of the eventual kernel; a failed item is a defect, reported, not
routed around. The items have stable ids `C-1` to `C-12`.

1. **C-1. One signature object.** Every effect, answering or control, user-defined or host-provided,
   is a signature `E` (K-SIG) and enters a row `Σ` (K-ROW) as a named summand. No effect is
   described by a second signature form (today's frontend `EffSig` and kernel `Row` are two,
   `docs/effects-audit.md` §1, item 1).
2. **C-2. One interpretation.** Every row is interpreted by `⟦Σ⟧δ` and checked by `opTable ⟦Σ⟧δ`
   (K-INT, D-OPTAB). No construct is checked by a table of its own.
3. **C-3. Models and comodels of it.** A handler is a model of `Σ` (K-MODEL, D-MODEL, T-MODEL); a
   capability is a comodel of `Σ` (K-COMODEL, D-COMODEL, T-COMODEL); both meet the protocol
   of the same `opTable` entry. How answering and control handlers relate is OQ-1; whether a
   control handler is a borrow as an answering handler is (`handle_is_shift`,
   `experiments/HandlersAsBorrows/HandlersAsBorrows/Safety.lean:115`) [Lean] is OQ-3.
4. **C-4. Laws over the kernel relation.** Every L id has its unary half stated and proved over D-EWP
   at `W` (or at `σ = []` with its survival obligation, OQ-11), not over a sibling carrier. Its
   binary half is stated and marked under OQ-4.
5. **C-5. One world.** The relation, the laws and the metatheorems are stated at `W = (ρ, ls, σ)`
   (D-W). There is no other relation family, and `vC`/`cC` equal its `σ = []` instance by T-NIL:
   by definition at the clauses that read no extension, by a per-row proof at `U`, `share` and
   `KapRel` (OQ-58). The closing-obligation index `τ` beside `W` is recorded as a defect (OQ-57).
6. **C-6. One borrow per printed constant.** Each printed borrow constant is one kernel constant
   `bor_k[Σ]`, generic over its callback's row with `TableOK ⟦Σ⟧` (K-BOR, T-SUMOK); today's
   pure constants are the `Σ = ∅` instance and today's `*U` twins abbreviations. Frame lemmas
   are lifted once (T-FRAME).
7. **C-7. No construct recognised by name.** No effect, handler, operation or role is recognised by
   its name in the kernel or the elaborator; roles are found from types or structure, or
   declared (OQ-6).
8. **C-8. Every construct complete.** Every K id has syntax (02/03), statics (03), dynamics (04), a
   model clause or obligation (05), its defining laws (06) and a compatibility obligation (07),
   and a lowering class with the law that justifies it (08, T-LOWER).
9. **C-9. No step index, no new mechanism.** No definition uses a step index; no section introduces a
   relation family, twin constant or side mechanism beside `W` (00 §0.2 items 1-2).
10. **C-10. Every narrowing named.** Every place the calculus is narrowed by a default is one of the R
    ids of §6, cited at the construct, with its open question.
11. **C-11. Every kernel definition change has a SPEC entry.** D-STOP and every other changed or new
    kernel definition has the text of its SPEC entry before kernel work (00 §0.1).
12. **C-12. The user's decisions at their strength.** No row of §4 is cited at a strength stronger
    than its source.

---

## 8. Relation to SPEC entries and decisions

Which SPEC entries the calculus replaces, extends or keeps. 08 writes the SPEC entries the
calculus requires; this table is the scope of that work.

| SPEC | entry | fate | ids |
|---|---|---|---|
| §14 | Entry 13, divergence as an effect | **kept** as the default kernel reading (div as `ν` codata, `Loop`); **extended** by effectful observations (`Loop_Σ`, already in §19 *Divergence*, `SPEC.md:2693-2725`); a handler around a div computation is K-HDIV, in the calculus, its spanning form's lift deferred by R-HDIV | K-DIV, K-NU, K-HDIV, L-DIV; OQ-15, OQ-67 |
| §18 | Entry 17, effects and handlers | **replaced** in its kernel reading: answering effects defined by elaboration (decision 48) become comodels of a kernel `Sig` checked against `opTable`; §18's laws (`op_tail`, `op_answer`, `handle_fold`) become instances of L-STATE and L-TAIL; the surface stays in 08 as the elaboration's source | K-COMODEL, K-CAP, L-STATE, L-TAIL, T-ELAB; OQ-1 |
| §19 | Entry 18, native capture | **kept** as the as-built core and **extended**: rows become sums (K-ROW), the stop is relativised (D-STOP, a SPEC entry), the relation is re-indexed at `W`, the `*U` twins become abbreviations of K-BOR, the handler laws are stated over the kernel | K-OP … K-HND, K-KONT, K-CANCEL, K-STEP, D-STOP, D-REL, L-HRET, L-HOP, L-HFWD |
| §20 | Entry 19, recursion as an effect | **kept** where §21 keeps it (`bounded_fix`, `Exhausted`, the drivers, the budget); revised by §21 | K-FIX |
| §21 | Entry 20, the fixed point of a generator; closure conversion at the seams | **kept**: recursion as the bounded fixed point of a generator, layers as generator transformers, effectful code as `!` code with its environment passed | K-FIX, L-FIX; R-STATIC, R-HDIV |
| §22 | Entry 21, the affine closure | **kept**; its effectful `close` is under OQ-7 (R-FINAB) | K-NU; OQ-7 |
| §23 | Entry 22, non-strict outlives | **kept**; **extended** by an outlives reading at `U(F_Σ A)` or at a boxed continuation (OQ-28) | K-FTY, K-KONT; OQ-28 |

Decisions: 48 is superseded in its "handlers are defined by elaboration" reading (U3); 52 is
superseded by errors as an abortive effect (#168, U9); 53's acceptance (per-class laws on
elaborated terms) is replaced by laws over the kernel (C-4); 57 stands as the default of
OQ-12 and OQ-13; 58 stands as revised by 59; 59 stands. 08 records each.

---

## 9. Open questions

### 9.1 Questions this section carries

Boxed in [99](99-open-questions.md); cited here by id.

| id | question | tag | default | where it bites in this section |
|---|---|---|---|---|
| OQ-2 | Tier 1 or tier 2 first (audit Q2) | [user decision] | the first lift at tier 1 with R-T1; the specification stated without R-T1 | §5 |
| OQ-12 | Operations that take computations | [user decision] | decision 57 stands, R-FO | §3.2 |
| OQ-15 | The kernel reading of divergence | [user decision] [settle by proof] | codata; K-HDIV specified under both readings | §3.2, §8, U5 |
| OQ-16 | Is multi-shot free? | [settle by proof] [settle by literature] | keep `unr`, laws at `lin`/`aff` | §3.2, U11 |
| OQ-18 | Sum, tensor, and threads | [user decision] [settle by literature] | rows sums, disjoint capabilities tensor, cancel uninterceptable and finalising | §3.2, U16 |
| OQ-30 | Allocation and I/O in the calculus: the presentation | [user decision] | (b'): allocation a capability, I/O comodel capabilities | §3.2, §3.3, U20 |
| OQ-31 | The cut-offs that keep the relation step-free | [user decision] | keep all five (R-NONEGREC) | §2.4 |
| OQ-33 | How the hard-stop rule applies under this specification | [user decision] | applies to the milestone that lifts R-T1; one proof for every depth | §5.4, U23 |
| OQ-34 | Is the BoLo world itself a comodel? | [user decision] [settle by literature] | neither depended on nor excluded | §2, U21 |
| OQ-56 | Operation types that mention the lend, at a borrow callback | [settle by proof] [user decision] | R-CLOSEDOP | §5.3 |
| OQ-58 | Is Core the `σ = []` instance at `U`? | [settle by proof] | not claimed until proved | §1.2, §2.3, C-5 |
| OQ-60 | The async scheduler against R-NONEGREC | [settle by proof] [user decision] | scheduler over `Loop_Σ` codata | §3.2, U7 |
| OQ-61 | Operation types that perform their own effect | [settle by proof] [user decision] | R-NOSELFROW | §3.2, U7, U16 |
| OQ-62 | Folds and counted loops at a row | [settle by proof] [user decision] | R-PUREFOLD | §3.2 |
| OQ-67 | K-HDIV's proof obligation | [settle by proof] | construct specified; lift deferred (R-HDIV) | §3.2, U5 |
| OQ-68 | K-ALLOC's proof obligations | [settle by proof] | construct specified; lift deferred (R-ALLOCORACLE) | §3.2, U20 |

The audit's Q1-Q7 are OQ-1 to OQ-7: Q1 answering and control (OQ-1), Q2 tier (OQ-2),
Q3 handler extent (OQ-3), Q4 binary relation (OQ-4), Q5 EffModelRel (OQ-5), Q6 role
declarations (OQ-6), Q7 finalisers at a non-abortive table (OQ-7).

### 9.2 Questions this section raises

OQ-33 (how the user's hard-stop rule applies once the frozen tier-2 list is replaced by this
specification's register) and OQ-34 (whether the BoLo world is itself one comodel, the
heap-runner architecture) are raised here and boxed in 99.

---

## 10. Obligations of this section

| obligation | mark | the step most likely not to be mechanical |
|---|---|---|
| §5.3: the model reading of T1 (`σ = []` at every stop) and the typing reading (restricted callback rows) coincide for the kernel's rules | mechanical in all rules but one | `[handle]` inside a borrow's callback (§5.3) |
| §4: every row's strength matches its source | mechanical (a check of each quotation) | U22, where a 2026-10-02 statement and the 2026-10-03 sign-off speak to the same laws at different halves |
| §7: 08 checks each item id by id | mechanical | C-3, which depends on OQ-1 |

### Printed lemmas in the run-up not transcribed; unspent hypotheses; unused results (CLAUDE.md §5)

- **Printed lemmas in the run-up not transcribed at resuming tables:** `[TR]` 6.150 (with its
  freshness); 6.64 at an `Imm` table beyond `ewpTS_I_frameR`; 6.65's `↭` steps line by line
  (`docs/effects-audit.md`, "Unspent and untranscribed items"). Tier 2 (§5.3) depends on all
  three through T-FRAME.
- **Unspent printed hypotheses:** none spent here; this section proves nothing.
- **Unused uniqueness or functionality results:** determinism of the machine
  (`head_det_eff`, `Core/Steps.lean:596`) and determinism up to renaming (`freshRun_det`,
  `experiments/TwoRun/TwoRun/Fresh.lean:255`; `run_sim`, `experiments/TwoRun/TwoRun/Sim.lean:253`)
  [Lean] are not used in this section; they bear on OQ-4 through T-2RUN.
- **Not derived, no obstruction verified:** §5.3's equivalence.

---

## Sources

Read for this section:

- `docs/effects-calculus/00-structure.md`; `docs/effects-audit.md` §1, §7 and "Unspent and
  untranscribed items"; `SPEC.md` §1, §11 (externs, assurance), §18, §19 (*Names*, *Cancels*,
  *Divergence*, *Theorems*, *Baseline*, *Open*), and the section list of §14 and §20-§23;
  `docs/decisions.md` entries 1-2, 7, 27, 30, 35, 48-61.
- Kernel declarations cited `file:line` above.
- The user's memory records named in §4 (quotations as recorded there).
- The literature report on #235 (`gh issue view 235 --comments`), §8.5 and L2-L4, for the
  readings that ground §1.1's "a handler is a model, a capability is a comodel": Plotkin and
  Pretnar, LMCS 9(4:23) 2013, a handler is a model of the theory and handling the unique
  homomorphism out of the free model [via #235, marked P there]; Møgelberg and Staton, LMCS
  10(1:17) 2014, §8, a theory sits on a linear state `S` as a comodel, and a state access
  operation is the same data as a generic effect and an algebraic operation [via #235, marked P
  there]; Hyland, Plotkin and Power, TCS 357 (2006), sum and tensor, as restated by Ahman and
  Bauer, ESOP 2020, §3.1 [via #235]; a theory with a 0-ary operation has only the empty comodel,
  so the inclusion is answering ⊆ algebraic [via #235; PP08 via `docs/effects-tr/12-sources.md`].
- `docs/effects-tr/12-sources.md` §12.2-§12.3 for the marks of the sources above.

Named and not read for this section: Patterson, Mushtak, Wagner and Ahmed, PLDI 2022 (OQ-34).
