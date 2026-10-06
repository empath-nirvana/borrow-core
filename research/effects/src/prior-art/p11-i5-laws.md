# Prior art: P11 handler correctness and P7 / I5 the capture laws

This chapter surveys the literature for one System A property and one interaction property, and ends in a menu of options with their trade-offs. It does not recommend one.

- **P11, handler correctness.** A handler means what its clauses say. In the literature that has two readings: the handler is a model of the operations' theory and handling is the induced homomorphism out of the free model (initiality), and the unary laws that follow (return, operation, forwarding, the tail-resumptive law, graded algebraicity). Fusion, Discard/Copy/Swap and representation independence are binary.
- **P7 / I5, the capture laws.**
  - **β**: freeze then resume is the identity.
  - **η**: the forwarding handler is the identity.
  - **Hiding**: a body cannot observe a handler's state except through its operations. This is BoLo's anti-frame ([TR] 6.66) read relationally.

**Decisions that bound the menu** ([decided constraints](../decisions.md)):
- nothing breaks the borrow calculus, meaning its guarantees, not BoLo's text;
- the core is linear, and discard is an explicit cancel;
- cancellation is what SPEC §19 builds (decision 62);
- handlers are deep (decision 62);
- multi-shot is ignored (decision 63), so it appears below only where a source needs it;
- errors are `raise`; divergence is codata;
- effect handling is erased (a call, a branch, or a state machine);
- no function colouring;
- **binary laws are optional unless safety needs them** (2026-10-02);
- row variables (decision 62) are an implementation choice, not a goal;
- no step-indexing (decision 7).

**Verification marks.**
- **[read]**: quoted from the primary PDF, fetched and read for this chapter, or from our Lean/docs as they stand on `main` (borrow-core) and `targets` (borrow-core-targets).
- **[relayed]**: taken from a sibling prior-art chapter, our survey, or a secondary source. Not re-read here.
- **[unverified]**: could not be checked.

Theorem numbers are those printed in the version named in the sources list.

---

## Menu at a glance

The options fall along four independent axes:
- **H.x**: what "the handler is correct" is stated as (initiality, P11);
- **F.x**: the *form* every law is stated in (unary reduction, unary program logic, run-level, contextual);
- **K.x**: the capture laws (β, η, hiding; I5);
- **Z.x**: which laws the erased lowering consumes, and whether lowering correctness is a theorem (OQ-23).

"Ours today" marks where `experiments/Targets` and Core sit (§6).

| # | option | statement shape | what it buys | main cost | literature | ours today |
|---|---|---|---|---|---|---|
| H.1 | **Reduction equations only** (empty theory) | handling reduces as the induced homomorphism does: return, catch, abortive catch, deep resume, cancel, finalise, each in every context up to store-free steps | every handler is correct by Plotkin–Pretnar's own remark; no model theory needed | says nothing a program logic can use about *what* a handler computes | Plotkin–Pretnar Def 4.5 and "If the effect theory is empty, then any handler is correct" | **A's S4 `HandlerSem`**; OPEN at our instance (`handlerSem_ourInst` not built) |
| H.2 | **Model rule in the program logic** (unary initiality, existence half) | if the clauses meet the protocol of the handled row against the outer row, the handled computation meets the outer protocol | the compositional `[handle]` rule; what `fundamentalC` already uses | the world's `ewp` at resuming tables (W) | Hazel's handler rule; Plotkin–Pretnar's induced homomorphism | `ewp_handle` (Core σ=[]); device `P11 = HandleCompat ∧ RedLaws`, PROVED AT σ=[] (`p11_core`) |
| H.3 | **Uniqueness half** stated | every homomorphism out of the free model agrees with the handler | η for handlers, and fusion, follow from it | needs a free model as an object of the calculus; ours is the machine | Plotkin–Pretnar §1.1 "unique homomorphism"; Ahman–Bauer Prop 3 | `handle_unique` (CoeffectsStrict, first-order `write` only, Core σ=[]); TR §13 T13.8 by hand |
| H.4 | **Denotational initiality via a sibling model** | handling *is* the fold `Tree.hnd`; laws are equal denotations | every algebraic law at once (SIB) | a bridge from Core to the model, which does not exist | Plotkin–Pretnar §4; Kammar–Lindley–Oury | EffModelRel (SIB, no bridge) |
| F.1 | **Unary reductions** (`PureJoin`) | `c ⇝* · ⇜* c′` by store-free steps | cheap at a deterministic machine; no relation | cannot state laws whose two sides are not joinable (tail-resumptive with an effectful clause, η, fusion, hiding) | Kammar–Lindley–Oury Fig. 4 (rules as laws) | S4 |
| F.2 | **Unary in the world** (a Kripke `ewp` lemma per law) | `ewpW … lhs ⊣⊢ ewpW … rhs`, or one direction | laws usable in the fundamental property; survives the re-index to W | one lemma per law per world; the world at resuming tables is unbuilt | Hazel (§4.2); our `I5beta`, `AntiFrameW`, `RedLaws` | device `I5`, `P11`; PROVED AT σ=[] (`i5_core`, `p11_core`), `I5beta` at every world |
| F.3 | **Run-level, closed** (two closed configurations, same runner, same observable runs) | `∀ R, Observes R lhs = Observes R rhs` at closed, typed programs; no context quantifier | the tail-resumptive law and the lowering's per-class correspondence, without a binary relation | only closed programs; every law needs its own context-closure argument to be usable inside a program | Lexa Thm 1 and Zero Thm 1 (simulation); Hillerström Thm 4.8 | `A.UnaryLaws` (`TailLaw`, `AlgLaw`, `EtaHold`; `EtaLin`), beside done, in every evaluation context of a reached configuration: STATED, not proved; A₃ `LoweringCorrect` has this shape for the whole lowering |
| F.4 | **Contextual equivalence** (binary) | `CtxEquiv` at A's contextual approximation, or Core's | every law, fusion and hiding included; the literature's standard | a binary relation or a direct context argument, at no step-index; out of the first pass | Biernacki et al. 2018 Thm 10; Plotkin–Pretnar §5 | **A₂ `HandlerLaws`**, Core's `Laws`: stated, OPEN |
| K.1 | **β, unary** | `ewp (handle H K[w]) ⊢ ewp (resume κ w)` | deep resume, the state machine's re-entry | none beyond today | TR T13.2; Plotkin–Pretnar H-op inequation | `I5beta` PROVED at every world; S4 deep resume |
| K.2 | **β up to fresh internal lifetimes** | as K.1, with the frozen lifetimes instantiated fresh beneath the resumer's | tier 2 under ghost end (I2 M1) | the freeze binder (I2 T3); `NotVDenNaturalArises` open | Staton's ν; TR §13.0 ("needs L14.4, open (O5)") | `FreezeBinder` beside done, OPEN |
| K.3 | **η, renaming form** (binary) | `handle (fwd n→n′) e ≡ e[n′/n]` | the forwarding handler is a no-op, the lowering may delete it | binary; at an affine operation a syntactic forwarding clause drops the frozen destructors | Plotkin–Pretnar "`M to x. N ≃ M handled with {} to x. N`"; Kammar–Lindley–Oury open handlers | Core `CapEta`: stated, OPEN; A₂ omits η; unary under L13.5's restriction: `A.EtaLin` (F.3), STATED |
| K.4 | **η with a continuation-holding frame** | K.3 with a clause written by `M to^k y. N` (TR D13.7), whose unwind cancels `k` | η at affine operations, cancel forwarded | a new former and its compatibility lemma | none published; TR T13.8(b) by hand | not in Core; L13.9 PAPER; unary at A: `A.EtaHold` (F.3), the frame written with A's `thenT`, STATED, beside done |
| K.5 | **Hiding, unary** (6.66 at W) | the anti-framed body meets `ewp` from the view `ℓ ↦ M_α …` | handler state behind a lend at resuming tables (P10 X.2) | 6.66 at a suspending table (TR "part of O8") | Hazel framing; Møgelberg–Staton linear-use state | `AntiFrameW` in the device: PROVED AT σ=[], OPEN at W |
| K.6 | **Hiding, binary** (representation independence) | two answering handlers whose states simulate are equivalent | changes of handler-state representation in the lowering; library abstraction (P12) | a relational interpretation of state, or relations in worlds; no step index | Ahmed–Dreyer–Rossberg 2009 [relayed]; EffModelRel `hnd_sim` | Core `Hiding`/`RepInd`: stated, OPEN; `hnd_sim` (SIB) |
| Z.1 | **Per-class laws plus corpus counts** (decision 48's shape, OQ-23 (a)) | each lowering class justified by one law; zero cost by counts | no compiler proof | the laws are needed anyway; "true by definition" no longer holds | Koka, Ante (unproved) | named-only (`LowClass`) |
| Z.2 | **Compiler correctness by forward simulation** (OQ-23 (b)) | source steps simulated by target steps up to a relation; deterministic target gives both directions | `LoweringCorrect` as stated; consumes only unary laws (F.1/F.2) plus typing | a simulation relation over three lowering classes and a state-machine transformation | Lexa Thm 2, Zero Thm 1, Xie et al. Thms 8, 11, Hillerström Thm 4.8 | **A₃ `LoweringCorrect`**: stated, out of the first pass |
| Z.3 | **Laws as source rewrites, then a naive lowering** | lowering = rewrite by binary laws (tail-resumptive, fusion), then a fixed translation | each optimisation is one law | needs F.4 for every rewrite | Kammar–Plotkin 2012 (effect-dependent optimisations) | not used |

**Where the target sits (§6).** P11 in done is H.1 in form F.1 (S4), plus forwarding as the structural fact `KontLaws`. The device adds H.2 (`HandleCompat`) and F.2 (`RedLaws`). I5 in done is S4's deep resume (K.1); the device adds K.1 at every world and K.5 at σ=[]. The tail-resumptive law, algebraicity and η have **no unary form in done**. Their unary forms are stated **beside done**, in form F.3, as `A.UnaryLaws` (`TailLaw`, `AlgLaw`, `EtaHold`) with η's alternative `EtaLin`: STATED, not proved; membership in done is a choice on axes H, F and K. Their binary forms are A₂'s (tail, algebraicity) and Core's `Laws` (F.4, η as `CapEta`), out of the first pass. A₃ is Z.2's statement, with OQ-23 open.

---

## 1. Canonical statements and their variants

### 1.1 Plotkin & Power, *Algebraic Operations and Generic Effects* (ACS 11, 2003) [read]

**Algebraicity** is naturality in the evaluation context: "naturality in the Kleisli category means that the operations commute with evaluation contexts" (§1). In §3: "In programming language terms, the condition of the definition is that evaluation contexts E[−] commute with the computational effects induced by the operations. For example, in a nondeterministic programming context … E[M or N] ≡ E[M] or E[N]". Definition 1 states it as a coherence square on `αx : (Tx)^v → (Tx)^w`.

**Generic effects**: an operation and its generic effect `perform op v` are interdefinable (abstract: "to give a generic effect is equivalent to giving an algebraic operation"). Our kernel's `perform` is the generic form; algebraicity is then the associativity of bind at `perform`, which is how A₂'s conjunct is written (§6).

### 1.2 Plotkin & Pretnar, *Handling Algebraic Effects* (LMCS 9(4:23), 2013) [read]

**Initiality.** §1.1: "h(M) = M handled with {raise_e() ↦ M_e} … is the unique homomorphism (a map preserving operations) from A+exc to M that extends the map in₁". §1.2: "Note that all the homomorphisms from the free model to a model on a given carrier are obtained in this way. So Benton and Kennedy's handling construct is the most general one possible from the algebraic point of view." Prop 4.3: "The functor U : Mod_T → Set has a left adjoint F".

**Correctness.** Def 4.5: "A handler Γ | K ⊢ H : C handler is correct at c if the op_H(c) are all total and the set U⟦C⟧ together with the op_H(c) forms a model of T." Directly after: "If the effect theory is empty, then any handler is correct, but, in general — and unsurprisingly — correctness is undecidable … even the decidability of the correctness of very simple handlers is a Π₂-complete problem."

**The unary laws, as printed (§5).** Two Kleene inequations "that state the universal properties of the induced homomorphism: it extends the inducing map on values, and it acts homomorphically on operations":
- `return x handled with H to x : A. N ⊒ N`;
- `op_y(x′ : β. M) handled with H to x : A. N ⊒ M_op[x′ : β. M handled with H to x : A. N / k]`.

Algebraicity at sequencing: "`op_V(x : α. M) to y : A. N ≃ op_V(x : α. M to y : A. N)` … This equation holds as sequencing is defined using the homomorphism induced by the universality of the free model".

**η, in its printed form.** "`M to x : A. N ≃ M handled with {} to x : A. N`, stating that sequencing is equivalent to the special case of handling in which all operations are handled by themselves." This is the forwarding handler being the identity.

**What is not a law for general handlers.** "There are other equations for exception handlers, given by Benton and Kennedy, and Levy … It turns out that these equations fail for general handlers, but do hold for particular classes of handlers".

### 1.3 Kammar, Lindley & Oury, *Handlers in Action* (ICFP 2013) [read]

- **Free theory:** "in this paper we always take the equational theory to be the free theory, in which there are no equations." Same position as our OQ-22 default.
- **The laws as reduction rules** (§3.2, Fig. 4): "The hoist.op-rule hoists operation applications through hoisting frames. Its purpose is to forward operation applications up to the nearest enclosing handler". handle.op: "A handled operation application … reduces to the body of the operation clause … with the parameter V substituted for p and the continuation λx.M substituted for k. Any further operation applications should be handled by the same handler H. Thus, we wrap H around M." This is deep resume as a rule. Theorems 1 (termination) and 2 (type soundness) are proved over these rules.
- **Forwarding as a default clause** (§3.3, open handlers): H_op "is also defined as λp k. op p (λx. k x) for any other operation op. This means that any operation that is not explicitly handled gets forwarded." The forwarding clause is the η-handler's clause.
- **Shallow handlers:** "(shallow-handle.op) … which does not wrap the handler around the continuation."

### 1.4 Kammar & Plotkin, *Algebraic Foundations for Effect-Dependent Optimisations* (POPL 2012), via Kammar's thesis [read: thesis; paper relayed]

Equation (11.1), the Discard optimisation, is graded by effect sets: `Γ ⊢_ε M : F_ε A`, `Γ ⊢_ε′ N : B`, `(ε ⊆ ε′)`, `coerce_{ε⊆ε′} M to x : A. N = N`. "Note that this transformation is not sound in general, by which we mean that, if we erase the effect annotations, we obtain an optimisation that is not valid in the CBPV model for global state". Theorem 12.5: "The Discard optimisation is operation-wise valid: … ThAx satisfies the Discard optimisation if and only if for every op : n in σ, op(x, …, x) = x." Theorems 12.8 and Prop 12.9 give Copy and Swap the same treatment.

So an effect-dependent law is valid exactly when every operation of the row satisfies the matching absorption, commutation or duplication equation. With no equations (OQ-22) it holds only at the empty row. That is A's `EffDepLaws` as stated.

### 1.5 Biernacki, Piróg, Polesiuk & Sieczkowski, *Handle with Care* (POPL 2018) [read]

A **step-indexed** binary logical relation for a row-typed CBV calculus with `lift`, mechanised in Coq. Lemma 7 (compat-handle), Theorem 8 (fundamental), Theorem 10 (soundness): "if Σ; ∆; Γ |= e₁ ≃ e₂ : τ / ε holds for all step-indices, then Σ; ∆; Γ ⊢ e₁ ≃ e₂ : τ / ε". Section 4 uses it for equivalences, including §4.1: `f ∗ (λx.5) ≃ handle_R f ∗ ask_R {ask _, r. r 5}` for row-polymorphic `f`. That is the tail-resumptive law at a pure clause composed with parametricity, the shape of our E6/`Tunnel`. Footnote 2: "We only treat deep handlers in the current work."

The step-index is decision 7's exclusion. EffModelRel avoids it with finite trees (`Rel.lean`: "no step index") [read].

### 1.6 Staton, *Instances of Computational Effects* (LICS 2013) [read, laws only]

Instance generation is an algebraic operation with its own laws, among them `(ν/ν)`: "x : [α, α] ⊢ νa.νb.x(a, b) ≡ νa.νb.x(b, a)", together with idem-ν and the commutation laws with other operations. EffModelRel proves idem-ν, ν/ν and new-ν (`Laws.lean`), and refutes ν/op at a contractible operation (`nu_op_fails_linear`). Under static per-site names there is no ν, and Core's `LawNuOp` is `True`.

### 1.7 Møgelberg & Staton, *Linear Usage of State* (LMCS 10(1:17), 2014) [read]

"We investigate the phenomenon that every monad is a linear state monad … There is a bijective correspondence between generic effects in the source language and state access operations in the enriched call-by-value calculus." Theorem 4.3 (full completeness): the linear-use state-passing translation is fully complete, "This means that contextual equivalence is preserved by linear-use state-passing translation."

For us this is the semantic content of two things at once: decision 59's handler state, passed to each clause and at each resume, used linearly; and the answering lowering, where the state is threaded through calls. The theorem is binary.

### 1.8 Ahman & Bauer, *Runners in Action* (ESOP 2020) [read]

Runners are handlers that use the continuation once, in tail position: "runners are simply a restricted form of handlers, which apply the continuation at most once in a tail call position." On the induced map `r_X`: "the continuation κ is used in a controlled way, as it appears precisely once as the head of the outermost application. In terms of programming, this corresponds to linear use in a tail-call position." Prop 3: "the monad morphisms Tree_Σ(−) → T are in one-to-one correspondence with T-runners for Σ." Theorem 7 (finalisation) is in the P5 menu.

So a tail-resumptive handler is a monad morphism, determined by its co-operations. This is the denotational reason the tail-resumptive law holds and the answering lowering is correct.

### 1.9 Katsumata, Rivas & Uustalu, *Interaction Laws of Monads and Comonads* (LICS 2020; arXiv 1912.13477) [read]

§3.1: "interaction of a 'just returning' computation should terminate immediately (in the initial state of the given machine behavior) whereas interaction of a sequence of computations should amount to a sequence of interactions." Section 4 relates monad–comonad interaction laws to Uustalu's stateful runners. The TR's T13.13 (an answering operation commutes with a control operation) reads itself as this compatibility at one operation of each. The TR says it has not checked that reading, and neither have I.

### 1.10 Congard, Munch-Maccagnoni & Douence, *Linear Effects, Exceptions, and Resource Safety* (ESOP 2026; arXiv 2510.23517v2) [read]

Algebraicity in a linear setting is a **strength**, and control effects lack one: "control effects have this particularity that they can change how many times the rest is computed, so we cannot guarantee that variables in Γ are not duplicated nor erased." Theorem 1 restores a strength for `T(− ⊕ E)` over the slice category `C/TI` (objects with destructors). The law that results is the destructor form, `K[raise e] ≡ D_K; raise e`, which the TR states as T7.3 and our S4 states as its finaliser conjunct.

**Graded algebraicity.** Read together, 1.1, 1.4 and 1.10 grade algebraicity by the operation's use:
- at a **linear** (resume-exactly-once) operation, the operation commutes with every evaluation context: plain algebraicity;
- at an **abortive** or **affine** operation, it commutes only with contexts whose frames own nothing, and in general takes the destructor form;
- at an **unrestricted** operation, the context's variables must sit under `!` (Congard's `U^!`), which is ignored here (decision 63).

Our A₂ `HandlerLaws` and Core's `LawAlg` state algebraicity at non-abortive, non-`unr` operations only. That is this grading, read off the qualifier.

### 1.11 Hillerström, *Foundations for Programming and Implementing Effect Handlers* (PhD thesis, Edinburgh, 2022) [read]

- Deep, shallow and parameterised handlers are **interdefinable**, each translation proved by simulation: Theorem 6.3 ("Simulation up to congruence"), Theorem 6.9 ("Simulation up to administrative reduction"), Theorem 6.12.
- The CPS translations are proved correct by simulation, through **forwarding** and **handling** lemmas: Lemma 4.6 (Forwarding), Lemma 4.7 (Handling), Theorem 4.8: "If M ⇝ N then ⊤⟦M⟧ ⇝⁺ ⇝*_a ⊤⟦N⟧". The thesis: "the only extra behaviour exhibited by a translated term is the bureaucracy of deconstructing the continuation stack." Lemma 4.15 adds backwards simulation for the higher-order translation.

So the published correctness proofs of handler compilation consume exactly the unary reduction laws (forwarding, handling, return), one per source rule.

### 1.12 Xie, Brachthäuser, Hillerström, Schuster & Leijen, *Effect Handlers, Evidently* (ICFP 2020; MSR-TR-2020-23) [read]

- **Scoped resumptions** (§1): "resumptions can only be applied in the very scope of their original handler context … the coherence of evidence translation turns out to only be preserved under scoped resumptions".
- **Translation correctness:** Theorem 4 ("Evidence translation is Sound in F^ev"), Theorem 8 ("Evidence translation is coherent": "If ∅ ⊢ e₁ : σ | ⟨⟩ ⇝ e₁′ and e₁ ⟼ e₂ … then there exists a e₂″, such that e₁′ ⟼ e₂″ and e₂″ ≅ e₂′"), Theorem 9 (to multi-prompt delimited continuations), Theorem 11 (coherence of the monadic translation: "e₁′ ⟶* e₂′"). Each is a forward simulation up to an equivalence.
- **Tail-resumptive in place** (§6.2): "almost all important effects are tail-resumptive." A clause of the form `λx k. k e` with `k ∉ fv(e)` becomes `tail (λx. …)`, and `perform_op w x = … case h.op of | tail f → f x`. "Note that even if f is tail resumptive, it may still use x. Moreover, since f has already captured its evidence w, it can still perform operations itself." The clause runs with the **handler's** evidence, not the perform site's. I found no theorem for §6.2 in the paper; it is presented as an optimisation of the proved translation.

### 1.13 Ma, Ge, Lee & Zhang, *Lexical Effect Handlers, Directly* (OOPSLA 2024), and Ma, Ge, Jung & Zhang, *Zero-Overhead Lexical Effect Handlers* (OOPSLA 2025) [read]

- Lexa: Definition 4 (simulation) and Theorem 1 (from Leroy): a translation is semantics-preserving if initial states are related, related final states agree, and "→ simulates → with respect to ∼". Theorem 2: "The translation from Lexa to Salt is semantics-preserving."
- Zero-Overhead: Theorem 1 (Simulation) and Corollary 1 (Semantics Preservation): "if a closed, well-typed SL program terminates with a value, then its translation in TL also terminates and produces the expected result."

These are the closest published precedents for A₃: a handler lowering, with a cost claim, proved by forward simulation. Neither has borrows. Zero-Overhead covers exceptional (abortive) effects only.

### 1.14 de Vilhena & Pottier, *A Separation Logic for Effect Handlers* (POPL 2021; Hazel) [relayed: P10 menu §1.4, P8 menu §1.3]

The handler rule assumes "Ψ allows do v {w. ewp E (k w) ⟨Ψ⟩{Φ}}", and the handler can resume only by supplying the protocol's `Q`. This is H.2: unary handler correctness as a program-logic rule, with the clauses checked against the protocol, which is the model condition. Our `ewp_handle` has the same shape over `opTable`.

### 1.15 Our own statements [read]

- **Core `ewp_handle`** (`Core/EffRules.lean:615`): from a return clause into `opTable Tout`, and from each clause meeting the entry's `PA ⋆ KapRel` at non-abortive and `PA` at abortive operations, `ewpTS e (opTable Tin) Qin` implies `ewpTS (hndE (hndVal n hr hs) e) (opTable Tout) Qout`. BRIEF §5 item 2 names it "initiality".
- **CoeffectsStrict `handle_unique`** (`experiments/CoeffectsStrict/CoeffectsStrict/Handler.lean`): "every homomorphism from the free model to a total algebra agrees with the handler on every finite tree", for the signature `{write : I32 ⇝ 1}` whose free model is data. Its header: free models of `read`-like arities "need X under U or ⊸ in the body, which FShape excludes".
- **EffModelRel** (`Laws.lean`, `Ownership.lean`): `h_ret`, `h_op`, `h_fwd`, `h_fwd_ab`; `alg_*` and `alg_dtor` (destructor form); `fwd_id` ("A handler of i whose clauses re-perform each operation on i with the destructors it was performed under … is the identity on related trees"); `eta_fails_linear`, `etaAff_leaks`, `etaAff_not_moded`; `hnd_sim` ("Hiding, as parametricity") and `hiding_counter`; `no_accidental_handling`. All are SIB.
- **effects TR §13** (`docs/effects-tr/13-adjunction.md`), PAPER:
  - freeze/resume are `φ`/`φ⁻¹` of CBPV's `F ⊣ U` on stacks, β is the existence half (T13.2) and η the uniqueness half (T13.8);
  - η at affine operations needs D13.7's `M to^k y. N`;
  - the generative form of η fails (P13.10, "computed here by hand");
  - binary hiding "is not in the binary relation" (O7);
  - the interaction law T13.13 holds in a special case and fails at affine operations (P13.14).
  - Verdict: "No proof in §7 becomes shorter when re-derived this way."

---

## 2. How prior systems realise and prove the laws

| system | laws stated | form | proof technique | borrows / linearity |
|---|---|---|---|---|
| Plotkin–Pretnar 2013 | initiality, return, op, algebraicity, η (empty handler) | denotational; Kleene (in)equations | free model's universal property | none |
| Kammar–Lindley–Oury 2013 | return, op, hoist (forwarding), deep/shallow | reduction rules | termination by adaptation of strong normalisation | none |
| Kammar–Plotkin 2012 | Discard, Copy, Swap, graded by effect set | denotational, effect-annotated | operation-wise validity (Thm 12.5) | none |
| Biernacki et al. 2018 | contextual equivalences by example | step-indexed binary LR, Coq | fundamental + soundness | none |
| Ahman–Bauer 2020 | runners = monad morphisms; finalisation | denotational | free model + Prop 3; Thm 7 | linear use of *external* resources by construction |
| Møgelberg–Staton 2014 | linear-use state passing fully complete | syntactic + enriched models | Thm 4.3 | linear state, no borrows |
| Congard et al. 2026 | destructor-form algebraicity (strength) | categorical; resource CBPV | Thm 1 | linear + destructors; no borrows |
| Hillerström 2022 | interdefinability; CPS correct | simulation | forwarding/handling lemmas, Thm 4.8 | none |
| Xie et al. 2020 | evidence translation sound, coherent | simulation up to ≅ | Thms 4, 8, 9, 11 | none |
| Lexa 2024 / Zero 2025 | lowering semantics-preserving | forward simulation (Leroy) | Thm 2; Thm 1 | none |
| Hazel 2021 | handler rule | unary separation logic, Iris | adequacy Thm 4.1 | affine resources, no lifetimes |
| EffModelRel (ours, SIB) | all of §7, η semantic, hiding by simulation | binary over finite trees, no step index | denotational equality + `TreeRel` induction | moded (lin/aff/unr), lends as runners, no BoLo |
| Core (ours, σ=[]) | `ewp_handle`, `ewp_kappa_resume`, `ewp_kappa_cancel`, frame/anti-frame at abortive tables | unary Kripke `ewp` | inner fixed-point induction | BoLo, at the empty lend stack |

**The pattern.** Unary correctness is proved one of two ways: by reduction rules that *are* the laws (Kammar–Lindley–Oury, our S4), or by a program-logic rule (Hazel, our `ewp_handle`). Binary laws are proved either denotationally, against a free-model semantics where they are equal denotations (Plotkin–Pretnar, EffModelRel), or through a binary logical relation (Biernacki et al.). Compiler correctness, wherever it is proved, is a forward simulation that uses one unary lemma per source reduction rule (§1.11–1.13). No source above proves a compiler correct through binary laws.

---

## 3. Pitfalls

1. **The tail-resumptive law has a hygiene condition the textbook form hides.** Xie et al. run a tail clause "in place" but with the *handler's* evidence (§1.12), so the clause's own operations go to handlers outside its handler. The law `handle_l H (K[perform l v]) ≡ handle_l H (K[c v])` moves `c` *inside* `K` and *inside* the handler. It holds only if neither `K` nor the handler catches an operation `c` performs.
   - At our instance, `[handle]`'s premise `∀ o ∈ S, o.n ≠ n` (`handle_compatC`, `hnS`) types the clauses at the outer row `S`. A handler inside `K` handles a name absent from its own result row, which contains `S`. So typing excludes both captures, which is an R3-style lacks fact (P2 menu).
   - A₂'s `HandlerLaws` tail conjunct carries only `catches K l = false`. Whether A's `CtxEquiv` typing premises supply the rest at every instance is a reading question I have not checked, and I have not verified that any gap is real.
2. **η loses destructors when written as a syntactic clause.** The forwarding clause `op(p, k). op(p; y. resume k y)` re-performs with an empty destructor list:
   - at a linear operation this is observable only at an unhandled operation (`eta_fails_linear`, SIB; TR P13.9);
   - at an affine operation, when an outer handler cancels, the frozen frames' finalisers never run (`etaAff_leaks`), and the program is not moded (`etaAff_not_moded`).
   So in a linear core with SPEC §19 cancellation, η needs either a frame that cancels the held continuation on unwind (TR D13.7, K.4), or its affine instances are excluded by typing (TR L13.5, "it never types when some resuming o has W ∈ q_o and C ∉ q_o"). Core's `CapEta` quantifies over typed closings, so by the analogue of L13.5 it may be vacuous at affine operations. That is a reading, unchecked against `CDerives`.
3. **The generative form of η is false; the same-instance form is not typable as a single name.** TR P13.10: `handle x : E with Fwd_{x→x′} in M ≡ M[x′/x]` fails at `ieq x x′` (PAPER). Core's `[handle]` forbids the handled name in the result row, so `fwdH n n` does not type. `CapEta` is therefore stated up to renaming `n` to `n′` (OQ-27). Under static names there is no `ieq`, so the renaming form is the one available.
4. **Algebraicity is not unconditional in a linear setting.** Congard et al. (§1.10): control effects have no plain strength. `K[raise] ≡ raise` "is unsound when K owns something" (TR §7.1). It must be graded: plain at linear operations, destructor form at abortive and affine ones. A₂ and `LawAlg` already restrict to non-abortive, non-`unr` operations. The abortive case lives in S4's finaliser conjuncts, not in an algebraicity law.
5. **The interaction law needs exactly once.** TR P13.14: an answering operation and an affine control operation do not commute when the control clause cancels (PAPER, by hand). Any law that commutes a lend's operation past a capture (tensor of model and comodel) is valid only at linear operations. Compare ν/op, which needs at most once (`nu_op_fails_linear`).
6. **Binary hiding is not free in a relation that matches cells with equal contents.** TR §13.4: "D6.4 relates a state of type A₀ by VR(A₀), which is equality at ground types". Representation independence needs relations in worlds (Ahmed–Dreyer–Rossberg) or abstract types. EffModelRel's `hnd_sim` gets it only because handler state there is a state-passing *type*, not a cell.
7. **Step-indexed binary relations are excluded.** Biernacki et al.'s route is step-indexed. Under decision 7 a binary relation must be denotational (EffModelRel's finite trees, which stop at negative recursion: `no_negative_domain`), biorthogonal over terminating observations, or determinism-based (TwoRun, which does not build on main).
8. **Contextual approximation over complete runs ignores divergence.** A₂'s `CtxApprox` reads `Observes`, which is defined on complete runs. Divergence is codata here, and driven loops are not complete runs. A law between two programs that never complete, or that differ only in the io trace of a driven loop, is not tested by `CtxApprox`. This is a reading of `Targets/A/Binary.lean`, not a claimed gap.
9. **"Correct" is vacuous with no equations, and that is deliberate.** Plotkin–Pretnar: with an empty theory every handler is correct. So P11's content is the reduction laws plus forwarding, not a model check. The moment OQ-22 admits equations (e.g. state's `get; get = get`), correctness becomes undecidable in general (Π₂-complete, §1.2) and becomes a proof obligation per handler.
10. **A law proved in a sibling calculus is not a law of the kernel.** BRIEF §8 pattern 5. EffModelRel proves everything here with no bridge to Core. TR §13.0's table shows the unary kernel lift of β needs L14.4 (open, O5).

---

## 4. Borrows and lifetimes: what the literature has, and where we would be new

- **No published handler-law result has lifetimes or borrows.** Hazel and Affect have affine resources and no lifetimes. Runners and Congard have linear resources and destructors, and no borrows. Biernacki, Kammar, Plotkin–Pretnar and Staton have neither. Lexa, Zero and Xie et al. prove lowering correct with no resource discipline.
- **What is ours, and new if done:**
  1. **β up to fresh internal lifetimes** (K.2): "freeze then resume is the identity, up to fresh internal lifetimes" (TR §13 head). The lifetime half of the freeze binder has no precedent (I2 menu T3: Pitts 2016, ordered name abstraction "remains to be investigated").
  2. **Hiding as 6.66 at a suspending table** (K.5 at W). Unary hiding at pure and abortive tables is proved (`wpTS_M_antiFrameX`, `ewpTS_M_antiFrameU`); at resuming tables it is open (TR "part of O8"; device `AntiFrameW` OPEN at W). Hazel's frame rule is the nearest; it has no lifetime and no view.
  3. **The tail-resumptive law as a borrow law.** Under the answering reading (P10 menu X.1, HandlersAsBorrows), a tail-resumptive handler is `withbor` of the handler state and the clause is `withswap`. Core's `I4c` already states the binary form: the control form equals the answering run (`CtxEquiv … (ctlForm n impl s₀ e) (ansRun d s₀ body)`, OPEN). So the tail-resumptive law, I4, and the answering lowering class are one statement at three levels. Ahman–Bauer Prop 3 and Møgelberg–Staton Thm 4.3 are its borrow-free denotational and syntactic analogues.
  4. **η with cancel** (K.4): no source forwards a cancel through a forwarding handler with destructors. The TR's D13.7 frame is ours.
  5. **Lowering correctness with a borrow invariant.** A₃ quantifies over typed programs. A simulation that tracks BoLo's invariant on the target is not in any source. A₃ as stated observes only answers and io traces, so it need not carry the invariant, only use typing.

---

## 5. The menu

Each option gives its statement shape, its cost, what it buys, its interactions, and its evidence. Cross-references name rows of the other menus: [P2](p2-effect-safety.md) (R.x, S-x), [P8/P5](p8-p5-linearity-drop.md) (8.x, 5.x, X.x, F.x), [I2](i2-capture-resume.md) (M.x, T.x), [P10/P9](p10-p9-exclusivity-lifetimes.md) (X.x, L.x, prefixed "P10"), and [rows vs capabilities](rows-vs-capabilities.md) (O.x).

### 5.1 H: what "the handler is correct" is stated as

**H.1 Reduction equations, empty theory (S4 as built).**
- *Shape:* `HandlerSem`'s seven conjuncts: return, resuming catch (the clause gets `v` and `capture l H K`), abortive catch (`unwindClear K`), deep resume, cancel, finaliser on return, and finaliser on unwind. Each holds in every context `K₀`, up to `PureJoin`, at `Live` configurations.
- *Cost:* the bridge `handlerSem_ourInst` from `Head`'s effect steps (RESTRUCTURE §4.1). It is mechanical by reading, since Core's head steps are these laws, but it is not built.
- *Buys:* P11 in done, with no model theory. Plotkin–Pretnar's own remark makes it the whole of correctness while signatures carry no equations.
- *Interacts:*
  - It **excludes P8 8.3** (the one-shot cell): `capture` is a store-free value and the laws are `PureJoin` (AGREE Q9).
  - It is compatible with P8 8.2 and 8.4.
  - It fixes P5's cancel to SPEC §19's `cancelOf` (decision 62).
  - It is neutral to the P2 R options: forwarding is `KontLaws`.
- *Evidence:* Core's head rules (`Paper/S3_Dynamics/Definitions.lean`); `ewp_kappa_resume`/`ewp_kappa_cancel` (Core σ=[]).

**H.2 The model rule in the program logic (unary initiality, existence half).**
- *Shape:* `ewp_handle` at W: `HandleCompat` (the `[handle]` rule compatible at W) plus `RedLaws` (head steps preserve `ewpW` at monotone tables).
- *Cost:* `ewpW` at resuming tables, which is OQ-8/OQ-9's world. The proof at W follows `ewp_handle`'s inner fixed-point induction.
- *Buys:* `fundamentalC` at W for handlers, and with it every safety theorem for handled programs. It is what B1 needs in the composite, which makes it the one H option that "safety needs".
- *Interacts:*
  - With I2 M0, it is what we have.
  - Under M1 or M2, `KapRel` at W must carry the spanning lends.
  - With P10 X.1, the answering case is `withbor`.
  - With O2 (capabilities), the rule becomes 6.60 plus a borrow constant, if handlers are lends.
- *Evidence:* `ewp_handle` (Core σ=[]); `p11_core` (device, σ=[]); `redLaws_of_mono`; Hazel's handler rule (§1.14).

**H.3 The uniqueness half, stated.**
- *Shape:* for a first-order signature whose free model is a data type, every term homomorphism agrees with the handler on every finite tree. That is `handle_unique` generalised from `write` to every `FShape` signature.
- *Cost:* a free model as a datatype (CoeffectsStrict's `foldOwn`). It fails for operations with non-trivial result arities ("need X under U or ⊸"), which are most of ours (`read`, `yield` with an answer, async). Beyond those it needs the operational free model, the machine itself, and then uniqueness is a binary statement.
- *Buys:* η and fusion follow from uniqueness (TR T13.8 is the uniqueness half). It is evidence that the reduction semantics *is* the induced homomorphism, not only a model of it.
- *Interacts:* the binary laws K.3 and fusion (OQ-49); nothing in safety needs it.
- *Evidence:* `handle_unique` (Core σ=[], one signature); Plotkin–Pretnar §1.1; Ahman–Bauer Prop 3.

**H.4 Denotational initiality via a sibling model.**
- *Shape:* a semantics `⟦−⟧ : Core → Tree` with adequacy, so that each EffModelRel law transfers to Core.
- *Cost:* the bridge does not exist (BRIEF §4: "No bridge to Core"). EffModelRel stops at negative recursion (`no_negative_domain`), and Core has `boundedFix`, codata loops and BoLo's resources. The trees erase lifetimes (TR D3.10), so the unary-at-W content is lost in the transfer.
- *Buys:* every algebraic law at once, including hiding by `hnd_sim`, if the bridge is built.
- *Interacts:* with I2 T3 (the freeze binder), whose location half is equality of denotations under renaming.
- *Evidence:* EffModelRel (SIB); BRIEF §8 pattern 5 warns against this as a substitute for a kernel law.

### 5.2 F: the form of every law

**F.1 Unary reductions.**
- *Shape:* as S4: two configurations joinable by store-free steps.
- *Cost:* lowest.
- *Buys:* return, catch, abortive catch, deep resume (β), cancel, and finalisers.
- *Cannot state:*
  - the tail-resumptive law when the clause performs effects: the left side runs `c` outside `K`, the right side inside, and they meet only after `c` returns;
  - η, fusion and hiding.
  - Algebraicity is built in: evaluation contexts include `□ to x. N`, so `perform` in a bind frame is a `StopsIn` configuration (S3), which is algebraicity in reduction form (Kammar–Lindley–Oury's hoist.op).
- *Interacts:* compatible with every other option.

**F.2 Unary in the world.**
- *Shape:* one `ewpW` entailment per law, as `I5beta`, `RedLaws` and `AntiFrameW`.
- *Cost:* one lemma per law per world. The resuming-table world is unbuilt, so each is OPEN at W.
- *Buys:* laws usable inside the fundamental property. This is the form BRIEF §5 item 3 asks for ("Handler laws over the kernel relation"), and BRIEF §8 pattern 5 says laws must be stated at W or shown to survive the re-index.
- *Interacts:*
  - I2 M1 needs β in the `Relend` form (K.2).
  - I2 M2 needs β with `held` carried.
  - P10 X.2 is K.5 in this form.

**F.3 Run-level, closed.**
- *Shape:* for closed typed programs at a data answer, under every respecting runner, the two sides have the same complete runs' answers and io traces. Equivalently, a stuttering bisimulation between the two closed configurations.
- *Cost:* per law, a simulation between two specific configurations. At a deterministic machine (ours, up to fresh locations: `head_det_eff`) a run-level equality reduces to joinability of *traces*, not configurations. No context quantifier and no binary logical relation.
- *Buys:*
  - the tail-resumptive law with effectful clauses, and η at closed programs;
  - exactly the per-class facts the lowering consumes (Z.2);
  - the shape of A₃'s `LoweringCorrect` (answers and io traces);
  - the A-level form of I4c restricted to closed programs.
- *Does not buy:* use of a law inside an open program. A law at F.3 says nothing about `C[lhs]` versus `C[rhs]` unless re-proved at each closing.
- *Interacts:*
  - Determinism makes F.3 cheaper than F.4, but determinism is up to the choice of fresh location, so equality of runs is up to renaming, which is I2 T3's location half.
  - It is neutral to the P2 R options, except that the tail law's hygiene (§3 item 1) is a typing fact that R1/R3 supply.
- *Evidence:* no precedent in this shape for laws. It is the shape of every compiler-correctness theorem in §1.11–1.13.

**F.4 Contextual equivalence.**
- *Shape:* A₂ `HandlerLaws`, `EffDepLaws`, `Abstraction`; Core's `Laws` (return, op, forwarding, tail, algebraicity, capture β, `CapEta`, `Hiding`, fusion at a parameter, ν/op = `True`).
- *Cost:*
  - a binary method with no step index (§3 item 7);
  - TwoRun's determinism-up-to-renaming route does not build on main;
  - for fusion, the composite handler as a term (OQ-49);
  - for hiding, relations in worlds (§3 item 6);
  - per the decision, optional unless safety needs it.
- *Buys:* every law, usable in any context. It is the only form in which P12's representation independence and the lowering's representation changes (K.6) can be stated.
- *Interacts:*
  - P12's binary `Abstraction` and `Tunnel` (E6's binary form) share the method.
  - Under P2 R5 (capabilities) contextual equivalence becomes lexical, and Biernacki et al. 2020 is the precedent [relayed].
- *Evidence:* EffModelRel (SIB); Biernacki et al. 2018 (step-indexed, excluded).

### 5.3 K: the capture laws (I5)

**K.1 β, unary.**
- *Shape:* `I5beta`: `ewpW (hndE H (K.plug w)) ⊢ ewpW (resume (kappa n H K) w)` at monotone tables; in done, S4's deep resume.
- *Cost:* none; proved at every world (`i5beta`).
- *Buys:* deep handlers (decision 62), E4, and the state machine's re-entry point.
- *Interacts:* it is decision 62 itself. A shallow handler fails it "by definition" (RESTRUCTURE's feature table).

**K.2 β up to fresh internal lifetimes.**
- *Shape:* resuming a frozen κ at `w` is `handle H (K[w])` with each lifetime bound in κ instantiated fresh, beneath the resumer's. In I2 terms, the resume half of `FreezeBinderLife`.
- *Cost:* `FreezeBinder`, and first `NotVDenNaturalArises` (I2 menu T3, open); L14.4 (TR O5).
- *Buys:* β stays true when a lend spans the stop under I2 M1 (ghost end), and resuming inside a younger lend is rejected (D-ORD, P10 L.5).
- *Interacts:* it **requires I2 M1 + T3**. Under I2 M2 (carry) β keeps the same lifetime, so K.1 at W with `held` suffices and K.2 is not needed. Under I2 M0, K.2 is K.1.

**K.3 η, renaming form (binary).**
- *Shape:* Core's `CapEta`: `handle (fwdH n n′ E) e ≡ e.renameOp n n′`, with `n ≠ n′`.
- *Cost:* F.4. At affine operations the syntactic forwarding clause drops destructors (§3 item 2), so the law needs a typing restriction or K.4.
- *Buys:* the lowering may delete forwarding handlers. η is also the uniqueness half (H.3), so with K.1 it closes the adjunction reading of TR §13.
- *Interacts:*
  - With P8 X.2 (§19 uncatchable cancel), a forwarding handler must forward the cancel too, which K.3 alone does not.
  - P2 R1's static names make the renaming form the only one (TR P13.10 refutes the generative form).
  - AGREE's minor finding read "η has no unary form in I5"; η's unary forms are now `A.EtaHold` (K.4's frame) and `A.EtaLin` (K.3's clause under L13.5's restriction), beside done, STATED.
- *Evidence:* `fwd_id` (SIB, semantic forwarding with destructors); `eta_fails_linear`, `etaAff_leaks` (SIB); TR T13.8(a)/(c) (PAPER).

**K.4 η with a continuation-holding frame.**
- *Shape:* K.3 with affine clauses written `(op x.o(p; y. ret y)) to^k y. resume k y` (TR D13.7), whose unwind runs `cancel k`.
- *Cost:* a new former and its compatibility lemma (TR L13.9 is PAPER only). In the destructor recursion, the well-foundedness argument ("S′ was captured before the frame holding it was pushed") must be redone at the kernel. The memory `few-formers` weighs against it without a program.
- *Buys:*
  - η at affine operations, with cancels forwarded through a forwarding handler and finalisers run in order;
  - a general "frame owning a continuation", which stored-continuation programs (E9) may also want.
- *Interacts:*
  - P5 5.5 (tagged finaliser frames) and the global exactly-once statement;
  - P8 8.x, since the held `k` is used exactly once by the frame;
  - I2 M1/M2, since the held `k` may hold lends (TR "§14's case").
- *Evidence:* TR T13.8(b), L13.9 (PAPER).

**K.5 Hiding, unary (6.66 at W).**
- *Shape:* `AntiFrameW`: `mutView ℓ α T δ i ⋆ AntiRelendW … ⊢ ewpW i e Tb Q`.
- *Cost:* the anti-frame at a resuming table, the device's open conjunct (TR "part of O8").
- *Buys:*
  - handler state behind a lend across resumptions (P10 X.2);
  - decision 59's state passing as the 6.66 round trip;
  - the safety half of representation independence: the body cannot reach the state.
- *Interacts:*
  - **required by P10 X.2**, and by I2 M1/M2 whenever handler state is lent across a stop;
  - with P10 X.1 (answering as reborrow) it is 6.65/6.66 at tier 1, already proved at abortive tables;
  - under O2 capabilities it is the anti-frame on the capability's cell.
- *Evidence:* `antiFrameW_core` (σ=[]); `ewpTS_M_antiFrameU` (abortive); GhostEnd `ewpTS_M_antiFrameR` (GE).

**K.6 Hiding, binary (representation independence).**
- *Shape:* Core's `Hiding`: two answering implementations related by `AnsSim` both ways, at related states, with agreeing observers, are contextually equivalent.
- *Cost:* F.4 plus relations in worlds (§3 item 6). `AnsSim` is syntactic (runs of the clauses), which keeps the hypothesis cheap, but the conclusion is still contextual.
- *Buys:* the lowering may change a handler state's representation (scalar replacement into the caller's frame, Z.1's "state lives in the caller's frame"); library abstraction (P12 `RepInd`).
- *Interacts:* P12; Z.2 only if the lowering changes representations by a source-level argument rather than inside the simulation.
- *Evidence:* `hnd_sim`, `hiding_counter` (SIB); TR §13.4 (O7).

### 5.4 Z: which laws the erased lowering needs, and OQ-23

**What each lowering class consumes** (BRIEF §1; `Instance/ZeroCost.lean` `LowClass`):

| class | lowering | source law that justifies it | unary form available? | extra conditions |
|---|---|---|---|---|
| answering (tail-resumptive) | direct call of the clause on the passed state | the tail-resumptive law; semantically, runner = monad morphism (Ahman–Bauer Prop 3), linear-use state passing (Møgelberg–Staton Thm 4.3) | F.3: `A.TailLaw`, beside done, STATED; binary `LawTail`, `I4c` | clause effects go to handlers outside its own (§3 item 1, from `[handle]`'s `n ∉ S`); the clause's footprint does not conflict with lends live at the perform (survey C1; P10 X.1) |
| abortive | early return through a sum, a branch per call | abortive catch (S4), destructor-form algebraicity (S4's finaliser conjuncts), forwarding (`KontLaws`) | yes (F.1) | `unwindClear K`; finalisers abortive-only (P8 F.1) |
| control | a hand-written state machine | catch, deep resume (β), cancel, forwarding | yes (F.1) | the frozen frame's placement (I2 T4 or T3) |
| forwarding handler | deleted | η | no (F.4) | K.3/K.4 at affine operations |
| nested handlers fused into one state machine | one dispatch | fusion | no (F.4; OQ-49) | — |
| handler state in the caller's frame | scalar replacement | hiding (K.6) | no (F.4) | — |

So the three classes the backend has today need only unary laws, plus the tail-resumptive law, plus typing facts. The binary laws enter only for the optimisations in the last three rows.

**Z.1 Per-class laws plus corpus counts (OQ-23 (a)).**
- *Shape:* each row above is backed by its law; `ZeroCost` is checked by corpus counts against `refCost`; no theorem relates `lower` to the source semantics.
- *Cost:* the tail-resumptive law in some form (F.3 or F.4), since the answering class has no unary justification. The counts need the reference programs, which are not written.
- *Buys:* no compiler proof. It matches decision 48's revised acceptance. OQ-23 records that its premise ("which elaboration makes true by definition") is gone since effects are core.
- *Interacts:* with O1 versus O2 (rows vs capabilities), because the class must be known where the law is applied. Under O1 it is in the type (`RowCon.cls`); under O2 it is in the value, and each specialisation needs its own law instance.
- *Evidence:* the backend compiles and runs (BRIEF §1). Ante has the same three classes, unproved (deep dive: "Tail-resumptive → inlined; abort-only → setjmp/longjmp").

**Z.2 Compiler correctness by forward simulation (OQ-23 (b)).**
- *Shape:* A₃'s `LoweringCorrect`: for typed closed programs at data answers, under `PlatformSim`, source runs and target runs agree on answers and io traces, both directions. Proved by Leroy's method: a relation `∼`, initial related, final agreeing, forward simulation. Backward follows from target determinism (`Tgt` is deterministic given the platform).
- *Cost:* a simulation relation over the three classes. The state-machine class is a CPS/defunctionalisation transformation, as in Hillerström Thm 4.8 and Xie et al. Thm 11, and it is the hardest case.
  - Inside the simulation, the tail-resumptive class needs the relation to pair "the clause running outside `K` with κ pending" (source) with "the clause running in place" (target). That uses §3 item 1's typing fact, not the binary law.
  - The driven programs are excluded today (`ZeroCost` reads complete runs).
- *Buys:*
  - "verified foundations … core → Wasm" (`language-purpose`, quoted in OQ-23);
  - the lowering of E1's no-colouring programs is then a theorem, not a count;
  - **the binary laws are not needed for it**, so Z.2 is compatible with "binary laws are optional".
- *Interacts:*
  - P2 S-g: the trace over-approximation is what the simulation preserves.
  - I2 T4: placement must be in the simulation relation, since the target never moves a frame.
  - P8 8.3 would add κ cells to the simulation.
  - O1/O2: specialisation by class is a compile-time case split the simulation follows.
- *Evidence:* Lexa Thm 2, Zero Thm 1 (lexical handlers, no borrows); Xie et al. Thms 8, 11; Hillerström Thms 4.8, 6.3. No Lean in our trees.

**Z.3 Laws as source rewrites, then a fixed naive lowering.**
- *Shape:* optimisations (tail-resumptive in place, forwarding deletion, fusion, state scalarisation) are source rewrites justified by F.4 laws. A naive, uniform lowering is proved once (Z.2 for one class).
- *Cost:* F.4 for every rewrite, with no step index.
- *Buys:* each optimisation is local, and new optimisations need only a new law. This is Kammar–Plotkin's programme.
- *Interacts:* makes the binary laws necessary for the lowering, against the decision's default. The only option on this axis that does.
- *Evidence:* Kammar–Plotkin 2012; Kammar thesis Thm 12.5.

### 5.5 How the families combine

| combination | P11 | I5 | lowering | needs from other menus |
|---|---|---|---|---|
| **H.1 + H.2 + K.1 + Z.1** (today's done and device, completed) | S4 at our instance; `HandleCompat` at W | β unary | counts | tail law in some form (F.3), or the answering class unjustified |
| **H.1 + H.2 + K.1 + K.5 + Z.2** | as above | + hiding at W | simulation theorem | I2 M0, M1 or M2 for the world; P10 X.2 for K.5; P2 R1/R3 for the tail hygiene |
| **+ K.2** | — | β with fresh lifetimes | — | I2 M1 + T3 |
| **+ K.3/K.4 + K.6 + F.4** | binary laws | η, binary hiding | Z.3 possible | OQ-49 (fusion), OQ-27 (η typing), a no-step-index binary method |
| **H.4 alone** | everything in SIB | everything in SIB | nothing | a Core→Tree bridge; BRIEF §8 pattern 5 |

**Required, excluded, favoured, per option** (summary of §5.1–5.4):
- H.1 excludes P8 8.3, and is neutral otherwise.
- H.2 is required by B1 at W, and so by "nothing breaks the borrow calculus". It needs the I2 world.
- H.3 favours K.3.
- H.4 is independent of everything, and helps nothing at the kernel.
- K.2 requires I2 M1 and T3.
- K.5 is required by P10 X.2.
- K.4 favours P5 5.5.
- K.3 is in tension with P8 X.2 unless K.4.
- K.6 favours P12.
- Z.2 favours P2 S-g and I2 T4. It requires the tail hygiene that R1/R3 give, and is excluded by nothing.
- Z.1's class lookup is easier under O1 than O2, and O2-g restores it.
- Z.3 requires F.4.

---

## 6. Where our current target sits

### 6.1 Position

- **P11 in done:** A's S4 `HandlerSem` (H.1, F.1). OPEN at our instance (`handlerSem_ourInst` not built; `Status.lean`: "OPEN (the bridges to build, RESTRUCTURE §4.1)").
  - Forwarding is the structural fact that a handler frame of `l` catches only `l` (RESTRUCTURE §1.5).
  - **The tail-resumptive law, algebraicity and η have no conjunct in S4**, and none in done.
  - Algebraicity in reduction form is S3's `StopsIn` under bind frames (§5.2 F.1).
- **Beside done: `A.UnaryLaws`** (`experiments/Targets/Targets/A/UnaryLaws.lean`), STATED, not proved, at no instance. Form F.3, in every evaluation context of a configuration a typed closed program reaches (`RunsAlike`).
  - `TailLaw`: the clause `tailCl c` runs in place. Its hygiene is three hypotheses over the row of `c v`: no label of it is caught by `K`; it lacks `l` (what `[handle]`'s `n ∉ S` appears to supply; not checked); `K` holds no finaliser, or every operation of the row is linear.
  - `AlgLaw`: graded as `LawAlg` (resuming operations); the abortive case is S4's finaliser conjuncts.
  - `EtaHold`: η with K.4's frame, written with A's `thenT` (`… then y. k.resume y unwind k.cancel`). `EtaLin`: η with the plain clause at labels with no affine operation (L13.5). `etaLin_of_etaHold` is PROVED.
  - Each fails at an instance whose handler or bind ignores its clauses (`not_tailLaw_toy`, `not_algLaw_toy`, `not_etaHold_toy`, `not_etaLin_toy`), PROVED.
  - Not conjuncts of S4 or of done: whether they join done is a choice on axes H, F and K, for the user.
- **P11 in the device:** `P11 = HandleCompat ∧ RedLaws` (H.2, F.2). PROVED AT σ=[] (`p11_core`), `RedLaws` at every world whose operation tables are monotone (`redLaws_of_mono`). OPEN at W.
- **I5 in done:** S4's deep resume (K.1).
- **I5 in the device:** `I5 = I5beta ∧ AntiFrameW ∧ FrameW`. `I5beta` is PROVED at every world, and the whole is PROVED AT σ=[] (`i5_core`). K.5 is OPEN at W.
- **Binary:** A₂ `HandlerLaws` (return, resuming and abortive catch, forwarding, tail, algebraicity, capture β, cancel), `EffDepLaws`, `Abstraction`. Core `Laws` adds `CapEta` (K.3), `Hiding` (K.6), `LawFusion` at a `fuse` parameter, and `LawNuOp = True`. All stated, OPEN, out of the first pass. A₂ omits η: "Capture η and Copy/Swap need a renaming of labels or of variables, and A has no substitution".
- **Lowering:** A₃ `LoweringCorrect` and `ZeroCost` (Z.2's statement), out of the first pass. `LowClass` is named-only. OQ-23 is open and needs the user.

### 6.2 Observations from reading, with no Lean checks run

1. **The tail-resumptive conjuncts have only one hygiene premise.** A₂'s carries `catches K l = false`, and Core's `LawTail` carries `K.HasHnd n = false`. At Core, `[handle]`'s `n ∉ S` premise appears to supply the rest through `J.closed` (§3 item 1). At A, I have not checked whether `CtxEquiv`'s typing premises do, and I have not verified that any gap is real. The unary `A.TailLaw` states all of the hygiene as explicit hypotheses: not caught by the handler (the premise `n ∉ S` is about this one), not caught by `K`'s frames, and no finaliser in `K` unless the clause's operations are linear (the premise `n ∉ S` is not about these two).
2. **`CapEta` may be vacuous at affine operations,** if the analogue of TR L13.5 holds for `CDerives`. OQ-27 says this is "settleable by trying the term in `CDerives`". Not tried.
3. **`LawAlg` and A₂'s algebraicity conjunct are graded by qualifier** (`o.abort = false`, `o.q ≠ .unr`), which matches §1.10. The abortive case is carried by S4's finaliser conjuncts. No statement covers an affine operation's algebraicity under a frame that owns something, which is the destructor form at a *resuming* affine operation (TR T7.3 covers arity 0 only).
4. **A₂'s observations are complete runs** (§3 item 8). For div-as-codata programs, the binary laws are termination-insensitive.
5. **`Hiding` is stated at answering implementations (`AnsImpl`) only.** Hiding for a control handler's state, which decision 59 passes "to each clause and at each resume", has no binary statement. Its unary half is `AntiFrameW` only if the state is a lend (P10 X.2).

### 6.3 Inventory (CLAUDE.md §5)

- **Unspent hypotheses.**
  - `HandleCompat`'s `E.length ≤ 2^32` and `n ≠ 0` are carried from `handle_compatC`.
  - `RedLaws`' `a.allocs = false` excludes allocating head steps, which is why the one-shot cell (8.3) is excluded twice.
  - `I5beta`'s `TableI.Mono` is the only premise, and it is spent.
- **Unused uniqueness and functionality results.**
  - Core's determinism up to fresh locations (`head_det_eff`) is unused by every law statement. It is what makes F.3 cheap, and what Z.2's backward direction uses.
  - CoeffectsStrict's `handle_unique` (H.3) is unused by the targets.
  - EffModelRel's `fwd_id` and `hnd_sim` have no Core counterpart.
- **Untranscribed literature results in the run-up.**
  - Plotkin–Pretnar's two Kleene inequations are S4's return and catch conjuncts, transcribed as joins.
  - Their η (`M to x. N ≃ M handled with {} to x. N`) is untranscribed at A as an equation; A states the TR's same-label η unary, beside done (`EtaHold`, `EtaLin`).
  - Congard Thm 1 (strength over destructors) has only the TR's T7.3 and EffModelRel's `alg_dtor` as counterparts, with none at Core.
  - Leroy's simulation theorem (as used by Lexa Thm 1) has no counterpart for `Tgt`.
  - Ahman–Bauer Prop 3 and Møgelberg–Staton Thm 4.3 have no counterpart. They are the denotational facts behind the answering class.
- **Printed BoLo lemmas in the run-up that are untranscribed:** [TR] 6.40 (`Paper/INDEX.md`'s one untranscribed row), in `fundamentalC`'s run-up, on which H.2 at W rests; 6.150 at a resuming table (GhostEnd: lift not written), which K.5 at W and H.2 at resuming rows will reach for.
- **No obstruction is claimed in this chapter.** Every "open" or "not built" above means "I have not derived it and have not verified that any obstruction is real."

---

## 7. What could not be verified

- Kammar & Plotkin's POPL 2012 paper itself; its content is read through Kammar's thesis (same results, thesis numbering).
- Staton 2013: only the law names and `(ν/ν)` were read, not the representation theorems.
- Katsumata–Rivas–Uustalu: the reading of TR T13.13 as an interaction-law instance is the TR's, unchecked by me as by it.
- Biernacki et al. 2020 (*Binders by Day*), Zhang–Myers 2019, Sieczkowski–Pyzik–Biernacki 2023 (a reduction theory): relayed from the survey and sibling menus.
- Hazel: relayed from the P10 and P8 menus.
- Xie et al. §6.2: I found no theorem for the in-place tail-resumptive optimisation; whether the extended version proves it elsewhere is unchecked.
- Ahmed–Dreyer–Rossberg 2009, Levy's stack adjunction, Curien–Fiore–Munch-Maccagnoni 2016: cited through TR §13 ("content recalled").
- Schuster, Brachthäuser & Ostermann, *Compiling Effect Handlers in Capability-Passing Style* (ICFP 2020): not read; whether it proves its translation correct is unchecked.

---

## Sources

Read for this chapter (full text, [read] items above):
- Plotkin, Power. *Algebraic Operations and Generic Effects.* Applied Categorical Structures 11, 2003. https://homepages.inf.ed.ac.uk/gdp/publications/alg_ops_gen_effects.pdf (doi 10.1023/A:1023064908962)
- Plotkin, Pretnar. *Handling Algebraic Effects.* LMCS 9(4:23), 2013. https://arxiv.org/abs/1312.1399
- Kammar, Lindley, Oury. *Handlers in Action.* ICFP 2013. https://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf (doi 10.1145/2500365.2500590)
- Kammar. *An Algebraic Theory of Type-and-Effect Systems.* PhD thesis, Edinburgh, 2014 (eq. (11.1), Thm 12.5, Thm 12.8). https://www.cs.ox.ac.uk/people/ohad.kammar/publications/kammar-ohad-thesis.pdf — for Kammar & Plotkin, POPL 2012, doi 10.1145/2103656.2103698
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Handle with Care: Relational Interpretation of Algebraic Effects and Handlers.* POPL 2018. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl18.pdf (doi 10.1145/3158096)
- Staton. *Instances of Computational Effects: An Algebraic Perspective.* LICS 2013. https://www.cs.ox.ac.uk/people/samuel.staton/papers/lics2013.pdf
- Møgelberg, Staton. *Linear Usage of State.* LMCS 10(1:17), 2014. https://arxiv.org/abs/1403.1477
- Ahman, Bauer. *Runners in Action.* ESOP 2020. https://arxiv.org/abs/1910.11629
- Katsumata, Rivas, Uustalu. *Interaction Laws of Monads and Comonads.* LICS 2020. https://arxiv.org/abs/1912.13477
- Congard, Munch-Maccagnoni, Douence. *Linear Effects, Exceptions, and Resource Safety: A Curry-Howard Correspondence for Destructors.* ESOP 2026. https://arxiv.org/abs/2510.23517 (v2)
- Hillerström. *Foundations for Programming and Implementing Effect Handlers.* PhD thesis, Edinburgh, 2022. https://era.ed.ac.uk/handle/1842/38868
- Xie, Brachthäuser, Hillerström, Schuster, Leijen. *Effect Handlers, Evidently.* ICFP 2020; extended version MSR-TR-2020-23. https://www.microsoft.com/en-us/research/uploads/prod/2020/07/evidently.pdf
- Ma, Ge, Lee, Zhang. *Lexical Effect Handlers, Directly.* OOPSLA 2024 (extended version). https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024-tr.pdf
- Ma, Ge, Jung, Zhang. *Zero-Overhead Lexical Effect Handlers.* OOPSLA 2025. https://cs.uwaterloo.ca/~yizhou/papers/zero-oopsla2025.pdf

Relayed:
- de Vilhena, Pottier. *A Separation Logic for Effect Handlers.* POPL 2021 (via the P10 and P8 menus).
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Binders by Day, Labels by Night.* POPL 2020 (via the survey and the P10 menu).
- Zhang, Myers. *Abstraction-Safe Effect Handlers via Tunneling.* POPL 2019 (via the P2 menu).
- Ahmed, Dreyer, Rossberg. *State-Dependent Representation Independence.* POPL 2009 (via TR §13.4).
- Levy, *Adjunction models for call-by-push-value with stacks*; Curien, Fiore, Munch-Maccagnoni, POPL 2016 (via TR §13.1).
- Leroy. *A formally verified compiler back-end.* JAR 2009 (via Lexa Thm 1).

Ours (read in the repositories):
- `borrow-core-targets/experiments/Targets`: `Targets/A/Soundness.lean` (S4), `Targets/A/Binary.lean` (A₂), `Targets/A/Lowering.lean` (A₃), `Targets/Instance/Binary.lean` (Core's `Laws`, `Hiding`, `CapEta`, `Tunnel`), `Targets/Instance/ZeroCost.lean`, `Targets/I/Interface.lean` (`I5`, `I4c`), `Targets/I/Device.lean` (`P11`), `Targets/I/Restricted/Device.lean` (`i5beta`, `i5_core`, `p11_core`, `redLaws_of_mono`), `AGREE.md`, `RESTRUCTURE.md` §1.5, §1.7.
- `borrow-core`: `Core/EffRules.lean` (`ewp_handle`, `ewp_kappa_resume`, `handle_compatC`); `experiments/CoeffectsStrict/CoeffectsStrict/Handler.lean`; `experiments/EffModelRel` (`Laws.lean`, `Ownership.lean`, README); `docs/effects-tr/07-laws.md`, `13-adjunction.md`; `docs/effects-state/BRIEF.md`, `05a` (OQ-22, OQ-23, OQ-27), `05b` (OQ-49, OQ-50).
