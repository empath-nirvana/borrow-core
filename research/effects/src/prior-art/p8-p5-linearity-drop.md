# Prior art: P8 continuation linearity and P5 / I3 drop finalisation

This chapter surveys the literature for two properties and ends in a menu of options. It does not recommend one.

- **P8, continuation linearity.** A continuation is used as its qualifier says. A linear one is used exactly once. An affine one is used at most once, and when it is not resumed it is cancelled explicitly.
- **P5 / I3, drop finalises exactly once.** Dropping a suspended computation runs every finaliser of its frames exactly once, innermost first, and ends every lend it holds. Owned resources are released exactly once.

**Decisions that bound the menu** ([decided constraints](../decisions.md)):
- the core is linear;
- discard is an explicit cancel that runs finalisers, and there is no `forget`;
- cancellation is what SPEC §19 builds (decision 62);
- handlers are deep;
- multi-shot is ignored as a design goal (decision 63), and appears below only as context;
- errors are `raise`.

**Verification marks.**
- **[read]**: quoted from the primary PDF or page, fetched and read for this chapter.
- **[relayed]**: taken from our survey or from a secondary source that quotes it. Not re-read here.
- **[unverified]**: could not be checked.

Theorem numbers are those printed in the cited version.

---

## Menu at a glance

The options are independent along four axes:
- how P8 is stated and proved (rows 8.x);
- how P5 is stated and proved (rows 5.x);
- the interception policy (rows X.x);
- finaliser rows (rows F.x).

"Ours today" marks where `experiments/Targets` and Core sit now (§6).

| # | option | statement shape | what it buys | main cost | literature | ours today |
|---|---|---|---|---|---|---|
| 8.1 | Capturing condition, typing side | syntactic capture lemma over typing derivations | names the cause: no linear thing in a multi-use context | inversion and substitution over `CDerives` (D21 cost) | Tang Thm 3.4; Affect §2.4, §4.3 | enforced by the rules (`[let]`, `contShare` at `unr`, `!` clauses), not stated as a lemma |
| 8.2 | Tagged conservation | instrumented semantics; `ℒ(M) ∪ S = ℒ(N) ∪ T` per step | per-step "never duplicated or discarded"; tells equal values apart | a second semantics, an erasure lemma, syntactic subject reduction (OQ-50 (a)) | Tang Thm 3.6 | not built |
| 8.3 | One-shot cell in the machine | κ carries a location; a use flips or frees it; safety gives at most once | at most once from safety; in a linear core, exactly once from adequacy's empty heap | machine change (OQ-50 (b)); S4 excludes it as stated | Hazel R6 and Thm 4.1; Affect §3.1–3.2; Yarrow | excluded by S4 (AGREE Q9) |
| 8.4 | Ghost obligation in the relation | κ's share owns a non-persistent obligation, consumed by resume or cancel | machine unchanged; reuses `contShare`'s wand | the run-level statement needs a coupling from ghost to step | Hazel law A1 (non-persistent wand); Affect EWP-Handle | named as a route to `ContUse` (RESTRUCTURE §1.5); not built |
| 8.5 | Observational use counts on runs | counts of catches, resumes and cancels along every run | states P8 with no instrumented semantics; fails R1–R4 | per-value counting; equality only on complete runs at data answers | none found in this shape | **S6 `ContUse`**: stated; open at our instance |
| 8.6 | Resource half only | no leak and no double release (B4 with B5) | free from adequacy | blind to a κ that holds nothing (OQ-50 text) | Congard Prop 6, Thm 12 | B4, B5 in `B.Guarantees`; `P8a` retired |
| 5.1 | Event traces of cancel and unwind | every run from a cancel follows a trace: fire innermost first, error policy | states §19 as built, observably | trace definitions per machine; bridges | none in this shape; nearest is Ahman–Bauer Thm 7 | **S5 `Cancellation`**: stated; open at our instance (`noInterception_tier1` proved at Core σ=[]) |
| 5.2 | Denotational factoring | the denotation of a run factors through the finalisation map | finalisation on every branch, as one equation | a denotational model; runners' tail-position, at-most-once discipline | Ahman–Bauer Thm 7 | not used (runners not user-facing) |
| 5.3 | Instrumented resource invariant | labels open or closed; `ActiveOpen ∧ InactiveClosed` preserved per step | cheap; one case analysis | close to a tautology: the instrumentation is the machine's own frame push and pop | Voigt et al. Thm 3.6 | not used |
| 5.4 | Exactly once via empty memory | the resource list at the end equals the start (LIFO), or a permutation of it | the memory half of P5 with no new semantics | needs every finaliser obligation to be a resource | Congard Prop 6, Thm 10, Thm 12 | B2, B4, B5 |
| 5.5 | Tagged finaliser frames | each `[then]` frame tagged at push and closed exactly once (return, unwind or cancel) | a global "each finaliser at most once, and exactly once on complete runs" | tags on frames; as 8.2 | Tang's technique applied to frames (synthesis) | not built; S5 is per event, not global |
| 5.6 | Lends ended by the cancel | the cancel's end holds no lend its start did not | the "ends every lend" clause | needs OQ-57's closing list | Yarrow's region revocation is the nearest | `ShareCancel`'s closing clause proved at σ=[]; `CancelCloses` named only |
| X.1 | Catchable, must re-raise | cleanup sees the cancel and must propagate it | libraries that clean up on unwind keep working | by convention unless enforced | libstdc++ `__forced_unwind` | §19's `ubind` is this, with re-raise **enforced** by `[cfin-ret]` |
| X.2 | Uncatchable forced unwind | nothing catches the cancel; only finalisers run | the cancel always completes | catch-all cleanup must become finalisers | Rust's "drop the future" (relayed) | **§19 as built** (with X.1's finaliser frames) |
| X.3 | Interceptable, re-linearised | the cancel is an exception the region may catch and continue from | OCaml compatibility | the region resumes after a cancel; the canceller must be re-obliged | OCaml `discontinue` | rejected by §19's stated reason |
| F.1 | Finalisers abortive-only | `D : F_{Σ^abort} 1`, plus answering calls | no finaliser reaches a dying handler | no awaiting, joining or async cleanup in a finaliser | Koka `finally` (abort path) | **as built** |
| F.2 | Resuming finalisers, outer handlers only | `D` may suspend at handlers outside the region | async cleanup (join, flush, await) | a suspension inside a cancel: κ holds `cfin` frames; no row knows the region statically | Voigt et al. (effects in finalisers, dynamic) | OQ-7 (a), open |
| F.3 | Finalisers that must not fail | the finaliser row has no abortive operation | no error channel needed | rejects fallible cleanup | §19 *Open* | listed in §19 *Open* |

---

## 1. Canonical statements, and how each is realised and proved

### 1.1 Tang, Hillerström, Lindley & Morris, *Soundly Handling Linearity* (POPL 2024) [read]

**Calculus.** F°eff is a fine-grain call-by-value System F with linear types, Rémy-style rows and deep handlers. Every operation carries a control-flow linearity `Y ∈ {•, ◦}`: `•` is unlimited and `◦` is linear. There are two points, with no affine point.

**Typing side.** "**Theorem 3.4 (Unlimited is unlimited).**"
1. "Unlimited values are unlimited: if Δ; Γ ⊢ V : A and Δ ⊢ A : •, then Δ ⊢ Γ : •."
2. "Unlimited continuations are unlimited: if Δ; Γ ⊢ E[(do ℓ V)^E] : C for E = {ℓ : A ↠• B ; R} and ℓ ∉ bl(E), then there exists Δ ⊢ Γ = Γ1 + Γ2 such that Δ ⊢ Γ1 : • and Δ; Γ1, y : B ⊢ E[(return y)^E] : C."
3. "Deep handlers are unlimited: if Δ; Γ ⊢ H : C ⇒ D, then Δ ⊢ Γ : •."

**The rule that enforces it.** T-Seq types `let^Y x ← M in N` with the premises `Δ ⊢ Γ2 : Y` and `Δ ⊢ R : Y`. When Y = ◦, "N may use some linear variables bound outside (Δ ⊢ Γ2 : ◦), and all operations in M should be control-flow linear". T-Handler types each resumption `r_i` at the operation's own linearity `Y_i`, and requires `Δ ⊢ Γ : •` of a deep handler "because they are recursively applied during evaluation".

**Semantic side.** The semantics is linearity-aware. A step `M ↝^S_T N` records the linear values it introduces (`S`) and eliminates (`T`). Values are tagged `V°` when first bound. "Definition 3.5 (Linear Safety)" says there are no tagged values inside unlimited values, inside the context of an unlimited operation, or inside handlers.

"**Theorem 3.6 (Reduction Safety).** For any closed, well-typed and linear safe computation M in F°eff, if M ↝^S_T N, then N is linear safe and ℒ(M) ∪ S = ℒ(N) ∪ T."

The authors add: "tracking linear values explicitly during evaluation is important for showing that they are indeed used safely. Otherwise, it is even unclear how to state what reduction safety means in the original semantics."

**Proof.** The proof is syntactic. It uses Progress (Thm 3.2), Subject Reduction (Thm 3.3), and Lemmas A.3 ("Linear variables appear exactly once") and A.4 (linear safety is preserved under substitution).

**What it does not cover.**
- F°eff has no cancel and no finaliser. A linear (◦) continuation must be resumed exactly once.
- A discarding clause, such as Links' `Fail`, can only be typed when the discarded context holds nothing linear. "For Fail the captured continuation is discarded (it must be: it is never bound)".
- So exceptions and linear resources do not mix in F°eff except by keeping linear resources out of the raising context.

**The Links bug** (§1). A session-typed program performs `Choose` and then `Fail`, under a handler that resumes `Choose` twice and discards `Fail`'s continuation. It sends two integers on a channel whose protocol expects an integer and then a string, and "running the program causes a segmentation fault".

### 1.2 van Rooij & Krebbers, *Affect: An Affine Type and Effect System* (POPL 2025) [read]

**Statement.** "Theorem 2.1. Every closed well-typed program is safe w.r.t. the operational semantics." Safety "also captures that continuations corresponding to one-shot effects are resumed at most once".

The safety predicate (§3.2) is `safe e := ∀ e′ σ′. e / ∅ →* e′ / σ′ ⇒ e′ ∈ Val ∨ (∃ e″ σ″. e′ / σ′ → e″ / σ″)`. Type soundness is `⊢ e : ⟨⟩ : τ ⊣ ⇒ safe e`.

**Realisation of one-shot: a cell in the machine.**
- A continuation value is `cont ℓ N`.
- "a location ℓ is associated with continuation values cont ℓ N, and the heap is abused to track if the continuation has been resumed. Application of a one-shot continuation (Red-Cont) is only defined when it has not been called yet".
- So a second use is a stuck state, and safety excludes it.
- The technique is credited to de Vilhena and Pottier.

**The capturing condition** (§2.4). "when performing an effect do op e1; e2, either the effect op is one-shot, or the effect op is multi-shot and the remainder of the computation e2 is unrestricted (i.e., e2 does not capture any affine variables)."

The paper warns that "constructs such as application and binary arithmetic operators implicitly perform sequencing, so their corresponding typing rules need to incorporate this condition". Affect enforces the condition with a two-context judgement and with modes on types (`!`, `¡`).

**Proof.** The proof is semantic. A logical relation in Iris is built over AffectLogic's `ewp`, and its adequacy theorem reads: "if True ⊢ ewp e {Φ} is derivable, then e is safe".

In the handler rule (EWP-Handle) the continuation's specification is `□^m (∀ w. κ w −∗ ewp v_k w ρ {Φ′})`. It is persistent only when the mode `m` is multi-shot: "Multi-shot signatures allow the weakest precondition for v_k to be persistent and thus allow k to be called more than once".

**Why Affect is affine.** "One-shot effects in AffectOS are affine instead of linear, i.e., their continuations should be resumed at most once instead of exactly once. Affine effects are necessary to support Except from § 2.1 (whose continuation is not resumed) without the need to explicitly 'discontinue'/'free' the continuation." (§3.3)

**Future work** (§7): "investigate a linear (instead of affine) version of Affect with a 'discontinue' operation for unused continuations".

### 1.3 de Vilhena & Pottier, *A Separation Logic for Effect Handlers* (POPL 2021; Hazel) [read]

**One-shot check in the machine.** Rule R6: "Provided ℓ contains true, an application of this continuation to a value w reduces to N[w] … Furthermore, ℓ is updated with false, so another attempt to apply this continuation will be stuck. This is the one-shot check."

**One-shot in the logic.** Protocol law A1 has no persistence modality. "Opponent, who is allowed to exploit this implication, may exploit it at most once. This will have the consequence that a captured continuation can be invoked at most once." The paper adds: "If a persistence modality was inserted in front of the implication … then this frame rule would not hold."

**Statement.** "Theorem 4.1. Let e be closed. If ⊢ ewp e ⟨⊥⟩{Φ} holds then executing e in an empty heap is safe … Because our operational semantics includes a one-shot check, the absence of crashes implies that, during the execution of e, no continuation is invoked twice."

**About the term "ghost token".** In Hazel, one-shot is a **non-persistent wand**, enforced against a **physical** flag in the machine. It is not a ghost cell. Our survey's "ghost token" (A3) is a fair reading of the logical half only. Whether Iris-WasmFX uses a literal ghost token is [unverified].

**Linear as future work** (§8): "an intriguing idea is to view one-shot continuations as linear instead of affine. Every one-shot continuation would then have to be either invoked or explicitly discarded … the primitive operation that discards a continuation would resume the suspended computation by raising an exception inside it. This would guarantee that every code block, once entered, must be exited, either normally or via an exception."

Footnote 5 records the cost of affinity in their own case study: if the user stops iterating early, "she has no way of recovering the ownership of the collection. We believe that this problem could be remedied by imposing a linear usage of continuations, combined with a discontinue operation".

**Related.** The companion type system *A Type System for Effect Handlers and Dynamic Labels* (ESOP 2023, TES) is [unverified] here.

### 1.4 Voigt, Schuster & Brachthäuser, *Dynamic Wind for Effect Handlers* (OOPSLA 2025, System Ξ↬) [read]

**Mechanism.**
- A handler has `on suspend`, `on resume` and `on return` (finally) clauses.
- Suspend clauses run while the continuation is being captured: "Since we cannot be sure whether the continuation will be discarded or resumed, we need to ensure that all resources are released during the continuation capturing (stack unwinding)."
- Finalisers may themselves perform effects and capture continuations, multi-shot included.

**Soundness.** "Theorem 3.3 (Progress)", "Theorem 3.4 (Preservation)", "Theorem 3.5 (Soundness)".

**Resource safety, §3.4.4.** The abstract machine is instrumented with a resource environment `R` that maps labels to 1 (open) or 0 (closed). `(try)` sets `R(l) = 1`, `(return′)` and `(suspend)` set it to 0, and `(resume′)` sets it back to 1.
- "ActiveOpen(M) := ∀li ∈ active(M.E), M.R(li) = 1"
- "InactiveClosed(M) := ∀li ∈ R \ active(M.E), M.R(li) = 0"
- "**Theorem 3.6 (Resource Safety).** If ActiveOpen(M) and InactiveClosed(M) and M −→ M′, then ActiveOpen(M′) and InactiveClosed(M′)."

**Proof.** "case analysis on the step … these cases fulfill the property of Resource Safety by construction."

**Caveat, in their words.** "These invariants are not statically checked, but rather represent a set of best practices that users should follow." The instrumentation flips with the machine's own push and pop of finaliser frames. The theorem therefore says that the instrumentation is consistent with the stack. It does not say that user resources are released.

**Koka, as Voigt et al. report it** (§6.3). Leijen 2018 "propose[s] to manually finalize continuations, which resume with a special finalization exception that unwinds the continuation and invokes the finalizers contained therein. They conjecture but do not prove that all finalizers are executed."

**OCaml, as they report it.** OCaml requires linear use "but do[es] not statically enforce this".

### 1.5 Ahman & Bauer, *Runners in Action* (ESOP 2020) [read]

**Claim.** The introduction claims "a strong guarantee that in the absence of external kill signals the finalisation code is executed exactly once (Thm. 7)".

**Statement.** "**Theorem 7 (Finalisation).** A well-typed run factors through finalisation: ⟦Γ ⊢ (using V @ W run M finally F) : Y ! (Σ′, E′)⟧ γ = φ†_γ t, for some t ∈ Tree_Σ′((⟦X⟧ + E) × ⟦C⟧ + S)." That is, "a computation tree all of whose branches end with finalisation clauses from F".

**Proof.** By computational induction on the runner's denotation.

**What makes it work.** "runners are simply a restricted form of handlers, which apply the continuation at most once in a tail call position". Linearity of the kernel state comes "not through a linear or uniqueness type system … but rather by a design based on the linear state-passing technique studied by Møgelberg and Staton".

**Related work.** On parameter-passing handlers: "There is however no guarantee of finalisation happening because handlers need not use the continuation linearly."

### 1.6 Congard, Munch-Maccagnoni & Douence, *Linear Effects, Exceptions, and Resource Safety: A Curry-Howard Correspondence for Destructors* (ESOP 2026; arXiv 2510.23517v2) [read]

**Problem.** The paper frames linearity with exceptions as giving a strength for `T(− ⊕ E)` in a linear setting. A strength with respect to `!` "amounts to precluding any linear variable from appearing in the monadic binding … linearity and control effects are exclusive with one another". This is the same restriction as Tang's T-Seq at `•` and our `[let]` at `unr`.

**Calculus 1** is linear and ordered CBPV with `new` and `delete`.
- "Proposition 6. For any value v and lists of resources l, l′, if ⟨t ∣ ⋆ ∣ l⟩ ⇝* ⟨v ∣ ⋆ ∣ l′⟩ then l′ = l." This holds for closed `t` at a purely positive, resource-free type, and gives LIFO from ordered typing.
- With exchange: "Theorem 10 … there exists a permutation σ of lists of resources such that l′ = σ(l)."

**Calculus 2, resource CBPV.**
- It has exceptions and a destructor `δ : A → T I` for every type, so weakening and exchange perform effects.
- "Theorem 12 … if ⟨π1⟦t⟧ ∣ ⋆ ∣ l⟩ ⇝* ⟨v ∣ ⋆ ∣ l′⟩ then l′ = σ(l) for some permutation σ. Moreover, if the expression does not contain 'move', then l′ = l."
- Summary (§6.1): "every allocated resource … is freed exactly once, even in case of errors during the execution of the program … the resources are released in a LIFO order."

**Exceptions must carry nothing.** "Proposition 15. Given an object E, the three following properties are equivalent: E is in the Drinfeld centre of C; E is resource-free …; E has a trivial destructor." Exception payloads must be resource-free.

**Scope.** Exceptions only. There are no resumable handlers and no continuations as values.

### 1.7 Fowler, Lindley, Morris & Decova, *Exceptional Asynchronous Session Types* (POPL 2019; EGV) [read]

**Position.** "Linear Types with Explicit Cancellation" (§1.4), after Mostrous and Vasconcelos: "(They characterise their sessions as affine, but it is important not to confuse their system with affine type systems … which allow variables to be discarded implicitly.)"

**Semantics.**
- "E-Raise … invokes the otherwise clause if an exception is raised, while also cancelling all endpoints in the enclosing pure context."
- `cancel` creates a zapper thread, and E-Zap cancels the endpoints in a cancelled buffer transitively.

**Effect handlers** (§5.4). Exceptions translate to `raise r ↦ cancel r ; ⟦N⟧`, "assuming the natural extension of cancellation to arbitrary linear values, whereby all free names in the value [are cancelled]".

**Theorems.** Preservation (Thm 3.2, 3.3), Progress (Thm 3.9, 3.10), Global Progress (Thm 3.11), Diamond (Thm 3.12), Strong Normalisation (Thm 3.13).

**Cancellation runs no user code.** It is a structural release of every name in the dropped context.

### 1.8 OCaml 5 `discontinue` [read]

**Manual** (*Effect handlers*, "Linear continuations"): "The delimited continuations in OCaml must be used linearly – every captured continuation must be resumed either with a continue or discontinue exactly once. Attempting to use a continuation more than once raises a Continuation_already_resumed exception."

It goes on: "there is no check to ensure that the continuations are resumed 'at least once' … Not resuming continuations will leak the memory allocated for the fibers as well as any resources that the suspended computation may hold."

**Sivaramakrishnan et al., PLDI 2021.**
- `discontinue k e` "raises the exception at input_line call site".
- In the formal semantics, `discontinue k l e = (k (λo x. raise l x)) e`, so a `try` inside `k` can catch the exception.
- The leak workaround: `Gc.finalise (fun k -> try ignore (discontinue k Unwind) with _ -> ()) k`, which works "assuming that user code does not handle Unwind exception and fails to re-raise it".

### 1.9 Koka finalisers [read: book; relayed: technical report]

**The book.**
- `finally` "is always executed when either returning normally, or when unwinding for a non-resuming operation".
- With `raw ctl`, `rcontext.finalize` "runs all finally handlers to clean up resources … it is now the programmers' resposibility [sic] to ensure the resumption is eventually resumed or finalized".
- The "Linear Effects" section is marked "Todo".

**The technical report.** Leijen, *Algebraic Effect Handlers with Resources and Deep Finalization*, MSR-TR-2018-10, could not be downloaded. The "conjecture but do not prove" quote is relayed through Voigt et al. §6.3. Whether Koka's finalisation exception can be caught by user code is [unverified], as the survey already noted.

### 1.10 Library contracts that a forget breaks [read]

- **Rust RFC 1066:** "It has never been a guarantee of Rust that destructors for a type will run, and this aspect was overlooked with the `thread::scoped` API which requires that its destructor be run!"
- **`std::pin`, the drop guarantee:** "in any situation where we may want to overwrite a pinned value, that value's drop must be called beforehand". Leaking is allowed: "leaking memory in such a way that its underlying storage will never get invalidated or re-used is still fine".
- **libstdc++ thread cancellation:** `catch(const __cxxabiv1::__forced_unwind&) { …; throw; }`. This is the catch-must-re-raise convention.
- **Relayed** (survey §2 P2): `std::thread::scope` runs `catch_unwind` and then joins; without.boats' "scoped task trilemma"; the `async-scoped` crate.

### 1.11 Yarrow (Mathiasen, Timany & Birkedal, arXiv 2607.15876) [read: abstract and §3]

- "multi-shot effect handlers break the invariant that regions can be exited at most once".
- One-shot continuations carry a location "used to enforce the affinity of one-shot continuations". This is the Hazel and Affect technique again.
- Regions use "temporary revocation for one-shot effects and permanent revocation for multi-shot effects". This is the nearest published analogue of "a dropped continuation ends the lends it holds".

---

## 2. The statement shapes, side by side

The sources state "used as the qualifier says" and "finalised exactly once" in six shapes. They are different theorems, not one theorem in six notations.

| shape | example | what it observes | at most once | at least once | needs |
|---|---|---|---|---|---|
| (a) capture lemma | Tang Thm 3.4(2) | typing derivations | indirectly | no | inversion |
| (b) tag conservation | Tang Thm 3.6 | instrumented steps | yes, per step | per step, with no discard | tagged semantics and linear safety |
| (c) stuck on second use | Affect Thm 2.1; Hazel Thm 4.1 | a physical flag | yes | no | machine change |
| (d) resource list at the end | Congard Prop 6, Thm 12; our B2, B4, B5 | heap at a final state | yes, for resources | yes, for resources, on terminating runs | a resource per obligation |
| (e) denotational factoring | Ahman–Bauer Thm 7 | denotation | built in | every branch | a model; runner discipline |
| (f) instrumented invariant | Voigt Thm 3.6 | instrumented machine | by construction | by construction | instrumentation |

Our S6 is a seventh shape, **(g) observational counts**, read off plain runs. Our S5 is an eighth, **(h) event traces**. Both are §6's subject.

**Three facts the table shows:**

1. **At least once is never a safety property.**
   - Every source that gets "exactly once" restricts it to terminating runs. Congard: "either reduces indefinitely, or there exists a final value". S6's equality conjunct holds only on complete runs at a data answer.
   - None claims it on diverging runs. Ahman–Bauer exclude "external kill signals".
2. **"At most once" comes cheaply from shape (c) or from a non-persistent wand.** "At least once" comes cheaply only in a linear system where the obligation is a **resource** that adequacy forces to be released: shape (d). This is exactly the advantage the linear core gives us (§4).
3. **Shape (f) can collapse into a restatement of the machine.** Voigt et al. say their invariant holds "by construction", and that it encodes "best practices". Our retirement of `ReleasedOnceAll` and `P8a` as "a tautology about runs" is the same lesson. Any instrumented statement should be checked to fail on R1–R4-style witnesses.

---

## 3. Pitfalls

1. **The Links bug** (Tang §1). A linear session endpoint was captured by a continuation that was resumed twice and also discarded. That gave a segfault in a type-checked program.
   - *Ours:* `unr` κ has an empty share (`contShare`, `Core/EffDefs.lean:144–149`), and `[let]` requires `!Γ₂` at a row with an `unr` operation. Multi-shot is out of scope anyway.
2. **Hidden sequencing** (Affect §2.4). In an ML-style language, application and arithmetic sequence implicitly, and each such rule must carry the capturing condition.
   - *Ours:* in CBPV the only sequencing former is `M to x. N` (`[let]`, `[then]`). The condition lives at one rule. Elaboration must not introduce sequencing outside it.
3. **Deep handler clauses are reused** (Tang Thm 3.4(3); Affect's persistent branches).
   - *Ours:* `[handle]` takes clauses as `!U(…)`.
4. **Affine weakening breaks library contracts.** Survey cases S1–S3 (`thread::scope`, `replace_with`, `Pin`) depend on "the destructor runs". RFC 1066 records that Rust gave this up.
   - *Ours:* there is no `forget` at `lin` and `aff`. `cancelOwed` is part of κ's share at `aff`, and `NoOwn` at the end of adequacy rules out a silently dropped κ that owns something.
5. **A dropped continuation that holds nothing is invisible to the resource half.** The OQ-50 text says so: "`NoOwn` … cannot see a dropped or duplicated `κ` that holds nothing owned."
   - Option 8.6 alone therefore does not state P8. S6 exists for this reason.
6. **Interception of the discard.**
   - OCaml's leak cleanup is sound only "assuming that user code does not handle Unwind exception and fails to re-raise it".
   - A catchable discard lets the region continue after the canceller believes it is gone.
   - §19 removes the problem structurally (§5.3).
7. **0-shot and 1-shot are incomparable once linear values exist** (survey A3, synthesis). In Tang, the clause that discards `Fail`'s continuation is typable only when that continuation captures nothing linear.
   - Our `aff` = {0 via cancel, 1} is not the `[0,1]` of an affine system. It is EGV's "linear with explicit cancellation". This naming matters when comparing with Affect: our `aff` corresponds to Affect's future-work linear system, not to Affect.
8. **Finalisers that perform effects.**
   - A non-abortive operation in a finaliser during a cancel could reach a dying handler that answers without resuming, "and the region would then continue as if not cancelled" (SPEC §19, *Typing*).
   - Voigt et al. allow effects in finalisers, and their resource theorem is the instrumented one.
   - Eager finalisation at suspension degenerates to blocking for obligations that cannot be re-acquired, such as running threads (survey §2 P2, synthesis).
9. **Exception payloads must carry nothing** (Congard Prop 15).
   - *Ours:* `[raise]`'s argument drops (`VTy.Drop`), and `errOk` requires `NoOwn`. These are the same condition.
10. **Counting per value conflates equal continuations** (RESTRUCTURE §1.5: "Two catches that hand out equal values are counted together"). A run that catches equal κ twice, resumes one twice and drops the other satisfies S6's counts.
    - When κ holds resources, B4 and B5 catch the double use.
    - When it holds nothing, no observation tells the two apart.
    - Shapes (b) and (c) distinguish them by tag or by location.
11. **Dynamic checks are not static guarantees.** OCaml checks "at most once" at run time and "at least once" not at all. Ante documents `resume` as at most once but does not enforce it (ante-deep-dive, probes `p1`, `q5`).

---

## 4. Linear versus affine

**What the literature says linearity costs.**

- **Exceptions need destructors, or else linear values must be kept out of raising contexts.**
  - Congard et al. make this precise: a linear strength for `T(− ⊕ E)` exists once every type has a destructor `δ : A → T I` (Theorem 1, Prop 16 and 17).
  - Without destructors, "linearity and control effects are exclusive with one another". That is Tang's position: a discarding clause only over unlimited contexts.
  - *Our realisation:* the `[let]` side condition at an abortive or affine row ("Γ₂ drops: NoOwn, or use [then]"), plus elaborator-inserted `[then]` drop glue.
- **Every continuation must be consumed.**
  - Affect chose affinity to avoid "the need to explicitly 'discontinue'/'free' the continuation".
  - Our cost is elaborator-inserted cancels (foundations/linearity.md).
- **Proof cost of "at least once".**
  - Affect and Hazel both list a linear version with `discontinue` as future work. No mechanised linear effect system with explicit discontinue was found.
  - EGV proves its theorems on paper. Congard has exceptions without resumable handlers.
  - This is a gap in the literature, not evidence against tractability.
- **Practical history.** Congard §6.1 recounts that Cyclone "permitted resource leaks in the name of 'flexibility and usability'", and that Tov and Pucella made their practical system affine because of control effects.

**What becomes tractable with a linear core (our case).**

- **Exactly once for owned resources is shape (d)**, read off adequacy's empty memory. It is already proved for today's rules (B2, B4) and stated with reuse (B5). The affine systems cannot state it, because their adequacy has no empty-heap conclusion.
- **Exactly once for κ reduces to making κ's use an owned obligation**: options 8.3 and 8.4. In an affine system the same device would only give at most once.
- **The interception choice shrinks.** With no `forget`, the only way to discard is the cancel, so the policy is a property of one primitive.
- **Library contracts that need "the destructor runs"** (§3 item 4) hold for any code that cannot forget. Leaking is ruled out at `lin` and `aff`, and the `std::pin`-style "leak forever is fine" escape does not arise.

**What linearity does not buy.**
- Lifetimes (P9), exclusivity (P10) and lends spanning a suspension (P4).
- The "ends every lend" half of P5, which needs OQ-57's accounting.
- Termination. Every "exactly once" stays restricted to terminating runs.

---

## 5. The menu

Each entry gives:
- **shape**: the statement;
- **cost**;
- **buys**: what it gains;
- **interacts**: with our decisions and the other properties;
- **evidence**.

### 5.1 P8: how continuation use is stated

**8.1 Capture lemma (typing side).**
- *Shape:* for `CDerives`, if `Γ ⊢ K[perform_{n,i} v] : F_Σ A` with `n` free in `K` and the operation `unr`, then the part of `Γ` that `K` uses is persistent. At `lin` and `aff` there is no restriction. This is Tang Thm 3.4(2) at our rules.
- *Cost:* inversion over `CDerives`. D21 asks for such work to be taken on "only with the cost stated".
- *Buys:* it explains why S6 holds, and serves as a lemma for 8.2.
- *Interacts:* it is meaningful only at `unr`, which is ignored (decision 63). Tang Thm 3.4(3) (deep handlers unlimited) is the `!` premise of `[handle]`.
- *Evidence:* the rules exist: `[let]`'s `!Γ₂` premise (`Core/EffRules.lean:897`) and `contShare` at `unr`. No lemma.

**8.2 Tagged conservation (Tang Thm 3.6 at our machine).**
- *Shape:* an instrumented step `c ↝^S_T c′` that tags κ at the catch and untags it at its resume or cancel. Statement: `ℒ(c) ∪ S = ℒ(c′) ∪ T`, with linear safety preserved. "Not discarded" is the equality on a final configuration where `ℒ = ∅`.
- *Cost:* a second semantics plus an erasure lemma, and OQ-50 (a)'s subject reduction at Core's typing of configurations. That is per-rule work, which D21 asks to have costed.
- *Buys:* a per-step statement, and it tells equal values apart (§3 item 10). It extends to owned values, not only κ.
- *Interacts:* the tags are erased at run time, so the erasure decision is untouched. It would also give 5.5 if frames are tagged too.
- *Evidence:* RESTRUCTURE §1.5 names "subject reduction at Core's typing of configurations" as one route to `ContUse`. Nothing is built.

**8.3 One-shot cell (Affect, Hazel, Yarrow; OQ-50 (b)).**
- *Shape:* the catch allocates a cell for κ, and resume and cancel free it.
  - At most once: a second use is stuck, so adequacy's "never stuck" excludes it.
  - Exactly once: an unused κ leaves its cell allocated, so adequacy's empty memory excludes it.
- *Cost:*
  - a machine change;
  - S4 as stated excludes it twice over ("`capture l H K` is a value … under (b) the clause would get a fresh location"; the laws are `PureJoin`);
  - B5's bump-run simulation must account for the extra cells;
  - erasure needs a simulation lemma from the machine with cells to the machine without them.
- *Buys:* in a linear core, both halves of P8 come from B2 and B4, which are already proved for today's rules. This is the cleanest "exactly once via the empty heap".
- *Interacts:*
  - AGREE Q9 is this choice.
  - It changes B's machine, so "nothing breaks the borrow calculus" needs B1–B5 re-run at the new machine.
  - It is orthogonal to S5.
- *Evidence:* the technique is mechanised in Iris (Hazel, Affect, Yarrow) for at most once. For us it is PAPER-ONLY (`docs/effects-tr/12-sources.md` §12.3 item 4, as cited in OQ-50).

**8.4 Ghost obligation in the relation.**
- *Shape:* `contShare` at `lin` and `aff` additionally owns a ghost obligation for κ. Resume and cancel consume it, and `NoOwn` at the end forces every caught κ to be used.
- *Cost:*
  - a ghost component in the world, which touches B's world, though it carries no physical resource;
  - the statement problem: a ghost resource proves an internal fact, and S6 is about runs. To transfer it, the relation must couple each consumption to the step that resumes or cancels κ, or the run must be instrumented, which falls back to 8.2.
- *Buys:* the machine stays unchanged, so S4 stands. It reuses Hazel's law A1 shape, which our `contShare` already has: a non-persistent wand at `lin` and `aff`.
- *Interacts:* with OQ-8 (where the Kripke quantifier sits) and with the one-world sign-off. A ghost index beside `W` would be a defect under ONEW.
- *Evidence:* named in RESTRUCTURE §1.5 ("the logical relation with a ghost token per continuation"). Not built. The coupling step is the unknown. I have not derived it and have not verified that any obstruction is real.

**8.5 Observational counts (S6 `ContUse`, as stated).**
- *Shape:* on every run, `uses ≤ caught` and `cancels ≤ caughtAff`. On a complete run at a data answer, `uses = caught`.
- *Cost:* proved through 8.2, 8.3 or 8.4. It is per-value, and equality holds only on complete runs.
- *Buys:*
  - a statement over any `EffectSystem`, with no instrumentation;
  - teeth: R1–R4 each have a breaking run, though those lemmas are not yet built;
  - it is the only shape that reads the use count from plain runs.
- *Interacts:* it fixes OQ-50 away from (c) and leaves (a) versus the ghost route open. It is compatible with 8.2 and 8.4. 8.3 needs S4 relaxed.
- *Evidence:* stated in `Targets/A/Soundness.lean`. Open at our instance.

**8.6 Resource half only (OQ-50 (c)).**
- *Shape:* B4 with B5.
- *Cost:* nothing new.
- *Buys:* every owned cell κ held is released once.
- *Interacts:* blind to a κ that holds nothing (§3 item 5). On runs without reuse it is the retired tautology.
- *Evidence:* B4 is proved for today's rules. B5 follows from B4′ given `BumpSim` (OQ-43).

**The multiplicity lattice** is `{0}`, `{1}`, `[0,1]`, plus `ω` for the ignored `unr`. Our qualifiers read `lin = {1}`, and `aff = {1} ∪ {cancel}`, which is not `[0,1]`. No option above needs a join on modes (Affect §7's "it might be useful to equip Affect with join ⊔ and meet ⊓", relayed by the survey). Mode polymorphism over `lin`/`aff` in callbacks is out of this chapter's scope.

### 5.2 P5: how drop finalisation is stated

**5.1 Event traces (S5, as stated).**
- *Shape:*
  - `NoIntercept`: every run from the start of a cancel of `capture l H K` follows a `CancelTrace` of `fins K`. Each finaliser fires innermost first, runs alone, and updates the kept error by `keep`. Last, the canceller is answered.
  - `UnwindOrder`: the corresponding trace for an ordinary raise.
- *Cost:* the trace definitions, and the bridges `noIntercept_of_core` and `unwindOrder_of_core`, not built.
- *Buys:*
  - §19's semantics as an observable spec;
  - "each once" is the trace consuming the list `fins K`;
  - LIFO is the list order.
- *Interacts:* per event, not global (see 5.5). It states nothing about the lends.
- *Evidence:* `noInterception_tier1` is proved at Core σ=[]. `FinaliserOrder` is open, with `two_frame` proved. E7 and E8 are concrete runs.

**5.2 Denotational factoring (Ahman–Bauer Thm 7).**
- *Shape:* ⟦run M finally F⟧ = φ† t.
- *Cost:* a denotational model of the kernel. Runners restrict handlers to "at most once in a tail call position", which excludes control handlers.
- *Buys:* "every branch ends in finalisation" as one equation.
- *Interacts:* runners are "not user-facing", and BoLo-as-runner is "not yet decided". A runner encoding of `withbor` might give the borrow constants' unwinding forms for free (synthesis). No step-indexing is not at issue for a denotational model.
- *Evidence:* paper only, for λcoop.

**5.3 Instrumented invariant (Voigt Thm 3.6).**
- *Shape:* labels open or closed, preserved per step.
- *Cost:* low.
- *Buys:* little. It holds "by construction", and for us it would duplicate `TW`'s frame bookkeeping.
- *Interacts:* it risks the tautology pattern (§2 fact 3).
- *Evidence:* paper.

**5.4 Exactly once via empty memory (Congard; B2, B4, B5).**
- *Shape:* the heap at the end equals the heap at the start, or is empty for a closed program. B5 adds the bump-run image for reuse.
- *Cost:* nothing new for owned cells. For finaliser effects that are not memory, such as closing a socket through a capability, it says nothing unless the obligation is a resource of the world.
- *Buys:* the memory half of P5 at once.
- *Interacts:* Congard gets LIFO from ordered typing (Prop 6). We get it operationally (5.1). An ordered discipline is not on our table, and BoLo is not ordered.
- *Evidence:* B4 is proved for today's rules. B5 is generic, modulo `BumpSim`.

**5.5 Tagged finaliser frames (synthesis from Tang's technique).**
- *Shape:* each `[then]` frame gets a tag when pushed. The tag is removed exactly once: by return (N runs and disposes Γ₂), by unwind (D fires), or by cancel (D fires under `cfin`). Statement: conservation per step, and an empty tag set on complete runs.
- *Cost:* as 8.2. It shares the instrumentation if both are built.
- *Buys:* the global form of "each finaliser exactly once", across nested cancels, unwinds and returns. S5's traces are per event and do not by themselves exclude a frame firing in one trace and again later.
- *Interacts:* with E9 (stored κ cancelled after its handler returned) and with tier 2, where frames spanning a stop are frozen in κ.
- *Evidence:* none. Whether S5 plus determinism already implies the global form has not been checked.

**5.6 Lends ended by the cancel.**
- *Shape:* `ShareCancel`'s closing clause says the cancel's end holds nothing its start did not. `CancelCloses` says every lend κ froze is ended.
- *Cost:* OQ-57's closing list `τ`, in one of three forms: as an index beside `W` (a, a defect under ONEW), a `closer` field on `σ` entries (b), or a split `σ` (c).
- *Buys:* the "ends every lend" clause of P5, which nothing else gives.
- *Interacts:* tier 2 (P4). At tier 1, no lend spans a stop, so the clause holds vacuously for spanning lends.
- *Evidence:* `i3_core` is proved at σ=[]. GhostEnd's `spans_two_affine_yields` covers the cancel path (Core σ=[]).

### 5.3 Interception policy: where §19 sits

§19 is decided: "Whatever they do is what we decided." This section maps it. It does not reopen it.

- **X.1 Catchable, must re-raise.**
  - In §19 a finaliser frame `ubind (N, D)` is the only frame that reacts to the cancel. It runs `D ()` under `cfin s`, and `[cfin-ret]` re-raises the cancel unconditionally.
  - So §19 contains X.1 with the re-raise **enforced by the machine**, not by convention as in libstdc++.
  - A finaliser that raises does not swallow the cancel. `[cfin-raise]` folds the error into the cancel state.
- **X.2 Uncatchable forced unwind.**
  - No handler is named `⊥`, and the region's handlers "catch nothing", so no code can stop the cancel.
  - §19 is X.2 for handlers and X.1 for finalisers.
  - The survey's warning that X.2 silently skips `catch_unwind`-style cleanup does not apply. Cleanup is written as `[then]` finalisers, which do run, and there is no catch-all to skip.
- **X.3 Interceptable, re-linearised (OCaml).** Rejected by §19's reasoning: a region that catches its cancel "would then continue as if not cancelled". Re-linearising would need the canceller to accept further operations from a region it believes is gone.

**Cost of §19's position.** Libraries that would clean up by catching must use finalisers. Finalisers are F.1-restricted, which is the next axis.

**The error channel.** First error kept, the rest suppressed, region-internal names suppressed. This has no counterpart in any source above. Koka, OCaml and Voigt et al. do not specify an error policy for multiple finaliser failures in a discard. [unverified for Koka, whose report could not be read.]

### 5.4 Finaliser rows (OQ-7)

- **F.1 Abortive-only, plus answering calls** (as built).
  - *Buys:* no finaliser reaches a dying handler; the cancel is a pure unwind; the frame lemmas at abortive tables apply.
  - *Cost:*
    - no suspension inside cleanup, so there is no join that waits on a scheduler and no await in a finaliser;
    - scoped concurrency (survey S1) needs its join to be an answering call, a blocking capability, or outside the finaliser;
    - threads are "required eventually", so this constrains the async design (OQ-56, 60, 61).
- **F.2 Resuming finalisers to handlers outside the region.**
  - *Buys:* async cleanup.
  - *Cost:*
    - a suspension in the middle of a cancel, so κ captures the `cfin` and dying frames;
    - cancelling that κ is a nested cancel;
    - no static row tells a frame which handlers will be dying, because that depends on where the cancel originates;
    - so either dying handlers forward (dynamic), or the finaliser row is restricted by a region bound.
  - *Evidence:* none in Core. GhostEnd's `withborR_compat` lifts the unwinding borrow to resuming callback rows, but keeps the finaliser table abort-only (`hA : Ta.AbortOnly`). Voigt et al. support effects in finalisers dynamically, with only the instrumented theorem.
- **F.3 Must-not-fail finalisers.** Listed in §19 *Open*. It removes the error channel at the cost of rejecting fallible cleanup.

### 5.5 Exactly-once release of owned resources

The options collapse to 5.4: B4 (leak freedom) with B5 (release exactly once, location reuse included). Congard Thm 12 is the published analogue. The only variant is how B5 is proved:
- generic, from B4′ and the step-for-step simulation `BumpSim` (OQ-43), as stated;
- or by 8.3's cells, if that machine change is taken, which would make B5's simulation carry κ cells.

---

## 6. Where our current targets sit

| property | Lean target | menu position | status (world) |
|---|---|---|---|
| P8 | A's S6 `ContUse` | 8.5, proved through 8.2 or 8.4 (8.3 excluded by S4; AGREE Q9) | stated; open at our instance; R1–R4 lemmas not built |
| P8, resource half | B4 `Sound`, B5 `ReleasedOnceReuse` | 8.6 / 5.4 | B4 proved for today's rules (Core σ=[]); B5 from B4′ and `BumpSim` |
| P8, typing side | `[let]`, `contShare` at `unr`, `[handle]` `!` | 8.1 as rules, no lemma | in the kernel (Core σ=[]) |
| P5, cancel | A's S5 `NoIntercept` | 5.1; X.1 ∩ X.2 | open at our instance; `noInterception_tier1` proved (Core σ=[]) |
| P5, unwind | A's S5 `UnwindOrder`; Core's `FinaliserOrder` | 5.1 | open; `two_frame` proved (Core σ=[]) |
| P5, programs | E7 `CancelPolicy`, E8 `UnwindPolicy`, E9 `StoredK` | concrete runs of 5.1 | stated; acceptance programs in `Core/EffPrograms.lean` (Core σ=[]) |
| P5, world | device's `I3` = `ShareCancel` | 5.6, closing clause only | `i3_core` proved (Core σ=[]); at W open |
| P5, lends | `CancelCloses` | 5.6 | named only (OQ-57) |
| P5, global exactly once | none | 5.5 | not stated |
| finaliser rows | `[then]`'s `D : F_{Σ^abort} 1` | F.1 | as built; OQ-7 open |

**Gaps relative to the menu.**
- **No global exactly-once statement for finaliser frames** (5.5). S5 is per event.
- **The ghost route (8.4) has an unresolved step:** coupling ghost consumption to run steps. I have not derived it and have not verified that any obstruction is real.
- **E7–E9 and R1–R4 have no lemma that a typing system lacking cancel fails them** (AGREE: "linear continuations with cancel (E7–E9) and S6's witnesses R1–R4 have no lemma").
- **The choice between 8.2 and 8.4 is the builder's.** The choice to admit 8.3 at all is the user's (AGREE Q9).

---

## 7. What could not be verified

- Leijen, MSR-TR-2018-10 (Koka deep finalisation): the PDF could not be downloaded. Quoted only through Voigt et al.
- de Vilhena & Pottier, ESOP 2023 (TES): not read.
- Iris-WasmFX's one-shot mechanism (survey: "ghost token"): not read.
- without.boats' "scoped task trilemma", `async-scoped`, and `std::thread::scope`'s source: relayed from the survey.
- Rust's "drop the future = cancel" and async-drop status: relayed or context only, not quoted.
- Tov & Pucella 2011, Mostrous & Vasconcelos 2014: cited through Tang and through EGV respectively.

---

## Sources

- W. Tang, D. Hillerström, S. Lindley, J. G. Morris. *Soundly Handling Linearity.* PACMPL 8 (POPL), Art. 54, 2024. Thm 3.4, Def 3.5, Thm 3.6, §1 (Links bug), Fig. 4 (T-Seq, T-Handler). https://arxiv.org/abs/2307.09383
- O. van Rooij, R. Krebbers. *Affect: An Affine Type and Effect System.* PACMPL 9 (POPL), Art. 5, 2025. Thm 2.1, §2.4, §3.1–3.3, §5 (EWP-Handle, adequacy), §7. https://doi.org/10.1145/3704841 ; PDF: https://robbertkrebbers.nl/research/articles/affect.pdf
- P. E. de Vilhena, F. Pottier. *A Separation Logic for Effect Handlers.* PACMPL 5 (POPL), Art. 33, 2021. R6, law A1, Thm 4.1, footnote 5, §8. http://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf
- D. Voigt, P. Schuster, J. I. Brachthäuser. *Dynamic Wind for Effect Handlers.* PACMPL 9 (OOPSLA2), Art. 377, 2025. Thm 3.3–3.6, §3.4.4, §6.3. https://doi.org/10.1145/3763155 ; PDF: https://se.cs.uni-tuebingen.de/publications/voigt2025dynamic.pdf
- D. Ahman, A. Bauer. *Runners in Action.* ESOP 2020, LNCS 12075. Thm 6, Thm 7, §1, §6. https://arxiv.org/abs/1910.11629
- S. Congard, G. Munch-Maccagnoni, R. Douence. *Linear Effects, Exceptions, and Resource Safety: A Curry-Howard Correspondence for Destructors.* ESOP 2026 (https://doi.org/10.1007/978-3-032-22720-1_8). Thm 1, Prop 6, Thm 10, Thm 12, Prop 15–17, §6.1. https://arxiv.org/abs/2510.23517 (v2)
- S. Fowler, S. Lindley, J. G. Morris, S. Decova. *Exceptional Asynchronous Session Types: Session Types without Tiers.* PACMPL 3 (POPL), Art. 28, 2019. §1.4, §2.3 (E-Cancel, E-Zap, E-Raise), Thm 3.2–3.13, §5.4. https://doi.org/10.1145/3290341 ; PDF: https://eprints.gla.ac.uk/223075/
- OCaml manual, *Effect handlers* (5.3), sections on `discontinue` and on linear continuations. https://ocaml.org/manual/5.3/effects.html
- K. C. Sivaramakrishnan, S. Dolan, L. White, T. Kelly, S. Jaffer, A. Madhavapeddy. *Retrofitting Effect Handlers onto OCaml.* PLDI 2021. `discontinue`, `Gc.finalise` workaround. https://arxiv.org/abs/2104.00250
- D. Leijen. *Algebraic Effect Handlers with Resources and Deep Finalization.* MSR-TR-2018-10 [not read]. https://www.microsoft.com/en-us/research/publication/algebraic-effect-handlers-resources-deep-finalization/
- The Koka book, `finally`, `raw ctl`, `rcontext.finalize`, "Linear Effects". https://koka-lang.github.io/koka/doc/book.html
- A. A. Mathiasen, A. Timany, L. Birkedal. *Yarrow: Reconciling Effect Handlers and Region-Based Memory Management.* arXiv 2607.15876. https://arxiv.org/abs/2607.15876
- Rust RFC 1066, *Safe `mem::forget`.* https://rust-lang.github.io/rfcs/1066-safe-mem-forget.html
- Rust `std::pin`, "Drop guarantee". https://doc.rust-lang.org/std/pin/index.html
- libstdc++ manual, *Exceptions* (thread cancellation, `__forced_unwind`). https://gcc.gnu.org/onlinedocs/libstdc++/manual/using_exceptions.html

**Ours.**
- SPEC §19 *Cancels*, *Typing*, *Finalisers that perform operations* (`~/repos/borrow-core/SPEC.md`).
- `Core/EffDefs.lean` (`errOk`, `cancelTab`, `cancelOwed`, `contShare`, `opTable`).
- `Core/EffRules.lean` (`ewp_cancel_absorb`, `cancel_then`, `ewp_kappa_cancel`).
- `Core/EffCancel.lean`.
- `experiments/Targets/Targets/A/Soundness.lean` (S5, S6).
- `Targets/A/Expressiveness.lean` (E7–E9).
- `Targets/B/Guarantees.lean` (B4′, B5).
- `Targets/I/Interface.lean` (`ShareCancel`, `I3`).
- `experiments/Targets/RESTRUCTURE.md` §1.5.
- `experiments/Targets/AGREE.md` Q9.
- `docs/effects-state/05a` (OQ-7), `05b` (OQ-50, OQ-52, OQ-57).
- `research/effects/survey.md` A3, A6, A7, T4, T6, P2, P3.
- `research/effects/ante-deep-dive.md` §3(e).
