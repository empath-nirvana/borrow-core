# Prior art: I2, capture and resume preserve the invariant (tier 2)

This chapter covers the literature for one interaction property and ends in a menu of options with their trade-offs. It does not recommend one.

**The property.** [I2](../properties/i2-capture-resume.md) is a **preservation** statement. Capture freezes a computation at an operation; resume thaws it. Both preserve the global invariant (`TW`, `TW.inv`, extended to W), including the lends that span the suspension. Tier 2 is I2 at arbitrary nesting. Read through [freeze as a binder](../foundations/freeze-binder.md), I2 is equivariance: the relation and the invariant are invariant under bijections of locations and instances, and under order-respecting renamings of lifetimes. Resume and placement are instantiations. The tier question is the question of preservation at one construct.

**Decisions that bound the menu** ([decided constraints](../decisions.md)):
- nothing breaks the borrow calculus, meaning its guarantees, not BoLo's text;
- the core is linear, and discard is an explicit cancel;
- handlers are deep;
- multi-shot is ignored (decision 63), so it appears below only as context;
- no step-indexing;
- handling is erased at runtime, and the lowering is a state machine (P13);
- tier 2 is in scope (BRIEF §5).

**Verification marks.**
- **[read]**: the statement was read in the primary full text for this chapter, by me or by a retrieval pass I ran. The quote is copied from that text.
- **[relayed]**: taken from our survey, the Ante deep dive, a sibling prior-art chapter, or a secondary source. Not re-read here.
- **[unverified]**: could not be checked.

Theorem numbers are those of the version named in the sources list. Where versions number differently, both are given.

---

## 0. Menu at a glance

Two parts are independent:
- **What happens to a lend at a stop.** This is the semantic option, rows M0–M3. It is OQ-9.
- **What the typing adds and how I2 is proved.** These are side conditions and proof routes, rows T1–T4. Each composes with M1 or M2.

| # | option | I2 statement shape | buys (programs) | main cost | nearest literature | our evidence |
|---|---|---|---|---|---|---|
| **M0** | **Keep T1 + `↭`** (tier 1 only; OQ-9 (c)) | I2 at abortive rows only; `StopVisible` with nothing held | nothing new; P14 holds by construction | rejects AT02, AT04, AT12, AT17 and `genSelf`, and the async read into a local buffer | well-bracketed logics (Timany–Guéneau–Birkedal 2024; Dreyer–Neis–Birkedal 2010) | `i2_core_abortive`, `wbCore` (Core σ=[]); `Restricted/RunEnd.lean` |
| **M1** | **Ghost end: end internal lends at the stop, re-lend fresh at resume** (OQ-9 (b)) | I2 at today's stop and `↭`; resume quantified over a fresh lifetime each time (`Relend`); `held = ([],[])` | AT02, AT04, AT12 and `genSelf` (instances proved); AT17 needs placement as well (T4) | re-lendability enters the relation (the `vRL*` line, GFP refuted as stated, GFPA open); needs a handler extent (OQ-3 (a)) and D-ORD | **Yarrow's temporary revocation** (EWP-Do-Once): the captured points-to resources are surrendered at the perform and returned at the resume | GhostEnd: `withbor_spans_yields_cC`, `imm_spans_yield`, `spans_two_affine_yields`, the stacked rows (Core σ=[], GE) |
| **M2** | **Carry lends open across the stop** (OQ-9 (a)): a relativised stop and a changed `↭` | I2 with `held` ≠ ∅; `Upd` differs from Core's off the nil slice; open entries closed on every path | the same programs, with the lend's identity (its lifetime) kept across the stop | the relation must carry the σ-component of `#` (WorldW FINDING-1); exclusivity at a stop open; 6.66 unresolved; OQ-44 and OQ-57 | Rust static coroutines and `async fn` (borrows stay live; frames pinned); Hazel/Affect (the resource sits in κ's affine wand); RustBelt's lifetime tokens owned by k (survey, synthesis) | WorldW resource-level hand-on and exit (probe); `carryW` meets the run-end laws (checked); `at02_held_end` (`↭` alone excludes the cell-kept form) |
| **M3** | **Lend unfolded at the stop, refolded at the same lifetime** (OQ-9 (a), cell unfolded) | as M1 at the run end; the index records the lend; refold at the old `α` | as M2 | refold at the same lifetime refuted at Core's `Ext` (`refoldKripke_false`); `MutFrameW` unchecked | none found | `at02_unfolded_end` (checked); LoopBorrow refutations |
| **T1** | **Ante-style restrictions as a tier-2 typing** (H1/H2) | I2 with side conditions: the handler sees no place of the suspended body; a passed-up borrow ends at κ's consumption | a borrow passed **up** to the clause (H2) and lends internal to the body (H1) | three typing rules; Ante has no proof; H2 does not cover a κ that is stored | Ante tour; Swift SE-0474 and Hylo (yield once; the access ends before the resume); Yarrow's UB rule | `admClosedOp` (R-CLOSEDOP) is the current `Adm`; no H1/H2 statement |
| **T2** | **Second-class resume; a boxed κ with a lifetime bound** (OQ-28) | I2 for second-class κ by escape; for a boxed κ, `[@c]` bounds only the external lends | P9 as escape analysis; a scheduler only through a box | boxing; `U C` has no outlives rule (`thunk_not_outlives`) | System C (Try binds `k` second-class; `box` records captured capabilities) | `experiments/SecondClass`; `ewp_gen` (lift-stage1) |
| **T3** | **Freeze-as-binder equivariance as the proof route** | `FreezeBinderLoc` (a symmetry under location bijections) and `FreezeBinderLife` (forward under `Emb`); I2's resume as instantiation | one argument for placement (AT17, moving a frozen frame) and for re-lend (M1) | the lifetime half is the first equivariance under an **ordered** name symmetry that I can find stated; `mut_not_natural`; `NotVDenNaturalArises` open | nominal sets (Gabbay–Pitts Lemma 4.7, Prop 4.10); Pitts–Stark Lemma 1; Benton–Leperchey; Pitts 2016 §9 ("remains to be investigated" for ordered names) | `Targets/I/Binder.lean` (stated, open); Restrat audit (natural except `𝒱⟦T⟧`, `wp` open); GhostEnd step 4 |
| **T4** | **Immovable placement (Pin) in place of the location half** | placement fixes addresses once; no location symmetry needed after it | AT17-style storage, on condition that the frame never moves afterwards | an extra placement rule; moving after placement needs T3 anyway | Rust `Pin`, E0626, RFC 2349, `async fn` is `!Unpin`; Ante/minicoro stacks never move | none |

**Where our target sits (§6).** In done, I2 is `Arises` (option-neutral), proved at σ=[], together with `Tier2Programs`, which is open at a typing system. The device's `I2` fixes an option. It is proved at σ=[] at abortive rows, which is M0. Its resuming conjuncts (`ImmFrameW`, `MutFrameW`) are stated in the single-lifetime form, "the lend quantified at the callback's start". By reading, that form is closer to M2/M3 than to M1, whose proved lift is the `Relend` form. `FreezeBinder` (T3) sits beside done and is open.

---

## 1. Canonical statements

### 1.1 Capture lemmas: typing the frozen context

**System C: Brachthäuser, Schuster, Lee, Boruch-Gruszecki, *Effects, Capabilities, and Boxes* (OOPSLA 2022)** [read, author TR]
- **Lemma 7** in the TR, which numbers results with one global counter: "Given a well-typed effect call ∅ ⊢ H_l[ cap_l(v⃗_i) ] : τ | C ∪ {l} with effect signature l : τ⃗_i → τ_0 ∈ Ξ, it follows that y : τ_0 ⊢ H_l[ return y ] : τ | C ∪ {l}."
  - The survey and the I2 chapter cite this as "Lemma 4.6". That numbering does not appear in the TR. The ACM numbering is [unverified], because the ACM PDF could not be fetched.
- **Theorem 5 (Preservation of System C):** "If ∅ ⊢ s : τ | ∅ and s ⟼ s′ then ∅ ⊢ s′ : τ | ∅." In the (cap) case, "we finally use Lemma 7 to conclude the proof."
- **How κ is typed.** Rule Try binds the continuation second-class, `k :^C τ_0 → τ`, at the handler's own capability set. To leave, it must be boxed: "the continuation resume closes over both the capabilities used by the handled program, as well as the capabilities used by the handler itself. In this case, we have box {console, time} resume" (§3.3). On (ret): "only boxed values can leave delimiters".
- **How the frozen context is reasoned about.** Contexts have their own judgement `⊢ctx E : τ1 ⇝ τ2 | C`, and Lemma 4 is proved "by induction over the typing derivation of the context". The Coq development uses an abstract machine whose invariant is "all free labels in the captured continuation are delimited in the remaining stack". No proof of Lemma 7 is printed.
- **Regions.** §5's local backtrackable state treats a region as a tracked `Reg` capability: "references that are used in a second-class way, and therefore naturally follow a stack discipline, do not need any special precautions to prevent them from escaping." By the retrieval pass's reading, this extension is outside the stated soundness theorems.

**Tang, Hillerström, Lindley, Morris, *Soundly Handling Linearity* (POPL 2024)** [read, arXiv v2 = PACMPL text]
- **Theorem 3.4(2):** "Unlimited continuations are unlimited: if Δ; Γ ⊢ E[(do ℓ V)^E] : C for E = {ℓ : A ↠• B ; R} and ℓ ∉ bl(E), then there exists Δ ⊢ Γ = Γ1 + Γ2 such that Δ ⊢ Γ1 : • and Δ; Γ1, y : B ⊢ E[(return y)^E] : C."
- The E-Op case of subject reduction (Thm 3.3) uses the same split for every operation: the context's environment `Γ12` separates from the argument's `Γ11`, "by a straightforward induction … similar to the proof of Theorem 3.4.2".
- **Theorem 3.6 (Reduction Safety):** "if M ⇝^S_T N, then N is linear safe and ℒ(M) ∪ S = ℒ(N) ∪ T."
- **What it says about one-shot.** For a linear (`◦`) operation, the lemma puts no condition on `Γ12`: the whole linear context moves into κ. Nothing is said about borrows or lifetimes.

**Bauer & Pretnar 2014 (LMCS 10(4:9))** [read]
- **Theorem 4.1 (Progress & Preservation)** is proved in Twelf.
- No capture lemma is needed, because operations carry their continuation syntactically, as `ι#op e (y. c)`. The handler step is `with h handle (ι#op e (y. c)) ⇝ ocs_ι#op (e, (fun y ↦ with h handle c))`. Ordinary substitution suffices.

**Survey T1** [relayed] generalises the two lemmas above to loans: `∃ Λ = Λ_E ⊎ Λ_rest with loans(E) ⊆ Λ_E such that Σ;Λ_E, y:B ⊢ E[y]`. This is synthesis, not a printed result.

### 1.2 Preservation with suspended frames: the frozen context as an owned resource

**de Vilhena & Pottier, *A Separation Logic for Effect Handlers* (POPL 2021, Hazel)** [read]
- **EWP2 (Fig. 5):** "ewp E §(N)[do v] ⟨Ψ⟩{Φ} ≜ Ψ allows do v {w. ⊲ ewp E N[w] ⟨Ψ⟩{Φ}}". The frozen context `N` is a wand inside the protocol obligation.
- **Law A1:** "this law does not involve the persistence modality □ … a captured continuation can be invoked at most once … In return, we will be able to establish a standard frame rule."
- **Frame:** "any resource P that is at hand before performing an effect (and that is not consumed by the very act of performing this effect) remains available afterwards." The paper says "the frame rule does not come for free: it holds because our definition of ewp imposes an affine usage of continuations."
- **Bind** holds for neutral contexts only, meaning contexts with no handler frame.
- **Theorem 4.1:** "If ⊢ ewp e ⟨⊥⟩{Φ} holds then executing e in an empty heap is safe."
- **A borrowed collection across yields.** In the `invert` case study (§5), a fold becomes a cascade: "The ownership of the collection, represented by 𝐶, must be abandoned when the cascade is created … It is recovered once the cascade is exhausted." Footnote 5 adds: "if the user stops iterating early … she has no way of recovering the ownership of the collection. We believe that this problem could be remedied by imposing a linear usage of continuations, combined with a discontinue operation". This is the nearest published case of an **external lend spanning yields**. The collection's ownership lives inside the suspended computation for the whole iteration, and linearity with a cancel is named as the fix for early exit. Our core is linear with cancel.

**van Rooij & Krebbers, *Affect* (POPL 2025)** [read]
- **Theorem 2.1:** "Every closed well-typed program is safe w.r.t. the operational semantics." The adequacy paragraph (§5.2, unnumbered): "if True ⊢ ewp e {Φ} is derivable, then e is safe", where safety "guarantees that one-shot continuations are called at most once, no effects are left unhandled".
- **EWP-Frame** holds only under "𝜌 mono in 𝑅 := □ (∀ op 𝑣 𝛷. 𝜌 op 𝑣 𝛷 −∗ 𝑅 −∗ 𝜌 op 𝑣 (𝜆 w. 𝛷 w ∗ 𝑅))". That is, a resource can be framed across an operation only if the protocol carries it to the continuation.
- References are `Cell`-like: loads only at unrestricted types. There are no borrows.

**Mathiasen, Timany, Birkedal, *Yarrow: Reconciling Effect Handlers and Region-Based Memory Management* (arXiv 2607.15876v2)** [read: §1, §2, §4]

Yarrow is the closest published result to I2.
- **The problem:** "the non-local control flow of algebraic effects break the stack discipline of function calls and returns that region-based memory management relies on".
- **The example:** `region (let r = ref local 0 in do Foo r; !r)`. "When Foo is a one-shot effect, loading from r is safe because the region that holds r is captured as part of the continuation of Foo, and is restored when the continuation is invoked."
- **The technique:** "continuations can capture regions when performing effects, making this a point of temporary revocation for one-shot effects and permanent revocation for multi-shot effects."
- **EWP-Do-Once** (§4.2). The performer surrenders the stack points-to resources of every fiber the continuation captures. In the paper's words, this "deallocated all the references that the continuation of the effect handler captures in its regions". The resumption obligation is `Ψ v κ1 (λ w κ1′. Stack (κ1′ ++ [(op, τ)] ++ κ2) −∗ ∗_{(ℓ,v)∈m} ℓ ↦ v −∗ Φ w)`. So the points-to come back at the resume, under a stack prefix `κ1′` that the handler may have changed. EWP-Do-Many withholds them.
- **The handler side (§2):** "We deem it undefined behavior to use local references that are not part of the current stack, i.e., local references allocated in a region of a fiber that a continuation points to". One reason given is "to ensure that reclamation of memory used by fibers of continuations should not depend on anything except on how the continuation itself is used."
- **Adequacy (§4.1, unnumbered):** "if Stack([(−, [[]])]) ⊢ ewp 𝑒 𝜌 {Φ} is provable, 𝑒 can always take a step … or it reduces to a value 𝑣 for which Φ(𝑣) holds."
- **Flix:** "The combination of regions and effect handlers is undefined behavior".

**How Yarrow reads against our options** (my reading, not a claim of the paper):
- EWP-Do-Once has M1's shape. At the stop the suspended segment's local resources leave the performer's view, and at the resume they return. In between, the handler runs with `Stack κ1` and may push or pop regions (`κ1′`).
- Two differences:
  - Yarrow's resources are points-to facts at fixed locations, not lifetime-indexed borrows. So "fresh at resume" has no content there, and the same `ℓ ↦ v` returns.
  - Yarrow's regions are owned memory, not lends of an outer place. The analogue of our *Mut lend of an outer cell spanning the stop* is not in Yarrow.
- Its UB rule is A5(c) (the handler touches no suspended place), enforced semantically rather than by typing.

### 1.3 Well-bracketing: what a proof gains from it, and what it loses

**Timany, Guéneau, Birkedal, *The Logical Essence of Well-Bracketed Control Flow* (POPL 2024)** [read]
- **Definition (abstract):** "A program is said to be well-bracketed if every called function must return before its caller can resume execution."
- **The mechanism is ghost stacks:** "To make a private transition from state 𝑠 to state 𝑠′ … we allocate a fresh instance of ghost state in state 𝑠′. We then pushes the name of this newly allocated ghost state on top of the stack. In order to roll back a private transition, we simply pop the stack."
- **wbHoare-access-stack:** "the contents of the stack are expected to be returned untouched in the postcondition; this is exactly the reason why we can guarantee well-bracketedness."
- **wbwp-definition:** `wbwp e ⦇Φ⦈ ≜ ∀S. AllStacksExcept(S, O) −∗ wp e {x. ∃S′. S ⊆ S′ ∗ AllStacksExcept(S′, O) ∗ Φ(x)}`.
- **Theorem 3.1 (Adequacy)** is the only numbered theorem.
- **Which rules hold:** "all the same reasoning principles as Iris's Hoare triples except for the rule for forking of threads".
- **Handlers:** "We conjecture that such logics can serve as a basis for a well-bracketed program logic that can reason about well-bracketedness in the presence of innocuous uses of control effects." This is a conjecture; the paper does not do it.

**Dreyer, Neis, Birkedal, ICFP 2010** [read]
- On call/cc: "every time we pass control to the context may be the last! … the private and public transition relations must be collapsed into one, and consequently we must disallow inconsistent states".
- On exceptions: "raising an exception causes a 'well-bracketed' kind of control effect … the presence of exceptions does not per se restrict our STS model".
- "We leave consideration of other control effects, such as delimited continuations, to future work."

**Timany & Birkedal, ICFP 2019** [read]
- **Definition 4.1:** "clwp e Φ ≜ ∀K, Ψ. (∀v. Φ(v) −∗ wp K[v] Ψ) −∗ wp K[e] Ψ". The paper explains: "clwp e Φ holds if the bind rule holds for e, which intuitively means that e behaves context-locally."
- Stepanenko et al. (ESOP 2025) [read] reuse the device for context-dependent effects ("our extension is conservative"; Definition 2, Lemma 5 "Limited bind rule").

**One-shot continuations recover part of well-bracketing** [read, three sources]:
- Yarrow: "temporary revocation for one-shot".
- blaze (de Vilhena, van Collem, Wright, Krebbers, POPL 2026) §4.3: "taking 𝑚 = os eliminates the persistently modality, thereby allowing ephemeral resources to be used".
- Hazel's frame rule, from A1's missing □.

None of them restores full well-bracketing: control still leaves the suspended segment while its frames are alive.

**How this maps onto BoLo** (synthesis, mine):
- BoLo's frame rules already have TGB's ghost-stack shape.
  - 6.64 and 6.65 open a fresh lifetime (И, [TR] 6.108–6.112) "on top of" the record list.
  - At exit `↭` demands that the reachable borrows are "exactly the same before and after" ([CONF] 415:23, quoted in FIX-RUN-END §1).
  - That is wbHoare-access-stack's "returned untouched".
- T1 (conjunct 40) and `↭` (conjunct 37) are therefore our well-bracketing conditions at a stop. Tier 2 asks what replaces them. TGB's answer for well-bracketed code is "push fresh, pop on return", which is M1's re-lend: push fresh at every resume, pop at every stop.

### 1.4 Binders, freshness and equivariance

**Pitts & Stark, MFCS 1993 (ν-calculus)** [read]
- **The judgement:** `s ⊢ M ⇓σ (s′)C`, "in state s, expression M evaluates to canonical form C creating fresh, local names s′".
- **Lemma 1:** "If s ⊢ M ⇓σ (s1)C and s ⊢ M ⇓σ (s2)C′, then there is a bijection R : s1 ↔ s2 so that C′ is α-convertible with the expression C[n′/n | (n, n′) ∈ R]."
- **Remark 2:** "(SUBST) … is a correct derived rule provided that f is an injective function". Contraction "is not a correct derived rule".
- **The logical relation** is indexed by partial bijections. Corollary 11 is the renaming form of the fundamental property.

**Gabbay & Pitts 2002 (FAC 13)** [read]
- **Lemma 4.7 (Equivariance property of FM-set theory):** "∀a, b ∈ A ∀x⃗ (φ(x⃗) ⇔ φ((a b) · x⃗))", proved "By induction on the structure of φ".
- **Proposition 4.10 (И as a 'freshness' quantifier):** "∀a (a # x⃗ ⇒ φ) ⇒ Иa φ ⇒ ∃a (a # x⃗ ∧ φ)", with equivalence when φ's free variables are among `a, x⃗`.
- **Definition 5.4:** atom abstraction `[A]X`.

**Pitts, *Nominal Techniques* (SIGLOG News 2016)** [read], §9 on ordered names: "Linear order: identify the countably infinite set of names A with the set of rational numbers and take G to be all order-preserving permutations. … The extent to which it has forms of name abstraction like those considered in Section 5 and Section 6 … remains to be investigated." Bojańczyk–Klin–Lasota (LMCS 2014) [read] develop the support theory for the total-order symmetry: Example 2.3, and Corollary 9.5, "The total order symmetry admits least supports".

**Locations in Kripke models** [read]:
- **Pitts & Stark 1998**, footnote 4: "the termination relation ↓ is invariant under bijective renamings of location constants" ("easily verified", no proof printed).
- **Benton & Leperchey (TLCA 2005)** build equivariance into the model with FM-cpos. Allocation picks "some/any ℓ ∉ supp(…)", and "working with FM-cpos allows the use of equality of locations, rather than partial bijections". They warn: "the support is not the right notion for defining separation of relations."
- **Ahmed, Dreyer, Rossberg (POPL 2009)** never rename. Worlds are "an ordered list of islands … new islands only be added to the end of the list". The order is on islands, not on locations.

**Instances.**
- **Staton (LICS 2013)** [read]: `ν(a.x(a))` "first allocates a new instance". Law (ν/ν) is `νa.νb.x(a, b) ≡ νa.νb.x(b, a)`: the order of generation is unobservable. Theorems 14–16 are the representation results. Renaming invariance comes from functoriality over renamings.
- **Biernacki et al. (POPL 2020)** [read]: "we pick a globally fresh runtime instance and substitute it for the instance variable". Worlds are maps of instance variables, functorial along partial maps. Theorems 1, 3 and 5 are formalised in Coq.

**Frozen frames as name abstractions.** None found. The nearest is Kobayashi & Kameyama (arXiv 2609.06443) [read]. They store continuations "under a fresh label" and "fix a linear order on L_D and take the least label not in Dom(θ)" to make allocation deterministic. Their footnote 16: "V₁ is identical to V₂ modulo freshly generated labels. Rigorously proving this part requires cumbersome analysis of stores".

### 1.5 Coroutines and borrow checking across a yield

**rustc** [read]
- **E0626:** "a borrow in a movable coroutine persists across a yield point … it is not permitted to have a yield in a movable coroutine that occurs while a borrow is still in scope. To resolve this error, the coroutine may be marked static". The fix then pins it (`std::pin::pin!`).
- **The coroutine transform:** "MIR locals which are live across a suspension point are moved to the coroutine struct with references to them being updated with references to the coroutine struct."
- **`layout.rs`:** "This is correct for movable coroutines since borrows cannot live across suspension points. However for immovable coroutines we need to account for borrows, so we conservatively assume that all borrowed locals are live until we find a StorageDead statement".
- **`std::pin`:** "From the moment a value is pinned … that value must remain, valid, at that same address in memory, until its drop handler is called." The state machines of `async fn` are "A key example of such self-referential types".
- **RFC 2349 (Pin):** "generators essentially reify a stackframe into an object … it is likely for idiomatic usage of a generator to result in such a self-referential type".
- **RFC 2394:** "all async functions do not implement `Unpin` … This allows them to contain references across yield points."
- **withoutboats (2018):** "you can never have a borrow for which the lifetime includes an await" before Pin.

**Formal treatment.** Jung's "A Formal Look at Pinning" (2018, blog) [read] gives a semi-formal pinned typestate in the RustBelt style. No mechanised semantics of Pin with coroutines was found, and no soundness theorem for borrows across a yield [read: RustBelt, RefinedRust, Aeneas, a-mir-formality searched by the retrieval pass].

**Yield-once projections** [read]:
- **Swift SE-0474:** "exactly one yield on every path"; "The caller only has access to that value until it resumes the coroutine … the lifetime of the lent value is strictly shorter than that of the base value."
- **Hylo spec:** "Control comes back to the subscript once after the last use of the yielded projection at the call site".

**Ante** [read on the current tour; the deep dive is relayed]:
- "Any temporary place passed to an effect handler is assumed to be dropped when resume is called";
- "elem is given the type ref '(_, resume) I32, which is invalidated once resume is moved by being called";
- "Effect handler branches cannot Mutate any places used in the handled expression."

The deep dive's probes ([relayed]) show that lends internal to a suspended body are accepted (`p4`), and are sound only because minicoro stacks never move. A borrow of a body local passed up is rejected as an escape (`q2`). No formal model exists.

**OxCaml `yielding`** [read]: "a future axis that tracks whether a function is permitted to perform effects that will be handled in its parent stack". No published semantics.

**Kobayashi & Kameyama, APLAS 2025** [read]: "one-shot effect handlers and one-shot delimited-control operators can be macro-expressed by asymmetric coroutines, but not vice versa". The numbered results are Theorems 2–4 and 6–7 and Corollary 1. They also find that the 2020 translation (Kawahara–Kameyama, Thm 1) "fail[s] to preserve semantics". So rustc's coroutine discipline is an expressiveness-level template for one-shot handlers. It is not a soundness result.

---

## 2. How each realises and proves it

| system | where the frozen frames live in the proof | what is preserved across the stop | technique | mechanised |
|---|---|---|---|---|
| System C | a typed context `y:τ0 ⊢ H[return y]` (Lemma 7) | typing; labels delimited | syntactic preservation; context judgement | Coq (abstract machine) |
| Tang et al. | split environment `Γ12` of the context | typing; linear tags conserved (Thm 3.6) | syntactic; tagged semantics | paper |
| Bauer–Pretnar | a syntactic subterm `(y.c)` | typing | syntactic; HOAS | Twelf |
| Hazel | inside the protocol wand (EWP2) | every resource not consumed by the perform (frame) | Iris ewp; affine wand plus a physical one-shot flag | Coq/Iris |
| Affect | the continuation predicate passed to the row | safety; frame under `ρ mono in R` | semantic typing over AffectLogic | Coq/Iris |
| Yarrow | captured fibers' points-to surrendered and returned (EWP-Do-Once) | `Stack κ` shape; points-to of captured regions | Iris ewp with fiber domains in protocols | Coq/Iris |
| TGB 2024 | not applicable: well-bracketed only | ghost stacks returned untouched | ghost stacks of instance names | Coq/Iris |
| rustc | the coroutine struct (live-across-yield locals) | borrows of upvars free; self-borrows only if immovable | flow analysis plus a library invariant (Pin) | none |
| Ante | stackful coroutine (minicoro) | nothing checked for internal lends | runtime: stacks never move | none |
| **ours, M1** | `contShare`/`KapRel` share, lends ended (`freeze_at`), re-lent by `Relend` | `TW`, `↭` at today's stop; fresh lifetime per resume | Kripke relation; the printed 6.65 proof per unfolding (`ewpTS_M_frameR`) | Lean, Core σ=[] / GE |
| **ours, M2** | entries handed on in σ (WorldW `OEnt`) | relativised `↭` (`close_upd_coherent`) | resource surgery per entry; printed exits at resource level | Lean, probe |

---

## 3. Pitfalls

1. **Self-referential frames that move.**
   - rustc's answer is immovability (E0626, Pin). A borrow of a frame-local across a yield is admitted only if the frame never moves again, and the borrow checker does not re-lend.
   - Our state-machine lowering moves frames as a matter of course: they are stored in a box or on the stack at placement.
   - Freeze-as-binder's location half (T3) is the claim that a frozen frame has no addresses, so moving it is a renaming. No published work treats a frozen frame that way (§1.4, last paragraph).
   - Without T3, AT17 needs T4 (placement fixes the addresses once).
2. **The handler touches a suspended local.**
   - Yarrow makes it UB. Ante forbids `Mutate` of handled-expression places. Survey A5(c) is the same rule.
   - In M1 it is excluded structurally: the cell's owner is in κ's share and the lend has ended, so the handler holds no view.
   - In M2 the open entry sits beside κ, and the relation must stop a clause from copying a view out of κ's share. That is WorldW FINDING-1: "A clause's proof can split an `imm` copy off `κ`'s share (6.43). A frame holding that copy fails `CompatW`".
3. **Regions or lends exited out of order.**
   - Yarrow tracks this with `Stack κ` and allows the handler to change the prefix `κ1′` before resuming.
   - Our WorldW FINDING-2 holds in Lean at an unordered σ: `reentryInheritA`, `reentryFreshA`, `resumeOutOfOrder`. Resuming κ inside a lend younger than κ's inner lend is out of nesting order under both OQ-3 options.
   - D-ORD (OQ-8) is what rejects it. GhostEnd's `relend_respects_nesting` is the M1 side of the same constraint.
4. **A passed-up borrow that outlives κ's use.**
   - Ante ends it at "resume is moved", and Swift ends the access before the coroutine resumes.
   - Both lose the borrow if κ is stored. An async read into a local buffer, where the handler keeps both κ and the buffer, is therefore not covered by these designs (deep dive H2, [relayed]).
5. **Multi-shot.**
   - Yarrow's permanent revocation, the persistence modality in Affect and blaze, and survey M3 (no self-loans at all).
   - Ignored here (decision 63). Listed only because it is why the one-shot literature's frame rules hold.
6. **Naturality at a stored Mut invariant.**
   - Restrat's `mut_not_natural` refutes naturality of `𝒱⟦Mut 'a (Imm 'b 1)⟧` under a re-stratification. Whether its witness arises is unchecked (`NotVDenNaturalArises`).
   - The literature gives no help here. Every equivariance result found is for unordered names, and Pitts 2016 leaves ordered name abstraction open.
   - GhostEnd step 4 shows that freeze followed by re-lend never asks naturality at such a cell (`relent_holds`, `gap_accepted`).
7. **`↭` is not just T1.** In Core, T1 keeps Imm frames from spanning a stop, and `↭` alone keeps a Mut lend from spanning one (`at02_held_end`, checked). A design that lifts only T1 admits nothing new for Mut lends. This is our pitfall; the literature has no `↭`.

---

## 4. Borrows and lifetimes across suspension: what the literature has

- **Lifetime-indexed borrows spanning a suspension: no formal result found.**
  - rustc admits them by flow analysis plus Pin, with no soundness theorem.
  - Ante admits them by runtime construction, with no model.
  - Swift and Hylo admit only the yield-once projection, whose access ends before the resume.
- **Ownership across suspension: well covered, mechanised, all affine.** Hazel (the resource is in κ's wand), Affect, and Yarrow (points-to surrendered and returned). None of them has lifetimes, `↭`, or an exclusivity invariant over lends.
- **Regions with handlers: Yarrow, one paper (2026).** It has temporary revocation for one-shot. Its regions are owned memory at fixed locations, so there is no lend of an outer place and no fresh re-lend.
- **Well-bracketing as a proof resource: TGB 2024 and DNB 2010.** The handler extension is a conjecture.
- **Equivariance under ordered renamings: open** (Pitts 2016 §9).

**Where we are new**, as far as this reading goes:
- (i) Preservation of a lifetime-indexed exclusivity invariant (`TW.inv`) across capture and resume.
- (ii) Ghost-end, meaning re-lend at a fresh lifetime per resume, as a proved technique. Yarrow's temporary revocation is the nearest, without lifetimes.
- (iii) A freeze binder whose lifetime half is an order-respecting instantiation.
- (iv) A machine-checked answer to Ante's questions 1–3 (deep dive, "Novelty check", [relayed]).

---

## 5. The menu

### M0. Keep T1 and `↭` (tier 1 only; OQ-9 (c))
- **Statement:** the device's `I2` at `c = .abortive` (`i2_core_abortive`, proved at Core σ=[]); `StopVisible` with `held = ([],[])`; `Tier2Programs` dropped from done.
- **Cost:** none. It is today's kernel.
- **Buys:**
  - P14 by construction (`wbCore`);
  - every conjunct of B's guarantees as proved;
  - TGB's ghost-stack reading applies verbatim.
- **Programs:**
  - rejects AT02 (Yarrow's region example), AT04 (stands in for the async read into a local buffer), AT12, AT17, and `genSelf` (the generator borrowing its own state, `corpus/reject/gen-self-borrow.bc`);
  - borrow callbacks stay at `Row.Unwind` (abortive operations only).
- **Interactions:**
  - OQ-9 (c);
  - OQ-8, OQ-44 and OQ-57 do not arise;
  - P9 and P10 as proved at σ=[];
  - OQ-28 is still needed for a stored κ that holds no lend.
- **Evidence:** `Restricted/RunEnd.lean` (`at02_runEnd`, `wpGW_at02`: AT02's run cannot end at `Foo` holding the lend while `↭` is fixed).

### M1. Ghost end: end internal lends at the stop, re-lend fresh at resume (OQ-9 (b))
- **Statement:**
  - `held = ([],[])` and `Upd` is Core's `↭` at every index, so the run-end laws hold as at Core (`updRefl_of_core`, …, `updLendBack_of_core`, checked).
  - Resume is stated over a fresh lifetime per resumption: the `Relend` form, `owner ⋆ Relend ⊨ ewpTS` (`ewpTS_M_frameR`).
  - Read as a binder, that fresh lifetime is the **instantiation of a bound lifetime**. A frozen κ's type mentions only external lifetimes.
- **Cost:**
  - **Re-lendability in the relation.** A generic resumer must re-derive the borrower at `δ[x ↦ α′]`. That produced the `vRL*` families (BRIEF §8, pattern 4). GFP is refuted as stated (`not_gfp`), at a witness that does not arise. GFPA is open. `RelendOfTyped` (the general borrower) is open.
  - **A handler extent** `∀'h` in `[handle]` (`frozen_above_extent` needs the body to start in `Res_h`). That is OQ-3 (a).
  - **D-ORD** for nested lends: `relend_respects_nesting`, and `AllCross`, discharged only at constant `true`.
  - **6.150 at a resuming table** is not lifted. `ptoImm_dup` is proved.
- **Buys:**
  - AT02-shape, AT04-shape, AT12 (cancel through `withborR_compat`) and `genSelf`-shape instances;
  - nested and stacked lends (`stack3_reborrow_yield`, `stack2_imm_yield`);
  - closures and callees holding the lend (`closure_spans_yield`, `callee_spans_yields`);
  - avoids naturality at Mut cells (GhostEnd step 4);
  - the stop condition is unchanged, so no kernel definition change is needed for the stop (OQ-10 moot);
  - P14 is cheapest here, because `↭` keeps its printed meaning at every stop.
- **Does not buy alone:** AT17's move of κ, if the frozen frame holds self-references. That needs T3's location half or T4.
- **Interactions:**
  - OQ-3 (a) presupposed;
  - OQ-8: where the future-world quantifier sits; the stacked line puts it at the binder clauses (`callback_ext`);
  - OQ-44 (a): GhostEnd's `LEnt` entries;
  - OQ-57: `OpenS` carries the stack as a parameter, the `τ` index;
  - P10: exclusivity at a stop is Core's, since no lend is open;
  - P9: external lends only in κ's bound.
- **Literature:**
  - Yarrow's EWP-Do-Once is the same move for owned region memory: surrender at the stop, restore at the resume, with the handler free to change the stack prefix.
  - TGB's ghost stacks are the same move for well-bracketed code: push fresh, pop.
  - Nothing published re-lends at a *fresh lifetime*.

### M2. Carry lends open across the stop (OQ-9 (a), cell kept)
- **Statement:**
  - The stop hands on open entries (6.64 frame, 6.65 lend, 6.66 anti-frame, 6.150 record).
  - `Upd` is relativised: it takes the carried cells out at both ends, as in `carryW`, by `ResU.delDom`, which is [TR] 6.56's restriction.
  - Every path of κ (resume, cancel, drop) closes each entry by its printed exit.
  - `held` records the entries.
- **Cost:**
  - **FINDING-1:** the relation at W carries the σ-component of `#` (`CompatW`), so a clause read only through a relation must not produce a view copy.
  - **Exclusivity at a stop is open.** `not_holdsInjective` is at a non-arising resource; `HoldsChain` is unfinished.
  - **6.66:** `anti_handOn_needs_invariant` fixes the ghost shape at the stop; `OpenFrame66` is not derived.
  - **OQ-44:** a 6.65 lend leaves no `TW` record. `entryRecorded_mut` shows (37) forces an entry in what the stop hands on.
  - **OQ-57:** `τ` cannot be read off the full stack at frame-lemma level (FINDING-3).
  - **`carryW` fails printed run-end laws:** 6.50 (`not_updOutlives_carryW`) and 6.27 (`not_updLendBack_carryW`). So a world of this shape owes replacements for them, and every Core consumer of `↭` must be re-proved (FIX-RUN-END §1 table).
- **Buys:**
  - the lend keeps one lifetime across stops, so a value whose type mentions `'x` can be held across a stop without re-derivation;
  - no re-lendability in the relation;
  - matches rustc's model, where the borrow is simply live in the saved frame.
- **Interactions:**
  - D-ORD still needed (FINDING-2);
  - OQ-3 does not separate (a) from (b) in the draft;
  - P14 is harder, since `↭` no longer has its printed meaning at a stop;
  - FIX-RUN-END's pin keeps the nil slice Core's.
- **Literature:**
  - Rust static coroutines and `async fn`: live borrows in a pinned frame, unproved.
  - Hazel and Affect: the resource is in κ's affine wand, mechanised, no lifetimes.
  - RustBelt-style token ownership by k: survey A7, synthesis.

### M3. Unfold at the stop, refold at the same lifetime (OQ-9 (a), cell unfolded)
- **Statement:** as M1 at the run end (`at02_unfolded_end`, checked), with the index recording the lend and the resume refolding at the old `α`.
- **Cost:** the same-lifetime refold is refuted at Core's `Ext` and at a list that arises (`refoldKripke_false`, `refold_fails_at_consumer_frame`). Whether a world of this shape meets `MutFrameW` is not checked.
- **Buys:** M2's one-lifetime reading with Core's `↭`.
- **Literature:** none found.

### T1. Ante-style restrictions as a tier-2 typing (deep dive H1/H2)
- **Statement:** I2 with side conditions on the spanning rules (`RowSpan Adm`):
  - (i) clauses have no place parameters and cannot mutate places of the handled expression;
  - (ii) a borrow passed up as an operation argument is a lend whose extent is the clause body up to κ's consumption (resume or cancel), the well-bracketed lend of H2;
  - (iii) answers stay closed (R-CLOSEDOP).
- **Cost:**
  - three typing rules and their compatibility lemmas;
  - H2 may need only the printed frame rules plus `ewp_kappa_resume`/`ewp_kappa_cancel` (a hypothesis, unbuilt);
  - Ante supplies no proof.
- **Buys:**
  - **with M1 or M2**, a sound typing for programs Ante writes today;
  - (ii) relaxes R-CLOSEDOP for arguments: a generator lending its elements up, and Yield of `&T`;
  - the restrictions make A5(c) a typing fact instead of Yarrow's UB.
- **Does not buy:**
  - a κ stored past the clause, so it does not cover the async read into a local buffer (OQ-56's motivating program);
  - Swift and Hylo hit the same limit by design.
- **Interactions:** OQ-56 (operation admissibility), OQ-29 (answers into handler state; Ante's coarse "one borrow per handler" is H3), P10.
- **Evidence:** `admClosedOp`, `AdmExtends` (the current lower bound), Ante probes `q2`, `q2b`, `p4` ([relayed]).

### T2. Second-class resume; a boxed κ with a lifetime bound (OQ-28)
- **Statement:**
  - κ is second-class (as System C's Try) unless boxed;
  - a boxed κ carries `[@c]`, and storing it at `'r` needs `c : 'r`;
  - under M1, `c` ranges over external lends only, since internal lifetimes are bound.
- **Cost:**
  - `U C` has no outlives rule (`thunk_not_outlives`);
  - `[gen]` stopped at `lift-stage1` (T14.4's coinduction);
  - colouring risk if higher-order code cannot be polymorphic over second-class-ness (deep dive H4; Ante abandoned second-class references for this reason).
- **Buys:**
  - P9 reduces to escape analysis for second-class κ;
  - the frozen κ's bound is exactly survey A4's `Cont<'k>`.
- **Literature:** System C (Lemma 7, Theorem 5; `box`), Osvald et al. 2016 ([relayed]).
- **Evidence:** `experiments/SecondClass` (`handleAt_compatC`); `ewp_gen` (lift-stage1, Core σ=[]).

### T3. Equivariance under freeze-as-binder as the proof route
- **Statement:**
  - `FreezeBinder M a = FreezeBinderLoc ∧ FreezeBinderLife` (`Targets/I/Binder.lean`):
    - the location half is an iff under block-affine permutations of an arising configuration, at `Fam`, `held`, `Ext`, `Stop`, `Upd`, `val`, `comp` and `share`;
    - the lifetime half is forward instantiation along `Restrat.Emb` below a cut.
  - I2's resume is then "instantiate the bound lifetimes beneath the resumer's", and placement is "instantiate the locations".
- **Cost:**
  - **The location half.** The literature has the standard routes. Prove it by induction on the semantics (Pitts–Stark Lemma 1; Pitts–Stark 1998 fn. 4, "easily verified"), or build it into the model (Benton–Leperchey's FM-cpos; Staton's functor category). Our carrier is a `PMap` with no permutation action. `pmapRekey`, `cellLoc` and `resLoc` define one by stratum recursion, so this is the induction route.
  - **The lifetime half has no precedent found.** Pitts 2016: ordered name abstraction "remains to be investigated". Stark's (SWAP) and Staton's (ν/ν) make generation order *unobservable*, which a stack-ordered lifetime discipline contradicts.
  - **Restrat:** every model definition is natural except `𝒱⟦T⟧`, refuted at a stored Mut invariant, and `wp`, open.
  - **The first check,** `NotVDenNaturalArises`, is open.
- **Buys:**
  - one argument for AT17 (moving a frozen frame), for TwoRun's determinism up to renaming (the location half; compare Pitts–Stark Lemma 1), and for D-ORD (bound lifetimes instantiated beneath the resumer's);
  - composed with M1, it explains ghost-end as instantiation, and GhostEnd step 4 shows it never needs naturality at a Mut cell.
- **Interactions:** OQ-8 (`StkAct` must act on the index), OQ-44, OQ-57, P10 (`Exclusive` must be equivariant), P13 (placement in the lowering).
- **Literature:** §1.4.

### T4. Immovable placement (Pin) in place of the location half
- **Statement:** a frozen value is placed once, on the stack for a second-class κ or in a box for a boxed one, and never moved after. I2 needs no location symmetry after placement.
- **Cost:**
  - a placement rule in the typing;
  - the state-machine lowering must keep the placed frame at its address. Rust's `async fn` lowering does, by `!Unpin`; its rationale was "unacceptable to force indirection and allocation for each layer of composition";
  - moving a placed κ (a scheduler migrating a task) is rejected.
- **Buys:**
  - rustc's model: self-borrows across a yield in a placed frame;
  - avoids T3's location half.
- **Interactions:** P13 (zero-cost: Pin needs no indirection), threads (a placed κ sent to another thread stays at its address), OQ-28.
- **Literature:** E0626, `std::pin`, RFC 2349, RFC 2394, Jung 2018 (semi-formal).

### Combinations

| combination | covers | open at the end |
|---|---|---|
| M0 | tier 1 | nothing new |
| M1 + T2 | AT02, AT04, AT12, `genSelf`; stored κ by box | GFPA / `RelendOfTyped`; OQ-3 (a); D-ORD; AT17 if self-referential |
| M1 + T2 + T3 | the above plus AT17 by the location half | `FreezeBinder`; `NotVDenNaturalArises` |
| M1 + T2 + T4 | the above plus AT17 by placement | the placement rule; no migration after placement |
| M2 + T2 + T4 | rustc's model, proved | FINDING-1; exclusivity at a stop; 6.66; replacements for 6.50 and 6.27 |
| any + T1 | passed-up borrows (H2), restrictions as typing | H1/H2 statements; OQ-56 for stored κ |

---

## 6. Where our current I2 target sits

### 6.1 Position
- **Done:**
  - `Arises M` (I's `Interface`), proved at σ=[] (`arises_core`). It is option-neutral, since `held` is a field.
  - `Exclusive M`, proved at σ=[].
  - `Tier2Programs` (AT02, AT04, AT12, AT17, `genSelf`), open at a typing system. Interpreter runs are evidence only.
- **Device:**
  - `I2 = Arises ∧ StopVisible ∧ ShareResume ∧ FramesW ∧ SpanBorrows`. It is proved at σ=[] at abortive rows (`i2_core_abortive`), which is M0, and open at W.
  - `StopVisible` makes the visible frames equal at a stop, so spanning lends must go into `held` (M2) or be ended (M1).
- **Beside done:** `FreezeBinder` (T3) and `NotVDenNaturalArises`, both open.
- **The run end:**
  - `Upd` is a field, pinned to `↭` on the nil slice (FIX-RUN-END).
  - `SliceShape` admits M1 (`Upd` Core's everywhere) and M2 (`carryW`-shaped off the nil slice).
  - No OQ-9 option is chosen (FIX-RUN-END §4).
- **Typing:** `RowSpan Adm` with `AdmExtends` (at least R-CLOSEDOP). T1's restrictions are not stated.

### 6.2 Observations from reading, with no Lean checks run
1. **`MutFrameW` and `ImmFrameW` are stated in the single-lifetime form.** Their premise is `fresh (fun α => … ewpW … (box α …))`: one `α` for the callback's whole run across stops. This is GhostEnd's `O151AsStated` at W, which GhostEnd did not attempt ("§15's statement (`O151AsStated`) is not attempted", README step 3c). GhostEnd proves the `Relend` form instead.
   - So the device's `FramesW` is shaped for M2/M3, where the lend keeps its lifetime.
   - Under M1 it would be met only if the single-α form follows from the `Relend` form at W.
   - I have not checked whether it does, and I have not verified that any gap is real. If it does not, M1 needs `FramesW` restated in the `Relend` form, which would be a device change, not a change to done.
2. **No Lean statement of T1.** H1/H2 are hypotheses in the deep dive. `Adm` is the only hook, and it constrains operation types, not what a clause may touch (H1).
3. **`FreezeBinderLife` is forward-only.** This matches the literature's position: the only symmetries with an iff are bijections. An `Emb` below a cut is an order embedding, not a symmetry (Restrat §2).
4. **The binder's location half quantifies over `BlockAffine` permutations,** because arrays are contiguous. The literature's location equivariance is over all finite permutations. Ours is a restriction that the literature has no counterpart for. I have not checked whether a block-affine restriction is needed for `Fam`'s iff or only for `val`.

### 6.3 Inventory (CLAUDE.md §5)
- **Untranscribed literature results in the run-up:**
  - System C Lemma 7 has no counterpart. No typed capture lemma exists over `CDerives`, since Core types semantically.
  - Tang Thm 3.4(2)'s environment split has no counterpart, except as `contShare`'s wand.
  - Yarrow's EWP-Do-Once has no counterpart at W. GhostEnd's `freeze_at` plus `Relend` is its σ=[] analogue.
  - Pitts–Stark Lemma 1, determinism up to renaming of fresh names, matches TwoRun's `head_rename`, which does not build on main.
- **Unspent printed hypotheses** that bear on I2 ([relayed] from WorldW and GhostEnd's report lists): 6.64/6.65's И freshness (H4, 6.112) at the WorldW entries; 6.65's `P̂ ⊨ [β]P̂` at WorldW; 6.150's `RebEscrow`. GhostEnd spends all of these at its instances.
- **Unused uniqueness and functionality results:** the machine's determinism (`AStep1.deterministic`) is unused by GhostEnd and WorldW. It is what Pitts–Stark Lemma 1 corresponds to, so it is the natural input to T3's location half. `TI`'s uniqueness of open frames is unused by WorldW.
- **Printed lemmas in the run-up that are untranscribed:** 6.40 (WorldW: not needed); 6.150 at a resuming table (GhostEnd: lift not written).
- **Could not be verified:**
  - System C's ACM numbering.
  - The JFP version of Dreyer–Neis–Birkedal.
  - The Pitts 2013 book's numbering, relayed through Pitts 2016.
  - TGB's §6 trace theorem, which is stated only in Coq.

---

## Sources

Read for this chapter, from full text:
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki. *Effects, Capabilities, and Boxes.* OOPSLA 2022. TR numbering: Thm 3, Lemma 4, Thm 5, Lemma 6, **Lemma 7** (capture), §3.3, §5. https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects.pdf (ACM https://doi.org/10.1145/3527320 not read)
- Tang, Hillerström, Lindley, Morris. *Soundly Handling Linearity.* POPL 2024. Def 3.1, Thms 3.2–3.4, Def 3.5, Thm 3.6, App. A.3. https://arxiv.org/abs/2307.09383
- Bauer, Pretnar. *An effect system for algebraic effects and handlers.* LMCS 10(4:9), 2014. Thm 4.1, Cor 4.2. https://arxiv.org/abs/1306.6316
- van Rooij, Krebbers. *Affect: An Affine Type and Effect System.* POPL 2025. Thm 2.1, §3.1, §5.2 (adequacy; EWP-Frame, EWP-Handle). https://iris-project.org/pdfs/2025-popl-affect.pdf
- de Vilhena, Pottier. *A Separation Logic for Effect Handlers.* POPL 2021. Fig. 3 (A1), Fig. 5 (EWP2), Fig. 6, R6, Thm 4.1, §5 and footnote 5. https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf
- Mathiasen, Timany, Birkedal. *Yarrow: Reconciling Effect Handlers and Region-Based Memory Management.* arXiv 2607.15876v2. §1, §2, §4.1 (adequacy), §4.2 (EWP-Do-Once, EWP-Region, EWP-End), related work (Flix). https://arxiv.org/abs/2607.15876
- Xie, Brachthäuser, Hillerström, Schuster, Leijen. *Effect Handlers, Evidently.* ICFP 2020 (MSR-TR-2020-23). §2.2 scoped resumptions (dynamic `guard`). https://www.microsoft.com/en-us/research/uploads/prod/2020/07/evidently-with-proofs-5f0b7d860b387.pdf
- Timany, Guéneau, Birkedal. *The Logical Essence of Well-Bracketed Control Flow.* POPL 2024. Abstract, §1, Fig. 2, Thm 3.1, §4 (wbwp), §10. https://cs.au.dk/~timany/publications/files/2024-popl-accepted-wbcf.pdf
- Dreyer, Neis, Birkedal. *The Impact of Higher-Order State and Control Effects on Local Relational Reasoning.* ICFP 2010. §1, §5.1, §6. https://people.mpi-sws.org/~dreyer/papers/stslr/icfp.pdf
- Timany, Birkedal. *Mechanized Relational Verification of Concurrent Programs with Continuations.* ICFP 2019. §2, Def 4.1. https://cs.au.dk/~timany/publications/files/2019_ICFP_logrelcc.pdf
- Stepanenko, Nardino, Frumin, Timany, Birkedal. *Context-Dependent Effects in Guarded Interaction Trees.* ESOP 2025. Def 2, Lemma 5. https://iris-project.org/pdfs/2025-esop-gitrees.pdf
- de Vilhena, van Collem, Wright, Krebbers. *A Relational Separation Logic for Effect Handlers* (blaze). POPL 2026. §4.3, Thm 4.1. https://iris-project.org/pdfs/2026-popl-blaze.pdf
- Pitts, Stark. *Observable properties of higher order functions that dynamically create local names, or: What's new?* MFCS 1993. Lemma 1, Remark 2, Prop 8, Def 10, Cor 11. https://homepages.inf.ed.ac.uk/stark/obspho-mfcs.pdf
- Stark. *Names and Higher-Order Functions.* PhD thesis, 1994. Fig. 3.3 (DROP, SWAP). https://homepages.inf.ed.ac.uk/stark/namhof.pdf
- Gabbay, Pitts. *A New Approach to Abstract Syntax with Variable Binding.* FAC 13, 2002. Def 4.4, Lemma 4.7, Prop 4.10, Lemma 5.1, Defs 5.3–5.4. https://www.cl.cam.ac.uk/~amp12/papers/newaas/newaas-jv.pdf
- Pitts. *Nominal Techniques.* ACM SIGLOG News 3(1), 2016. Defs 2.4, 3.1, 5.1; §9. https://www.cl.cam.ac.uk/~amp12/papers/nomt/nomt.pdf
- Bojańczyk, Klin, Lasota. *Automata theory in nominal sets.* LMCS 10(3:4), 2014. Def 2.2, Ex 2.3, 2.5, Def 4.3, Cor 9.5. https://arxiv.org/abs/1402.0897
- Pitts, Stark. *Operational reasoning for functions with local state.* HOOTS, CUP 1998. Footnote 4 (p. 254), p. 252. https://www.cl.cam.ac.uk/~amp12/papers/operfl/operfl.pdf
- Benton, Leperchey. *Relational Reasoning in a Nominal Semantics for Storage.* TLCA 2005. §1, §3, Fig. 3, §4, Def 14, Thm 16. https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/bentonleperchey.pdf
- Ahmed, Dreyer, Rossberg. *State-Dependent Representation Independence.* POPL 2009. §3.2, §4, Figs 2–3. https://home.ttic.edu/~amal/papers/sdri/main.pdf
- Staton. *Instances of computational effects: an algebraic perspective.* LICS 2013. §V-B (idem-ν, ν/ν), Prop 6, Thms 10, 14–16. https://www.cs.ox.ac.uk/people/samuel.staton/papers/lics2013.pdf
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Binders by Day, Labels by Night.* POPL 2020. §4, §5 (Fig. 5), §6, Thms 1, 3, 5. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl20.pdf
- Kobayashi, Kameyama. *Expressive Power of One-Shot Control Operators and Coroutines.* APLAS 2025. Thms 2–4, 6–7, Cor 1; footnotes 9, 16 (arXiv 2609.06443). https://www.cs.tsukuba.ac.jp/~kam/papers/aplas2025.pdf
- Kawahara, Kameyama. *One-shot Algebraic Effects as Coroutines.* TFP 2020 (author draft). Thm 1. https://www.cs.tsukuba.ac.jp/~kam/papers/tfp2020-author.pdf
- rustc E0626. https://doc.rust-lang.org/error_codes/E0626.html
- `std::pin` module documentation. https://doc.rust-lang.org/std/pin/index.html
- rustc coroutine transform. https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/index.html ; `compiler/rustc_mir_transform/src/coroutine/layout.rs` (rust-lang/rust main, 2026-10-06)
- RFC 2349 (Pin). https://github.com/rust-lang/rfcs/blob/master/text/2349-pin.md ; RFC 2394 (async/await). https://github.com/rust-lang/rfcs/blob/master/text/2394-async_await.md ; RFC 2033 (no borrow discussion). https://github.com/rust-lang/rfcs/blob/master/text/2033-experimental-coroutines.md
- withoutboats. *Async/Await I: Self-Referential Structs* (2018). https://without.boats/blog/async-i-self-referential-structs/ ; *Pin* (2024). https://without.boats/blog/pin/
- Jung. *A Formal Look at Pinning* (2018). https://www.ralfj.de/blog/2018/04/05/a-formal-look-at-pinning.html
- Swift SE-0474, *Yielding accessors.* https://github.com/swiftlang/swift-evolution/blob/main/proposals/0474-yielding-accessors.md
- Hylo language tour (subscripts) and specification. https://docs.hylo-lang.org/language-tour/subscripts ; https://github.com/hylo-lang/specification/blob/main/spec.md
- OxCaml modes (Yielding). https://oxcaml.org/documentation/modes/intro/ ; janestreet/handled_effect README. https://github.com/janestreet/handled_effect
- Ante language tour, "In Traits and Effect Handlers". https://antelang.org/docs/language/

Relayed, not re-read here:
- Ante compiler behaviour and probes `p1`, `q2`, `q2b`, `q4`, `p4`, and hypotheses H1–H6: `~/repos/borrow-core/research/effects/ante-deep-dive.md`.
- Survey A1, A4, A5, A7, T1, T5, §1.7, P4, P10: `research/effects/survey.md`.
- Osvald et al. 2016 (second-class values); Pitts 2013 (*Nominal Sets*, CUP) numbering.

Unverified:
- System C's ACM numbering of the capture lemma (survey: "Lemma 4.6").
- Whether "very awkward example" appears in the JFP 2012 version of Dreyer–Neis–Birkedal.

Local sources:
- `experiments/Targets` (branch `targets`): `Targets/I/Interface.lean` (`I2`, `Arises`, `StopVisible`, `ShareResume`, `FramesW`, `SpanBorrows`, `RowSpan`, `admClosedOp`), `Targets/I/World.lean` (`SemWorld`, `wpGW`), `Targets/I/RunEnd.lean` (`at02_held_end`, `at02_unfolded_end`, `at02_imm_end`, `carryW`, `not_updOutlives_carryW`, `not_updLendBack_carryW`), `Targets/I/Binder.lean` (`FreezeBinderLoc`, `FreezeBinderLife`, `NotVDenNaturalArises`), `Targets/I/Programs.lean` (`at02`, `at04`, `at12`, `at17`, `genSelf`, `Tier2Programs`), `FIX-RUN-END.md` §0, §1, §4, `RESTRUCTURE.md` §3.2–§3.4
- `experiments/WorldW` (branch `probe-open-frames`): README, DESIGN §8 (FINDING-1/2/3), CHECKPOINT
- `experiments/GhostEnd`: README (steps 1–4, 3c, report lists)
- `experiments/Restrat`: README (§3–§5, `not_vDenNatural`)
- `docs/effects-state/BRIEF.md` §3, §4; `05a` (OQ-3, OQ-8, OQ-9, OQ-28), `05b` (OQ-44, OQ-57)
- `research/effects/src/prior-art/p8-p5-linearity-drop.md` §1.1–§1.3, §1.11
