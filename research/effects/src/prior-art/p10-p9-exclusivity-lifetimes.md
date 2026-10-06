# Prior art: P10 exclusivity across the handler and P9 lifetime soundness

This chapter surveys the literature and the known designs for two interaction side conditions, and ends in a menu of options. It does not recommend one.

- **P10, exclusivity across the handler boundary.** Every reachable configuration satisfies the aliasing invariant. The count includes the loans held by:
  - suspended frames;
  - running handler clauses;
  - values in transit, meaning operation arguments and resume values.
- **P9, lifetime soundness for continuations and capabilities.**
  - No capability is used outside its handler's extent.
  - No continuation is resumed after a lifetime it borrows from has ended.

**Framing** ([interaction](../interaction.md)). Both are side conditions of the interface between System A (effects) and System B (BoLo). They are read in good faith, as the literature's theorems are.

**Decisions that bound the menu** ([decided constraints](../decisions.md)):
- the core is linear;
- multi-shot is ignored (decision 63), and appears below only where a source needs it for context;
- handlers are deep;
- handler state is passed to each clause and at each resume (decision 59);
- nothing breaks the borrow calculus.

Decision 62's row variables are an implementation choice, not a goal. So "rows versus capabilities" stays an axis here (§5.4).

**A reading that runs through the chapter.** In BoLo a borrow is a lifetime-polymorphic value. A second-class value is the special case of a borrow whose lifetime is pinned to the frame. Ante dropped second-class references because they coloured `map`. That objection may not carry over, because the second-class discipline here is a type, `∀'a. Mut 'a T ⊸ …`, and not a binder mode (§1.1, §5.2 L.1).

**Verification marks.**
- **[read]**: quoted from the primary PDF or page, fetched and read for this chapter.
- **[relayed]**: taken from our survey, our Ante deep dive (`~/repos/borrow-core/research/effects/ante-deep-dive.md`, which read Ante's primary sources and compiler at `3e680ef3`), or a secondary source. Not re-read here.
- **[unverified]**: could not be checked.

Theorem numbers are those printed in the version read. Where that version is a TR, it is named.

---

## Menu at a glance

The options fall along two families, and within each family the axes are independent:
- **X.x**: how exclusivity across the handler is realised and stated (P10);
- **L.x**: how lifetimes of continuations and capabilities are bounded (P9).

"Ours today" marks where `experiments/Targets` and Core sit (§6).

| # | option | statement shape | what it buys | main cost | literature | ours today |
|---|---|---|---|---|---|---|
| X.1 | Reborrow encoding, answering handlers | `handle` = `withbor`, the capability is `Mut 'h S`, an operation is `withswap`; P10 is B6 on the image | two `&mut` from one handler rejected by `Mut` having no copy; effect safety = no use after a lifetime | answering (tail-resumptive) clauses only | Ξ/System C as source; survey A5 synthesis; Ante 2024 rule (b) | **PROVED at PAPER** (`translate_typed`, `effect_safety`); `I4a` PROVED AT A RESTRICTION (tier 1, abortive rows) |
| X.2 | Reborrow encoding, control handlers | clause receives the handler state as a 6.66 unfolding; `resume` hands it back; κ holds the rest | survey A5 rules (a)–(b) for resuming clauses; scheduler state with no second mechanism | 6.66 at W at resuming tables; decision 59's state passing must be the 6.66 round trip | Swift `yielding mutate`, Hylo `inout` subscripts (one yield); Hazel law A1 | **`AntiFrameW`** (I5.hiding) stated in the device; OPEN at W |
| X.3 | Count suspended loans in the world | `TI` over visible ∪ held frames, `Valid` over the whole configuration | AT02/AT04 as stated; no re-lend at resume | `held` sees only 6.64 frames; a 6.65 lend open across a stop needs `Upd` and the index (OQ-9 (a), OQ-44) | Yarrow's `Stack κ` and fiber domains; RustBelt tokens owned by κ (synthesis) | **P10 `Exclusive`** stated with `held`; PROVED AT σ=[] (`exclusive_core`, nothing held) |
| X.4 | Ghost-end: nothing held | lends end at the stop, re-lent fresh at resume; P10 is `TW` at each stop | P10 reduces to today's invariant | re-lendability; naturality (`mut_not_natural`, arising unchecked) | none found in this shape; Yarrow's temporary revocation is nearest | instances PROVED at Core σ=[] (GhostEnd); general OPEN |
| X.5 | Borrow passed up, ends at `resume` | an operation's argument may be a lend; its extent is the clause up to κ's consumption | async-style "lend a buffer to the handler" without lifting T1 in general (H2) | lost when κ is stored (Ante's rule invalidates it on move) | Ante `ref '(_, resume)`; Hazel protocol `{P}`/`{Q}`; Hylo/Swift yield-once (dual) | not admitted (`admClosedOp`, R-CLOSEDOP) |
| X.6 | Clause cannot touch the body's places | clauses are persistent code; body places are invisible to them | survey A5 rule (c); AT06's rejection | clauses capture no linear state; state goes through decision 59 | Ante tour; Yarrow (UB, revocation); Koka/Effekt locals | **enforced** by `[handle]`'s `!U` clauses; `Rejects` names AT06 |
| X.7 | Dynamic enforcement | runtime flag per access | accepts more | not a static guarantee; panics | Swift class properties (SE-0176); `RefCell` (clippy lint) | out of scope (assurance goal) |
| L.1 | Second-class `resume` and capabilities as frame-pinned borrows | κ and capabilities are values at a lifetime the frame instantiates; escape is 6.60 plus `[]I`'s premise | P9 reduces to escape analysis; stack-allocated κ | storing κ needs L.2 or L.3; Ante's colouring objection to check (H4) | Ξ Thm 4.3–4.4; Osvald Cor 3.6; OxCaml `local`/`unique` | capabilities: `capability_not_outlives` (PAPER); κ has no outlives rule, so it cannot be boxed |
| L.2 | Boxed continuation `[@c] U(Aff^c A B)` (OQ-28 (a)) | a `[gen]` rule; the box records the lifetimes κ borrows | schedulers, generators stored in data | a new rule and T14.4's coinduction | System C box (Example 10, Cor 9) | ATTEMPTED (`lift-stage1`), stopped |
| L.3 | Outlives rule at `U C` (OQ-28 (b)) | `Δ ⊢ U C ⊐ @a` from what C captures; `[gen]` derived | one rule serves closures and κ | 6.60's induction at `U`; T2 (#173) | CC<:□ capture prediction (Lemma 4.11); Capless (Lean 4) | `OutJ.core` has no `U C` rule |
| L.4 | A handler site opens a lifetime (OQ-3) | (a) every site, (b) a named restriction, (c) answering sites only | (a) gives GhostEnd's handler extent and K-BORANS (OQ-29) | (a) changes `[handle]`'s compatibility lemma | Müller Thm 3.6 (region per handler); Biernacki 2020 binder; Xie 2022 rank-2 η; Capless `boundary` | `effHandle` opens none; `handle_is_shift` (PAPER) for answering |
| L.5 | Resumption under a different handler | resume only beneath the capture's lifetimes (D-ORD) | rules out resuming inside a younger lend | needs L.4 (a) and the lend stack's order | Xie 2020 scoped resumptions (dynamic guard); Müller (relaxed via subregions) | OPEN; `AllCross` discharged only at constant `true` |
| L.6 | Lifetime-polymorphic operations at a borrow callback (OQ-56) | (a) R-CLOSEDOP, (b) `∀`-operations instantiated at the lend and masked at its end, (c) only outer lifetimes | (b) admits the async read into a local buffer | (b) is a new construct; masking needs the Yoshioka conditions | Ante `Mutate 'p`; Xie 2022 `vec^η`; Lucassen–Gifford masking [relayed] | **done fixed at `admClosedOp`** |
| L.7 | Lifetime tokens owned by κ (semantic) | κ's share holds the token fractions the suspended frames hold; resume returns them | the semantic counterpart of L.1/X.3 | no mechanised precedent | RustBelt lifetime logic (LftL-bor-acc) | not used; `Life = ℕᵒᵈ` strata in place of tokens |

---

## 1. Canonical statements and designs, and how each is realised and proved

### 1.1 Ante (design; compiler at `3e680ef3`) [relayed: ante-deep-dive]

Ante is the one active language that puts Rust-style borrowing beside algebraic effects. It has no formal model and no proofs. The deep dive separates **designed** (tour, blog) from **implemented** (compiler, probes).

**(a) Borrows passed up through an operation.**
- 2024 post, designed: "we need to tie `y` to the variable that owns it - which is `resume`. This way we can still yield owned references if needed, but we cannot call `resume` until they are dropped."
- Tour, designed: "Any temporary place passed to an effect handler is assumed to be dropped when resume is called … `elem` is given the type `ref '(_, resume) I32`, which is invalidated once resume is moved by being called."
- Implemented: neither. A borrow of a handled-expression local passed up is rejected as an escape (probe `q2`: "This reference to x outlives its scope"). A borrow of a place declared outside the `handle` passes (`q2b`). This is close to our R-CLOSEDOP.

**(b) Two `&mut` from one handler.**
- 2024 post, designed: "each function using the same `Read (&own mut Box String)` effect is considered to borrow from the same effect handler. Attempting to retrieve two owned, mutable references from the same handler then would be a lifetime error."
- Implemented: not enforced. Probe `q4` performs `get ()` twice at `Get (uniq 'y I32)`, writes through both, and passes.

**(c) The handler cannot mutate the handled expression's places.**
- Tour: "For simplicity, effect handlers and traits do not have place parameters". Consequences: "Effect handler branches cannot `Mutate` any places used in the handled expression"; branches "are thus treated as loop bodies".
- The tour's `bad1` example relies on a `Mutate 'v` effect that invalidates a handler-held reference "even before resume is called". `Mutate` is not implemented.

**`Mutate 'p`.** "When a reference `mut 'e t` is mutated, the compiler issues a `Mutate 'e` effect … The `Mutate 'p` effect cannot be manually handled by users but will be automatically handled once the function signature it is propagated to no longer references `'p`." This is a place-indexed effect, discharged when the place leaves the signature: region-effect masking. It exists because Ante's `mut` aliases. BoLo's exclusive `Mut` makes the callback case it guards impossible to write. Its value for us is as a model of an operation whose label mentions a lifetime (L.6 (b)), not as a mechanism we need.

**Lends internal to a suspension.** Probe `p4` (`r = ref x; emit 1; emit 2; _ = r`) passes. It is sound at run time only because Ante's general lowering uses stackful coroutines whose stacks never move.

**Second-class references dropped over colouring.** From the ideas page: "dividing the language into two colors: second-class and non-second-class. Second-class references not being a type for example means you'd need another separate map function which takes its argument by reference instead of by value."
- The objection is to second-class-ness **not being a type**.
- In BoLo, a frame-pinned borrow is the type `∀'a ⊏ ⊓Δ. Mut 'a T ⊸ ['a] U` (the withbor rows 6.172–6.174), instantiated at the frame's lifetime.
- So a `map` over a borrowed callback is one definition, polymorphic in `'a`. Whether this avoids the second `map` is the deep dive's H4. It is a hypothesis, untested here.

**Documented versus enforced.** The one-shot `resume` (`p1`, `q5`), rule (b) (`q4`) and `Mutate` are documented and not enforced. So no type-level argument covers Ante's effect–borrow interaction today. The deep dive's novelty check, which this chapter's reading does not change: a machine-checked answer to "does a passed-up borrow end at `resume`?", "is 'the handler may not touch the body's places' enough?" and "is one exclusive borrow per handler sound?" over a lifetime calculus would be new.

### 1.2 Hylo subscripts and Swift yielding accessors (implementations; static) [read]

**Hylo.** Language tour, *Subscripts*: "a subscript must have exactly one `yield` statement on every possible execution path."

Specification (`spec.md`):
- *Subscript implementations* ¶6, typo as printed: "A `let` subscript implementation or an `inout` subscript implementation must have exactly one a yield statement on every terminating execution path."
- *Yield statements* ¶1: "Yield statements project an object out of a subscript, suspending the execution path and temporarily transferring control to the subscript's caller. Control comes back to the subscript once after the last use of the yielded projection at the call site, resuming execution at the statement that directly follows the yield statement."
- *Projections* ¶8: "If a projection `p` projects an object `o` immutably, `o` is immutable for the duration of `p`'s lifetime. If a projection `p` projects an object `o` mutably, `o` is inaccessible for the duration of `p`'s lifetime."

The only formal result is Swiftlet (Racordon et al., JOT 2022). Its Theorem 4.1 (type soundness) and Def 4.1 (disjoint access paths) cover `inout` parameters, with no subscripts and no `yield`. No proved calculus for yield-once projections was found.

**Swift SE-0474** (accepted):
- *Detailed design*: "The `UniqueBorrow.property { yielding borrow }` accessor is a 'yield-once coroutine'. When called, it borrows `self`, and then runs until reaching a `yield`, at which point it suspends, lending the yielded value back to the caller."
- *Taking advantage of exclusive access*: "the `yielding mutate` accessor has exclusive access to `self`, and that exclusive access extends for the duration of the accessor's execution, including its suspension after `yield`-ing."
- *The "yield once" rule*: "there must not be a path through the yield-once coroutine's body with either zero or more than one yield."
- *Throwing callers*: on a throw in the caller, "The body of `Array.first { yielding mutate }` is resumed … Then the code after the `yield` executes." The caller "must put the yielded mutable value back into a consistent state".

**SE-0176** states the Law of Exclusivity: "two accesses to the same variable are not allowed to overlap unless both accesses are reads." It is enforced statically for locals, `inout` parameters and struct properties, and dynamically for class properties and globals.

**SE-0306** (actors) forbids passing actor state `inout` to an `async` function. The rationale: a modification "initiated by passing it as `inout` to a call that is then suspended" can be interleaved by another task on the same actor. It adds: "the `inout` restriction is not required for memory safety (because errors will be detected at runtime)".

**For us.** A yield-once projection is a lend across exactly one suspension, where the suspended party is the **lender**. That is the dual of a body that holds a lend across a `perform`. Swift's actor rule is the same boundary seen from the other side: a mutable borrow across a suspension that hands control to arbitrary code is rejected. Swift justifies the rejection by determinism, not by safety, because a dynamic check backs it up.

### 1.3 Rust coroutines, async and lending iterators (static) [read]

- **E0626**: "a borrow in a movable coroutine persists across a yield point … it is not permitted to have a yield in a movable coroutine that occurs while a borrow is still in scope. To resolve this error, the coroutine may be marked `static`". A static coroutine is pinned.
- **RFC 2394**: async functions are `!Unpin` "because the future could have internal references which means it needs to never be moved". "All of the input lifetimes to this function are captured in the future."
- **Clippy `await_holding_refcell_ref`**: "`RefCell` refs only check for exclusive mutable access at runtime. Holding a `RefCell` ref across an await suspension point risks panics".
- **RFC 1598 (GATs), motivation**: a `StreamingIterator` "yields values which have a lifetime tied to the lifetime of the reference passed to `next`". With `Iterator`, "each slice would be required to exist for as long as the iterator, rather than for as long as the borrow initiated by `next`".

**For us.** The lending iterator is the static form of Ante's rule (b): each `&mut` handed out ends before the next request to the same source. `Pin` is the runtime face of our freeze binder: a frozen frame that lends to itself must not change address, or must be renamed consistently ([freeze as a binder](../foundations/freeze-binder.md)).

### 1.4 Hazel: de Vilhena & Pottier, *A Separation Logic for Effect Handlers* (POPL 2021) [read]

**Protocols** (§3.1.1): `! x⃗ (v) {P}. ? y⃗ (w) {Q}`. "The ownership of the resources governed by 𝑃 is then transferred from Player to Opponent. Symmetrically, when replying … The ownership of the resources governed by 𝑄 is transferred from Opponent to Player." The paper adds: "this is very much like a polymorphic specification for a function."

**Law A1** (Fig. 3): "! x⃗(v){P}. ? y⃗(w){Q} allows do v′ {Φ} ⊣⊢ ∃x⃗. v′ = v ∗ P ∗ ∀y⃗. Q −∗ Φ(w)".
- The wand is not persistent, so "a captured continuation can be invoked at most once."
- In return, "we will be able to establish a standard frame rule". The authors also note: "If a persistence modality was inserted … then this frame rule would not hold."

**The handler** (§4.2.2) assumes "Ψ allows do 𝑣 {𝑤. ewp E (𝑘 𝑤) ⟨Ψ⟩{Φ}}". It receives `P` and can resume only by supplying `Q`.

**Frame across a perform** (§4.2.4): "any resource 𝑃 that is at hand before performing an effect (and that is not consumed by the very act of performing this effect) remains available afterwards."

**Theorem 4.1** (adequacy): "If ⊢ ewp 𝑒 ⟨⊥⟩{Φ} holds then executing 𝑒 in an empty heap is safe." Mechanised in Iris/Coq.

**For P10.** Exclusivity across the handler is ownership transfer. What the body does not put into `P` is framed, and the handler cannot reach it. Hazel has no lifetimes: a borrow passed through `P` is a full transfer, so "the borrow comes back at `resume`" is `Q` returning it. That is X.5 in program-logic form.

### 1.5 TES: de Vilhena & Pottier, *A Type System for Effect Handlers and Dynamic Labels* (ESOP 2023) [read]

- Theorems 1–3: soundness of TesLogic, the fundamental theorem, and soundness of Tes. Mechanised in Coq/Iris.
- Its aliasing discipline is about **effect labels**, not heap cells: "whenever a question about aliasing arises, require absence of aliasing … we interpret a row … also as a requirement that these names be pairwise distinct."
- Semantic types are persistent, and continuations multi-shot: "Ensuring that every continuation is invoked at most once would require an affine type system and is beyond the scope of this paper."
- The semantic clause for `τ ref` is omitted from the paper [unverified].

**For P10.** TES says nothing about exclusive heap ownership across a handler. Our survey groups "Hazel and TES" under A5; only Hazel bears on it.

### 1.6 Yarrow: Mathiasen, Timany & Birkedal (arXiv 2607.15876v2) [read]

This is the closest source to P10's stack-allocated case.

- **§1**: "continuations can capture regions when performing effects, making this a point of temporary revocation for one-shot effects and permanent revocation for multi-shot effects."
- **§3.1**: "We deem it undefined behavior to use local references that are not part of the current stack, i.e., local references allocated in a region of a fiber that a continuation points to".
- **§4.1**: resources include stack points-to `ℓ ↦ v` and `Stack κ`. Protocols are indexed by fiber domains: "Ψ ∈ Protocol ≜ Val → FiberDomains → (Val → FiberDomains → iProp) → iProp".
- **EWP-Do-Once** (Fig. 6–9): the performer gives up `∗(ℓ,v)∈m ℓ ↦ v` for the captured fibers, and gets them back in the resumption obligation. **EWP-Do-Many**: "we can not assume stack points-to resources for the references in the regions of the fibers that the continuation capture."
- **Adequacy** (§4.1, unnumbered): from `Stack([(−,[[]])]) ⊢ ewp e ρ {Φ}`, "e can always take a step … or it reduces to a value v for which Φ(v) holds."
- **§8**: "The combination of regions and effect handlers is undefined behavior" in Flix (personal communication). "Another direction of future work, is to build a type system for Yarrow using semantic typing."
- Mechanised in Iris on Rocq.

**For P10.** Yarrow's one-shot revocation is X.3 at the level of a logic. The suspended fibers' points-to facts are owned by the continuation, counted in `Stack κ`, and returned at resume. The handler cannot touch them, because using them is UB. Yarrow has regions, not `&`/`&mut`, and no type system yet.

### 1.7 System Ξ: Brachthäuser, Schuster & Ostermann, *Effects as Capabilities* (OOPSLA 2020) [read]

**Second-class blocks.** "blocks are considered second-class [Osvald et al. 2016] and can neither be returned nor stored in data structures." Operations "only take expressions as arguments and never blocks. Otherwise blocks could escape their scope through the effect operation".

**`resume` is a second-class block** typed `(τ0) → τ / ∅`: "Typing the continuation with the empty set of effects is safe since it is a block and cannot leave the scope of its definition." Storing it: "in Effekt continuations are blocks and can neither be returned, nor stored in data structures. In our implementation of Effekt we resort to locally unsafe primitives".

**Theorems.**
- Def 4.2 (undelimited label).
- Thm 4.3 (progress) and Thm 4.4 (preservation): "from progress and preservation follows effect safety: programs are never stuck on an undelimited label."
- Thm 5.1: the translation preserves typing.
- Mechanised **in Idris**.

**Aliasing.** None. Capabilities and `resume` may be duplicated freely within scope.

**Ours.** `experiments/HandlersAsBorrows` embeds a Ξ fragment with answering handlers into BoLo + `!`. In that embedding:
- `handle` becomes `withbor` and the capability becomes `Mut 'x S`;
- Ξ's effect safety becomes BoLo's fundamental property (`effect_safety`);
- Ξ's second-class restriction becomes the outlives check (`capability_not_outlives`, `escape_refused`).

The embedding is stricter than Ξ on aliasing: `twoBlocks_refused`.

### 1.8 System C: Brachthäuser, Schuster, Lee & Boruch-Gruszecki, *Effects, Capabilities, and Boxes* (OOPSLA 2022; TR numbering) [read]

**Theorems.**
- Thm 3 (progress) and Thm 5 (preservation).
- Lemma 4: labels are delimited.
- Lemma 7, continuation capture: "Given a well-typed effect call ∅ ⊢ H_l[cap_l(v⃗ᵢ)] : τ | C ∪ {l} … y : τ0 ⊢ H_l[return y] : τ | C ∪ {l}."
- Def 8 (undelimited label).
- Cor 9: "reducing a well-typed program ∅ ⊢ s : τ | ∅ never results in an undelimited label."
- Mechanised in Coq (zenodo 5833713).

**[Try].** The handled body sees `f :* σ` (tracked). The clause sees `k :^C τ0 → τ`, a second-class block with a **transparent** binding at the handler's own restriction `C`.

**Box.**
- [BoxIntro]: `Γ ⊢ b : σ | C ⟹ Γ ⊢ box b : σ at C`.
- [BoxElim]: "We only allow unboxing when all the capabilities mentioned in the box's type are in scope."

**Storing a continuation** (Example 10): "In order to be able to store a second-class continuation in a Queue, we need to explicitly box it. Boxing reifies the capability set of the continuation into the type, which is () ⇒ Unit at {p, schedule}." What `resume` captures: "the continuation resume closes over both the capabilities used by the handled program, as well as the capabilities used by the handler itself".

**Regions** (§5.2): "every block definitions and effect handlers implicitly creates a new region"; second-class references "naturally follow a stack discipline".

**Aliasing.** None. Capability sets are plain sets.

**For P9.** System C is L.1 plus L.2. In BoLo terms a capture set `C` maps to `⊓{lifetime(f) | f ∈ C}`. That map is monotone and forgets which capabilities were captured (HandlersAsBorrows README §5, precondition 3; no Lean). So a `[@c]` bound on κ (OQ-28) is System C's `at C`, read through outlives. HandlersAsBorrows (c) separates BoLo + `!` from Ξ, not from System C.

### 1.9 Osvald, Essertel, Wu, González Alayón & Rompf, *Gentrification Gone too Far?* (OOPSLA 2016) [read]

**Definition.** "Second-class values cannot be stored in mutable variables, they cannot be returned from functions, and they cannot be accessed by first-class (named or anonymous) functions through free variables."

**Theorems** (λ1/2):
- Thm 3.2: "Evaluation never leaks stack references".
- Cor 3.4: "The lifetimes of second-class bindings in λ1/2 follow a stack discipline."
- Thm 3.5: soundness.
- Cor 3.6: "All well-typed programs are guaranteed to respect stack-based lifetimes for second-class values."
- Mechanised in Coq.

**Effects** appear as second-class capabilities (CanThrow, CanIO), and the paper calls them co-effects. There are no continuations.

**On borrowing.** "The restrictions imposed on second-class values in our system are similar to those on borrowed references [19, 33] in ownership type systems, e.g., as implemented in Rust … orthogonal to the goals of ownership types (controlling aliasing, ensuring uniqueness, preventing race conditions, etc)."

**For us.** Osvald says outright that second-class values are lifetime-only borrows. BoLo has both halves: lifetime (6.60) and aliasing (6.64–6.66). This is the literature's support for this chapter's opening reading.

### 1.10 Capture checking and separation: CC<:□, Capless, Capybara, reachability types [read]

**CC<:□** (Odersky, Boruch-Gruszecki, Lee, Brachthäuser & Lhoták, arXiv 2207.03402, *Scoped Capabilities for Polymorphic Effects*; TOPLAS 2023 *Capturing Types*):
- Lemma 4.11 (capture prediction for answers): "If Γ ⊢ σ[a] : S ∧ C, then Γ ⊢ cv(σ[a]) <: C."
- Theorem 4.14 (used capability prediction).
- (box)/(unbox): "while one can create a boxed type with {∗} as its capture set through subsumption, one cannot unbox values of this type. This property is fundamental for ensuring scoping of capabilities."
- TOPLAS §7 adds scoped `boundary`/break, with Thms 7.1–7.2 over "proper programs": "Typing ensures that after a boundary is left, its capability is never invoked; otherwise, we could get stuck terms."
- Fourment & Xu 2023 mechanise progress, preservation and capture prediction for the base calculus in Coq (EPFL TR, `github.com/felko/ccsubbox`). Nothing claims §7 is mechanised.
- The earlier CF<: (arXiv 2105.11896) has a deep-handler rule whose continuation is typed `k : C_k B → R`, with `C_k = (fv(t) \ {x}) ∪ (fv(s) \ {y,k})`. Its soundness argument for the extension is prose.

**System Capless** (Xu, Bračevac, Pham & Odersky, OOPSLA 2025, arXiv 2509.07609): "We have fully mechanized the formal metatheory of System Capless in Lean, including proofs of type soundness and scope safety."
- Rule (boundary) requires "the result type S to be well-formed in the outer context Γ, which suffices to enforce scoping".
- §5.2.3: "a scope extrusion will lead to a stuck evaluation. The proof is fully mechanized in Lean 4."
- Its scoped capability is a one-shot `boundary`/`Break`, not a resumable continuation.
- §9 lists "aliasing, separation, and capability exclusivity" as future work.

**System Capybara** (Xu, Bračevac, Pham, Zhao & Odersky, arXiv 2607.09383):
- Thm 5.5 (separation): "If Γ ⊢ C1 ⊲⊳ C2, then in every world realizing Γ the two footprints are non-interfering". Semantic soundness in Lean 4.
- On borrows: "Rust enforces shared-xor-mutable throughout each borrow's lifetime; Capybara tracks aliases and demands exclusivity only at a consume or a separation check."
- No scope-safety theorem.

**Reachability types:**
- Wei et al. POPL 2024: Cor 4.8 (preservation of separation), in Coq.
- Deng et al. (arXiv 2510.08939), *Capture Now, Consume Later*: use and kill effects, all key results in Rocq. Its one-shot continuation (§6.2) wraps an existing continuation with a kill effect: "the right to invoke the continuation is moved into the one-shot wrapper and consumed on use". It also says: "a move is a borrow whose block is the entire continuation of the move point".

**Scala docs** (*scoped-capabilities*): "Capture set ≈ Lifetime bound: A capture set {x, y} bounds the lifetime of a value to be no longer than the shortest-lived capability it contains … Level containment ≈ Outlives".

**For P9.** "Avoidance plus well-formedness in the outer context" is our `[]I` premise plus 6.60. Capture prediction (Lemma 4.11) is the shape of a 6.60 extended to `U C` (L.3). Capless is the only mechanised scope-safety result, and it covers a one-shot escape, not a resumption. **For P10**, no capture-checking calculus has lifetime-indexed shared/mutable borrows with reborrowing.

### 1.11 Xie et al.: scoped resumptions (ICFP 2020) and named handlers (OOPSLA 2022) [read; 2022 from MSR-TR-2021-10 v1]

**Scoped resumptions** (*Effect Handlers, Evidently*, §2.2): "a resumption can only be applied under the same handler context as it was captured." The definition is "minimal in the sense that it is the minimal requirement needed in the proofs to maintain coherence of evidence translation."
- It is checked **dynamically**: "we guarantee scoped resumptions using a dynamic runtime check in evidence translated programs (called guard), but it is also possible to check it statically."
- A suggested static design: resume "fully applied within the operation clause and no occurrences under a lambda".
- Theorems 2–8 cover progress and preservation of Fε, soundness and coherence of the evidence translation, and uniqueness of handlers. They are paper proofs.

**Named handlers** (TR v1): rule `handler` "concludes with a rank-2 type … With η ∉ ftv(ε, σ), it is guaranteed that η cannot escape through the return type and effect."
- Example: `withvec : ∀α μ. (∀η. () → ⟨vec^η | μ⟩ α) → μ α`.
- On why: "it is essential to attach a scoped type parameter η to not only the associated index (ix η) but also the effects (vec^η)".
- Scope safety "is subsumed by the type soundness theorem" (Thms 3.1, 3.3).
- The OOPSLA 2022 camera-ready was not reachable, so its numbering is [unverified].

**For us.**
- Scoped resumption is L.5: a continuation's "lifetime" is the handler context of its capture.
- `vec^η`, an effect label indexed by a rank-2 scope variable, is a typed precedent for L.6 (b): operation labels that mention a lifetime, kept from escaping by the binder.

### 1.12 Biernacki, Piróg, Polesiuk & Sieczkowski, *Binders by Day, Labels by Night* (POPL 2020) [read]

- "in the expression handle_a e {h; r}, the instance variable a is bound in e".
- On why escape is subtle: "the use of resumptions is crucial here: mere exceptions, which may not use the resumption, would never lead to such a problem."
- Thm 1 (fundamental) and Thm 2 (type soundness), proved with a Kripke-style step-indexed biorthogonal logical relation. Mechanised in Coq.

**For P9.** A handler site that binds a type-level name is L.4 (a). The source's warning applies to us: resumptions, not aborts, are what make escape non-trivial. That matches our state, where abortive rows are proved and resuming rows are open.

### 1.13 Müller, Schuster, Starup, Ostermann & Brachthäuser, *From Capabilities to Regions* (OOPSLA 2023) [read]

- "a region denotes the scope of an effect handler and subregion evidence is used to constructively witness how handlers are nested."
- Evidence "is either an evidence variable, the trivial evidence 0, or the composition e ⊕ e". So `0` is reflexivity and `⊕` is transitivity.
- Lemma 3.5 (sound environments).
- Thm 3.6 (typability preservation).
- Thm 3.7 (evaluation: `n + 2k` steps).
- The guiding principle: "each call-site region of a block is a subregion of its definition-site region. This is facilitated by the second-class property of blocks".
- The continuation: "the continuation has capability type, not function type. This allows to call the continuation not only in region ρ but also in any subregion of ρ … we lift the restriction of scoped continuations".
- Paper proofs; the extended TR was not fetched.

**For P9.** This is formal evidence that a handler's scope is a lifetime, and that second-class-ness is what makes "call site ⊑ definition site" hold. Our outlives order (`Life = ℕᵒᵈ`, 6.60) plays the role of the subregion evidence. It also shows L.5's restriction can be relaxed to "any subregion of the capture's region".

### 1.14 RustBelt and the lifetime logic [read]

Jung's thesis, Fig. 11.1:
- LftL-begin `True ≡−∗ ∃κ. [κ]₁ ∗ ([κ]₁ ≡−▷∗ [†κ])`;
- LftL-tok-fract;
- LftL-borrow `▷P ≡−∗ &κ_full P ∗ ([†κ] ≡−∗ ▷P)`;
- LftL-bor-acc `&κ_full P ∗ [κ]_q ∝ ▷P`.

On the last: "in our proofs, we will always be forced to give back all the lifetime tokens that we obtained."

Function types (§9.2): `∀α. fn(ϝ : E; τ) → τ`, with ϝ the function's own lifetime. The semantic instruction rule threads `⟦L⟧(1)` through pre and post (Fig. 12.x). So the tokens a call holds come back in its postcondition or through its return continuation. Adequacy is thesis Theorem 5. Mechanised in Coq/Iris.

**The survey's synthesis, checked against the text.** A suspended `perform` holding a token fraction breaks the call rule's "give back on return", because the return is delayed indefinitely. The repair is that tokens move through the protocol and are owned by κ (survey §1.7, "Semantic call rule"). The text supports the premise: tokens are threaded and must be returned. **No mechanised work combines the lifetime logic with handlers, coroutines, async or `Pin`.** That is a search result, not a proof of absence.

**For us.** L.7 is this repair. BoLo has no tokens: a lifetime is a stratum of `Life = ℕᵒᵈ`, and `[α]` boxes stand where token access would. So L.7's content for us is the stratum discipline at a stop, which is what conjunct 37 (`↭`) and `Row.Unwind`'s outlives conjunct encode today.

### 1.15 OxCaml `handled_effect` (implementation; static modes) [read]

- README: "Each effect handler can be represented as a `local` argument, which is needed to perform its operations. Functions accepting `local` functions are then effect-polymorphic".
- `continue : ('a,'b,'es) Continuation.t @ unique -> 'a @ once unique -> … -> 'b @ once unique`.
- "Exception raised when a continuation is continued or discontinued more than once. Only achievable with [Obj.magic_unique] or similar escape hatches."
- The borrow doc: `borrow_` gives a value that "is `local`: it cannot escape the current borrow region".

**For us.** This is L.1 shipped. The capability is a frame-local (second-class) borrow, κ is unique, and the same `local` mode serves borrows and handlers. There is no formal result.

### 1.16 State under resumption: Effekt, Koka, Flix [read, except where marked]

- **Effekt tour**: a `var` outside the handler is shared across resumptions; a `var` inside "actually backtracks … the captured continuation includes the initial state of `x`". Regions are second-class, and a boxed closure "may only ever be unboxed where region `r` is still in scope."
- **Koka book §3.4.10**: "If var declarations were instead heap allocated or captured by reference, they would no longer be local to their scope and side effects could 'leak' across different resumptions."
- **Flix**: regions "cannot outlive their lexical scope". What region memory does under multiple resumption is not documented [unverified]. Yarrow's report that it is UB is [relayed via Yarrow §8].

These matter for P10 only at multi-shot, which is ignored. They are listed because they show where the stack-allocated discipline places state.

### 1.17 Others [read]

- **Fluet, Morrisett & Ahmed 2006** (λrgnUL; Thm 1; Twelf): region access through a linear capability. "during the scope of the open, we temporarily lose the capability to deallocate the object, but regain the capability upon exit from the scope". This is the well-bracketed lend, with no control effects.
- **Timany, Guéneau & Birkedal 2024**: ghost stacks recover private transitions. Handlers are left as a conjecture (§10). This is P14's subject, not P10's.
- **Affect** (POPL 2025): "Affect's references Ref 𝜏 correspond to &Cell<𝜏>". Load is restricted to unrestricted types, and `replace` moves out. The semantic `Ref` is an invariant, with no exclusive borrow and no lifetime.

---

## 2. The statement shapes, side by side

### 2.1 P10 shapes

| shape | example | what it counts | where exclusivity comes from |
|---|---|---|---|
| (a) translation into a borrow calculus | HandlersAsBorrows (a)+(b) | the image's resources | B6 on the image; the capability is `Mut 'h S` |
| (b) ownership transfer in protocols | Hazel A1; Yarrow EWP-Do-Once | `P` sent, `Q` returned, framed rest | separating conjunction; non-persistent κ |
| (c) global validity over configurations | our `Exclusive`; survey T5(i) | the whole configuration plus held frames | `ResU.Valid` over `fρ`, `TI` over visible ∪ held |
| (d) yield-once projection | Hylo ¶8; SE-0474 | the projected object, frozen or inaccessible for the projection | static flow analysis; no proof |
| (e) separation of footprints | Capybara Thm 5.5; reachability Cor 4.8 | capture sets as footprints | checked at consume or separation points only |

**Shape (c)'s three counts, as our target reads (observation from reading; no Lean check run).**
- `Exclusive M` requires `ResU.Valid fρ` of every configuration `M.Fam fρ ps i` reaches, where `fρ` is the whole composed resource.
- Values in transit (an operation's argument inside the table at a stop, a resume value) and a running clause's resources are parts of `fρ`. So survey counts (ii) and (iii) are covered by validity of the whole, not by a separate clause.
- Count (i) is the `held` conjunct, and it sees only 6.64 frames and records. `SemWorld.held`'s docstring: "A 6.65 `Mut` lend adds no 6.64 frame or record, so `held` does not see it; a world that carries one open across a stop accounts for it through `Upd` and the index (OQ-9 (a), OQ-44)."

### 2.2 P9 shapes

| shape | example | what it observes |
|---|---|---|
| (a) progress + preservation with an undelimited-label stuck state | Ξ Thm 4.3–4.4; System C Cor 9; Capless §5.2.3; CC<:□ Thm 7.1–7.2 | a capability applied outside its delimiter gets stuck |
| (b) stack-discipline lemma | Osvald Thm 3.2, Cor 3.4 | no heap value holds a stack reference |
| (c) capture prediction | CC<:□ Lemma 4.11; CF<: Lemma 2.5 | a value's free capabilities are bounded by its type |
| (d) parametricity of a scope binder | Xie 2022 (subsumed by soundness); Biernacki Thm 1 | the binder cannot escape |
| (e) dynamic guard | Xie 2020 scoped resumptions | a mis-scoped resume gets stuck at `guard` |
| (f) semantic outlives | BoLo 6.60; our `LifetimeSound` | a value at a type that outlives `a` lives in `Res_α` |

**Two facts the tables show:**
1. **Every P9 result in the literature is shape (a) or (c), at a calculus with no exclusive borrows.** None states "no continuation resumed after a lifetime it borrows from ended" for lifetime-indexed `&mut`. Ours is shape (f), and B2's adequacy supplies (a)'s "never stuck" for free once the run reaches a use after free. That is how AT07's rejection is meant to follow (`RejectsAT07`, "a lemma derived from `Sound J`, to build").
2. **Every P10 result with a proof is shape (a), (b) or (e).** Shape (c), counting suspended loans globally at lifetime-indexed borrows, has no mechanised precedent.

---

## 3. Pitfalls

Each pitfall is mapped to the acceptance or rejection program in `Targets/I/Programs.lean` that pins it, where one exists.

1. **Iterator invalidation across a `perform`.** The body holds `&mut v` across an operation, and the handler, or the answer, changes `v`'s shape.
   - The survey's `v.push(do choose())` is **AT04**. It is accepted, because the answer is written *through* the lend after resume.
   - The bad half has the handler reaching `v` itself. That is excluded only if (6) holds.
   - Rust's E0626 forbids the analogous borrow in a movable coroutine.
2. **Two `&mut` into handler state** (survey §1.11 item 15; Ante rule (b)). This is **AT05**: "two `Mut 'h S` taken from one handler's state cell … `Mut` has no copy rule." It is rejected by X.1 with no new rule.
   - Ante documents it and does not enforce it (`q4`).
   - The lending-iterator GAT is Rust's static answer.
   - For control handlers the question returns: does each operation's answer end before the next operation at the same handler? That is X.2's obligation.
3. **A handler writing a place the suspended body borrowed** (survey §1.11 item 16; Yarrow UB). This is **AT06**: "a clause that writes a place the suspended body uses … Clauses are `!U`, so they capture only persistent values, and `c` is linear." It is rejected structurally.
   - Swift's actor rule is the same hazard under re-entrancy, and Swift gives up memory-safety reliance on the static rule because a dynamic check backs it.
4. **A continuation resumed after a lifetime it borrows from has ended.** This is **AT07**, "a continuation capturing a lend of `x`, stored past `x`'s release, then resumed". `at07_eval` shows the interpreter stops at a use after free, so the rejection is semantic and is to be derived from `Sound J`.
   - Ante's `'(_, resume)` invalidation on move is the design response.
   - System C's box with `at C` is the typed one.
5. **A continuation duplicated through a shared cell.** This is **AT08**. It is a P8 pitfall that becomes a P10 pitfall when κ holds a `Mut` lend, because the two copies alias it. Affect's restricted load is the literature's fix, and ours is `kTy` being neither droppable nor persistent.
6. **Resumption under a different handler.** Xie 2020 makes this a dynamic guard, and Biernacki 2020 shows resumptions are what let names escape.
   - Ours: OQ-3 and D-ORD. "Resumed by a handler between two lenders" is not among GhostEnd's built instances.
   - WorldW's `HandlerBetweenLenders*` probes are unfinished, and `AllCross` is discharged only at constant `true`.
   - **No acceptance or rejection program pins it.** That is a gap in `Accepts`/`Rejects`, not a finding about the calculus.
7. **Treating second-class as a binder mode** (Ante's colouring experience). If the restriction is not expressible as a type, higher-order code needs two copies. BoLo's restriction is a lifetime-polymorphic type (§1.1). The test is H4 (§5.2 L.1).
8. **A dynamic check standing in for a static rule** (Swift class properties, `RefCell`, Xie's guard, Ante's unenforced rules). Each turns a type error into a run-time panic or a stuck state. The assurance goal excludes this as a realisation of P10 or P9 (X.7).
9. **A capability laundered through an operation argument.** Ξ forbids blocks as operation arguments because "Otherwise blocks could escape their scope through the effect operation". For us this is R-CLOSEDOP's job (`¬ VFree x o.A`), and it is what OQ-56 (b) must keep for answers while relaxing it for arguments.
10. **Assuming the Iris route composes with RustBelt for free** (survey §1.11 item 20). This chapter's reading confirms that no mechanised work combines them.

---

## 4. Borrows × effects specifically: what is mechanised

| question | mechanised result | at lifetime-indexed `&`/`&mut`? |
|---|---|---|
| capability cannot escape its handler | Ξ (Idris), System C (Coq), Osvald (Coq), Biernacki 2020 (Coq), Capless (Lean 4), CC<:□ base (Coq) | no: scope only, capabilities duplicable |
| handler scope is a region | Müller 2023 (paper) | lifetimes as subregions, no exclusivity |
| stateful handler = mutable borrow | **ours, HandlersAsBorrows (Lean, PAPER)**, answering handlers only | **yes**, `Mut 'h S` at BoLo's judgment |
| ownership transferred through an operation and back | Hazel (Coq/Iris); Yarrow (Rocq/Iris, regions) | no lifetimes; Yarrow has stack regions |
| exclusive footprints | Capybara (Lean 4), reachability types (Coq/Rocq) | aliasing and separation, no lifetime-indexed reborrow |
| lifetime tokens | RustBelt (Coq/Iris) | **yes**, no handlers or continuations |
| a lend spanning a resuming operation | **ours, GhostEnd instances (Lean, Core σ=[])** | yes, instances only |
| yield-once lend | none (Hylo, Swift: implementations) | — |
| exclusivity counting suspended loans at a lifetime calculus | **none found** | — |
| continuation resumed after its lender's lifetime ended, rejected by typing | **none found**; AT07 is our pinned program | — |

The survey said: "No mechanized type system covers it for lifetime-indexed `&`/`&mut`." This chapter's reading did not find one either. The search covered RustBelt, Hazel, TES, Yarrow, Affect, the capture-checking line, reachability types and the second-class line.

---

## 5. The menu

Each entry gives:
- **shape**: the statement;
- **cost**;
- **buys**: the programs it admits;
- **interacts**: with I2, OQ-3, OQ-28, OQ-56, and rows versus capabilities;
- **evidence**.

### 5.1 X: exclusivity across the handler (P10)

**X.1 Reborrow encoding, answering handlers.**
- *Shape:* `handle` lends the handler's state as `Mut 'h S` through `withbor` form (2). An operation is `withswap` on it, and the clause is `!` code. P10 on the image is B6. This is decision 57's form, pinned as `I4a`.
- *Cost:* paid at PAPER. At Core it is `I4a` beyond abortive rows, plus OQ-1 (how the answering mechanism relates to `hnd`).
- *Buys:* AT05 rejected with no new rule. Effect safety becomes no use after a lifetime. The capability is first-class but bounded: HandlersAsBorrows (c) stores it in a heap cell inside the handler, which Ξ cannot express.
- *Interacts:* it is OQ-3 (c) by construction (`handle_is_shift`), and OQ-29 (b), K-BORANS, is its natural extension. Under capabilities it is the whole story for answering effects. Under rows the capability is implicit, and `I4Typing` relates the two forms.
- *Evidence:* `translate_typed`, `effect_safety`, `effect_safety_open`, `capability_not_outlives`, `twoBlocks_refused` (PAPER); `i4a_tier1` (Core σ=[], abortive).

**X.2 Reborrow encoding, control handlers.**
- *Shape:* at a resuming operation the clause receives the handler's state cell unfolded, as 6.66 unfolds `ℓ ↦ Mut α P̂` into `ℓ ↦ v ⋆ P̂(v)` for a run and owes it back. `resume` hands the cell back to the handler's frame for the resumed segment, and κ holds everything else. Survey A5 step 5 says the same in Rust terms: "calling `resume` hands `self` back to the continuation for the duration of the call".
- *Semantically* this is 6.66 across stops: I5.hiding, `AntiFrameW`, whose unfolding `antiFW` says "a stop owes the view and the computation again". Reading `AntiFrameW` as X.2's statement is an observation from reading; no Lean check was run.
- *Cost:* `AntiFrameW` at W at resuming tables (OPEN). Decision 59's state passing must be shown to be this round trip, not a second mechanism.
- *Buys:* rule (b) for control handlers, meaning each answer that borrows handler state ends before the next operation at that handler. An async scheduler's queue as handler state, under one mechanism.
- *Interacts:* it needs OQ-3 (a) or (c) for the state's lifetime. The literature's nearest are the yield-once accessors (§1.2), which are its one-operation special case with the roles reversed. Under capabilities it is a method call on a reborrow. Under rows, `opTable`'s entry carries the unfolded cell in `en.PA`/`en.PB`.
- *Evidence:* `wpG_M_antiFrameX` (Core, at `wpG`); GhostEnd's `ewpTS_M_antiFrameR` (GE); `AntiFrameW` stated (device).

**X.3 Count suspended loans in the world (OQ-9 (a)).**
- *Shape:* P10 as `Exclusive` states it: `Valid` of the whole configuration, with `TI` over visible ∪ held frames and records. A 6.65 lend open across a stop is accounted for through `Upd` and the index.
- *Cost:* `held` is defined only for 6.64 frames. Option (a) "has no Lean" (OQ-9). It costs the relation a no-copy-out-of-the-share property (WorldW FINDING-1). It must also show `TI`'s eight conjuncts survive a stop that leaves frames open.
- *Buys:* AT02, AT04, AT12 and AT17, read directly, with no re-lend at resume. Stack-allocated κ, as Yarrow's `Stack κ` keeps captured fibers' points-to.
- *Interacts:* I2's `Arises` is the same counting, and the two are proved together. OQ-57 (closing list) and OQ-8 (where the future-world quantifier sits). `FreezeBinder`'s location half if κ moves (AT17).
- *Evidence:* `exclusive_core`, `arises_core` (Core σ=[], nothing held); WorldW's resource-level hand-on for 6.64, 6.65 and 6.150 (probe); `HoldsChain` (exclusivity at a stop) open.

**X.4 Ghost-end: nothing held (OQ-9 (b)).**
- *Shape:* every internal lend ends at the stop and is re-lent fresh at resume, beneath the resumer (D-ORD). `held` is empty, and P10 is `TW` at each stop.
- *Cost:* re-lendability of the payload (WorldW FINDING-1). The general borrower reduces to `RelendOfTyped` (OPEN). Naturality: `mut_not_natural` refutes it at a stored `Mut` invariant, and whether the witness arises is unchecked. GFP is refuted as first stated, by a witness that does not arise (`wpG_below_not_arises`).
- *Buys:* P10 reduces to today's invariant. This is the freeze binder's lifetime half.
- *Interacts:* it presupposes OQ-3 (a) (GhostEnd README step 1). The cancel path is proved for 6.65 (`spans_two_affine_yields`), and cancel over a 6.64 frame is not built.
- *Evidence:* `withbor_spans_yields_cC`, `imm_spans_yield`, `spans_two_affine_yields`, `withborR_compat` (Core σ=[]).

**X.5 A borrow passed up ends at `resume` (Ante H2).**
- *Shape:* an operation's argument may be a lend `Mut 'x T` or `Imm 'x T` of the body's. Its extent is the clause, from the catch up to κ's consumption by resume or cancel. It is a well-bracketed lend whose end is a linear use of κ. Answers stay closed.
- *Cost:* an admissibility `Adm` beyond `admClosedOp` for arguments only. A proof that the printed frame rules plus `ewp_kappa_resume`/`ewp_kappa_cancel` close it without lifting T1 in general (H2, untested). Storing κ ends the lend, so Ante's rule does not cover a scheduler that queues κ while the handler holds the buffer.
- *Buys:* "lend a buffer to the handler for one operation", the synchronous half of async I/O. Hylo/Swift's yield-once projection is the dual: there the lender is the suspended party.
- *Interacts:* it is OQ-56 restricted to arguments. With L.2/L.3 it decides what happens when κ is stored: the lend must end, or the box must carry `'x`. Under capabilities the argument is a reborrow, so X.5 is X.2 with roles reversed.
- *Evidence:* none in Lean. GhostEnd's `payload_strict` concerns `'x` in a lent cell's content, not in an operation type.

**X.6 The clause cannot touch the body's places.**
- *Shape:* clauses are persistent code (`!U`), so they capture no linear place of the body. Handler state reaches them only through decision 59's passing.
- *Cost:* none at tier 1; it is how `[handle]` is built. At tier 2 the obligation moves into X.2/X.3: what the handler *receives* through `PA` must exclude the suspended frames' lends.
- *Buys:* survey A5 rule (c) and AT06's rejection. It matches Ante's "branches cannot `Mutate` any places used in the handled expression", enforced here and not in Ante.
- *Interacts:* Yarrow makes the same rule UB in a logic. It is X.1's "clauses typed as closures alive for the whole handle" (survey A5 step 4).
- *Evidence:* `[handle]`'s `!` premise; `Rejects` (AT06), OPEN at a typing system.

**X.7 Dynamic enforcement.** Swift's class-property rule and `RefCell` are listed for completeness. They are not a realisation of a static guarantee.

### 5.2 L: lifetimes of continuations and capabilities (P9)

**L.1 Second-class `resume` and capabilities, as frame-pinned borrows.**
- *Shape:* a capability is `Mut 'h S` or `Imm 'h S` at the handler's lifetime, and κ is a value at the frame's lifetimes. "Second-class" means the lifetime is instantiated at the frame and cannot be named outside it. P9 for capabilities is 6.60 plus `[]I`'s premise (`capability_not_outlives`, `escape_refused`). For κ it is the absence of any outlives rule at `U C`: κ cannot enter an `[α]` box, so it cannot outlive anything.
- *Cost:* nothing new for capabilities. For κ, storing needs L.2 or L.3.
- *Buys:* P9 as escape analysis (Ξ Thm 4.3–4.4, Osvald Cor 3.6). Stack-allocated κ and capabilities. Effect polymorphism for callbacks that are only called.
- *Interacts:* Ante's colouring objection (§1.1), which is the H4 test. Write `map`, `filter` and `fold` once over `∀'a. Mut 'a H ⊸ …` and check no second copy is needed. Osvald §1.9 and Müller §1.13 support the reading that second-class is the lifetime half of a borrow. OxCaml ships it (`local` capabilities, `unique` κ). Under capabilities it is decision 1's form; under rows, a capability is the row entry, and L.1 constrains κ only.
- *Evidence:* `capability_not_outlives`, `object_not_outlives`, `escape_refused` (PAPER); `thunk_not_outlives` (CoeffectsStrict); `OutJ.core` has no `U C` rule; SecondClass's `handleAt_compatC` (Core σ=[]).

**L.2 Boxed continuations at `[@c] U(Aff^c A B)` (OQ-28 (a)).**
- *Shape:* a `[gen]` rule gives κ a box at the meet of the lifetimes it borrows. Storing at `'r` needs `c ⊒ 'r`.
- *Cost:* T14.4's coinduction (`aff_coind`). `lift-stage1` built `genE`, `Qgen` and `ewp_gen` (L14.3), with T14.4, T14.6 and the rule unwritten.
- *Buys:* schedulers, generators and continuations in data, as System C Example 10 does.
- *Interacts:* AT07 must stay rejected; the box's bound is what rejects it. With X.5, a stored κ's passed-up lends must end or be in `c`. With L.4, `c` includes the handler's extent when κ uses it.
- *Evidence:* `box_lolli_outlives_iff` (PAPER); `ewp_gen` (branch, Core σ=[] under T1).

**L.3 An outlives rule at `U C` (OQ-28 (b)).**
- *Shape:* `Δ ⊢ U C ⊐ @a` holds when every lifetime C's environment holds outlives `a`. `[gen]` is then derived. 6.60's induction (`vC_outlives`) gains a `U` case. That case is capture prediction (CC<:□ Lemma 4.11) read through `C ↦ ⊓ lifetimes`.
- *Cost:* T2 (#173). The `U` clause of `vC` has the Kripke quantifier (`∀ ls', Ext ls ls' ρ → …`), and the case must hold at every extension (OQ-58).
- *Buys:* one rule for closures and κ. HandlersAsBorrows precondition 2 (`box`/`unbox` for closures crossing a scope) is the same rule.
- *Interacts:* with L.2 it is either/or. `LifetimeSound` then fires on κ, because `OutJ` gains the case. Today it is vacuous there.
- *Evidence:* `lolli_not_outlives` (PAPER: no rule at `⊸`); Capless's Lean-mechanised scope safety as the literature's nearest checked analogue, at a one-shot escape.

**L.4 Does a handler site open a lifetime (OQ-3)?**
- *Shapes:*
  - (a) `[handle]` takes an extent `∀'h`, and the body starts in `Res_h`;
  - (b) "a handler between two lenders" is a named restriction;
  - (c) only answering handlers open one.
- *Cost:* (a) changes `handle_compatC`. (b) costs programs, decided only through the user if it excludes one they want. (c) is today's paper result.
- *Buys:* (a) gives GhostEnd its handler extent, K-BORANS answers at `'h` (OQ-29 (b)), and L.5.
- *Interacts:* distinguishing (a) from (b) needs D-ORD (WorldW). Müller (region per handler), Biernacki (binder), Xie 2022 (rank-2 η) and Capless (`boundary` at an outer-well-formed type) all take (a) in their own terms. Under capabilities (a) is forced, since the capability needs a lifetime. Under rows it is a choice.
- *Evidence:* `handle_is_shift` (PAPER); `effHandle` opens none (`Core/Fundamental.lean:367-372`); `wpG_box`, `frozen_above_extent` (GhostEnd).

**L.5 Resumption under a different handler.**
- *Shape:* κ is resumed only where its captured lifetimes are live and beneath the resumer's (D-ORD). Xie 2020's static variant is "fully applied within the operation clause and no occurrences under a lambda". Müller's relaxation is any subregion of the capture's region.
- *Cost:* L.4 (a), and the freeze binder's lifetime half (forward instantiation, OPEN).
- *Buys:* it rules out resuming inside a younger lend, the between-lenders case.
- *Interacts:* I2's `ShareResume` quantifies over every `M.Ext` extension. Whether that is the right range is OQ-8's question.
- *Evidence:* `AllCross` at constant `true` only (`StackStep.lean:1280`); WorldW's `HandlerBetweenLenders*` unfinished.

**L.6 Lifetime-polymorphic operations at a borrow callback (OQ-56).**
- *Shapes:*
  - (a) R-CLOSEDOP, today's `admClosedOp`;
  - (b) operations quantified over a lifetime, instantiated at the lend, and masked when the lend ends;
  - (c) only lifetimes outside the borrow.
- *Cost:*
  - (b) is a new construct. The masking needs the Yoshioka conditions (P2). 6.65's conclusion puts whatever leaves the callback in `[α]`, so a stop that hands the lent view to an outer handler must be accounted for (GhostEnd's admissibility: "the borrower's share less its view lies in `[α]`").
  - (c) is a sub-case of `RowSpan`'s `Adm` with no new construct.
- *Buys:* (b) admits the async read into a local buffer, OQ-56's motivating program (`asyncRead`, with `at04` its stand-in).
- *Models:* Ante's `Mutate 'p`, discharged "once the function signature … no longer references `'p`", is the masking shape. Xie 2022's `vec^η` is a typed precedent with a rank-2 binder. Ante's `'(_, resume)` is the argument-only restriction, X.5.
- *Interacts:* AGREE question 5 asks whether done moves to the chosen `Adm`. It interacts with L.4, because a masked label's lifetime may be the handler's.
- *Evidence:* `Row.Unwind`, `Row.Unwind.out` (`Core/EffBorrow.lean:133–172`); `admClosedOp`, `RowSpan` (Targets); no Lean on an operation type mentioning `'x`.

**L.7 Lifetime tokens owned by κ (semantic counterpart).**
- *Shape:* in RustBelt terms, the token fractions a suspended frame holds move into κ's share, and resume returns them. In BoLo terms, κ's share holds resources in the strata of the lifetimes it borrows from, and the stop condition's `↭` and T1 conjuncts are relaxed to allow that.
- *Cost:* the stop change the brief names (conjuncts 37 and 40), with its SPEC entry.
- *Buys:* the semantic justification shared by L.1, X.3 and X.4. It is a way of stating, not a separate design.
- *Evidence:* `not_upd_of_new_mut` (LoopBorrow) and `RunEnd.lean` (Targets) show conjunct 37 is a real constraint.

### 5.3 How the families combine

- **X.1 + L.1** is the tier-1 shape, already largely in hand: answering effects as borrows, second-class κ, abortive borrow callbacks.
- **X.3 or X.4** is OQ-9's choice. Each needs L.4 (a) for the between-lenders case, and L.5 follows.
- **X.2 and X.5** are the two directions of one reborrow across a suspension: handler state down, body borrow up. Under capabilities both are reborrows of one object, which may make them one statement. Whether they reduce to 6.66 across stops (`AntiFrameW`) plus 6.65 at a resuming table (`MutFrameW`) is the probe.
- **L.2 or L.3** is OQ-28's choice, and each must keep AT07 rejected.
- **L.6 (b)** is the async lead-axis crux. It depends on X.5 for arguments and on L.4 for which lifetimes a label may mention.

### 5.4 Rows versus capabilities

The choice bears on these two properties as follows:
- **Under capabilities**, P9's capability half is 6.60 at `Mut 'h S` (L.1), proved at PAPER. P10's rules (a) and (b) are reborrow rules (X.1, X.2).
- **Under rows**, the capability is implicit. P9's capability half is effect safety (P2), and P10's rule (b) must be stated on `opTable` entries.

Row variables are in the kernel by decision 62, as an implementation choice. Neither property requires rows or excludes them.

---

## 6. Where our current targets sit

**P10.** `Exclusive M` (`Targets/I/Interface.lean`) and B6 `ExclusiveB` (`Targets/B/Guarantees.lean`) are both in done.
- *Status:* `exclusiveB_core` and `exclusive_core` are PROVED AT σ=[], from `TW.valid` and `TW.inv`, with `held = ([], [])`. Both are OPEN at W.
- *Shape:* §2.1 (c). Counts (ii) and (iii) come from validity of the whole configuration; count (i) is `held`, which sees 6.64 frames only.
- *Option fixed:* none. `held` is the world's field, so X.3 and X.4 both instantiate it, the second with nothing held.
- *Pinned programs:* AT05 (two `Mut` from one handler) and AT06 (clause writes a body place) are in `Rejects`. AT02, AT04, AT12 and AT17 are in `Tier2Programs`. **No program pins resumption under a different handler** (§3 item 6).

**P9.** `LifetimeSound M J.out` (`Targets/B/Guarantees.lean`) is in done.
- *Status:* `lifetimeSound_core` is PROVED AT σ=[] (`vC_outlives`, `vC_outlivesLe`), OPEN at W.
- *Shape:* §2.2 (f), 6.60 at W at the typing system's outlives judgments.
- *What it says about κ today: nothing.* `OutJ.core` has no rule at `U C`, so no κ type outlives any lifetime and the conjunct never fires on κ. It fires once OQ-28 adds L.2 or L.3. AT07's rejection is carried separately, as `RejectsAT07` derived from `Sound J` (to build).
- *What it says about capabilities:* under rows there is no capability value, so the capability half is P2's. Under X.1 it is 6.60 at `Mut 'h S`.
- *Fixed:* done is at `admClosedOp` (L.6 (a)) until OQ-56 is chosen (AGREE question 5).

**The device.** `AntiFrameW` (I5.hiding) is X.2's semantic statement. `FramesW`'s `MutFrameW`/`ImmFrameW` at resuming classes are X.3's and X.4's frame obligations. `SpanBorrows` at `Adm` is where L.6 (b) would enter. All are OPEN at W.

**Observations from reading, with no Lean checks run:**
- `Exclusive` states only "`TI` over visible ∪ held". If X.3 is chosen and a 6.65 lend stays open across a stop, `held` does not see it. P10 then rests on `Valid fρ` alone for that lend, and `TI`'s `NoMut` conjunct would have to be read with the lend's cell inside κ's share. Whether that is enough is the `HoldsChain` question WorldW left open.
- The menu's X.2 reading of `AntiFrameW` and L.3's reading of capture prediction are hypotheses about statement shape, not checked equivalences.

**Unspent and untranscribed** (CLAUDE §5, as it applies to a survey chapter):
- No printed BoLo lemma is used beyond 6.60, 6.64–6.66 and the withbor rows. The run-up of `fundamentalC` includes [TR] 6.40, the one untranscribed row of `Paper/INDEX.md`.
- No obstruction is claimed in this chapter. Every "not built" above means "I have not derived it and have not verified that any obstruction is real."

---

## 7. What could not be verified

- First-class names, OOPSLA 2022 camera-ready (ACM DL unreachable). Quoted from MSR-TR-2021-10 v1, which does not list Ikemori.
- Müller et al.'s extended TR with the full proofs.
- The contents of the Coq/Lean artifacts: System C (zenodo 5833713), `felko/ccsubbox`, `Linyxus/capless-lean`, `tiarkrompf/reachability`, `aleff-lex`. Coverage is relayed from the papers.
- Whether Fourment–Xu covers CC<:□'s §7 boundary extension (not claimed anywhere).
- TES's semantic clause for `τ ref`.
- Flix's semantics for region state under multiple resumption.
- "Borrow checking Hylo" (IWACO 2023), abstract only. No formal calculus for Hylo projections was found.
- Lucassen–Gifford masking: cited from our notebook, not re-read.
- The absence of any mechanised lifetime-logic + handlers development is a search result.
- Ante's claims are relayed from our deep dive, which ran probes at `3e680ef3`. They were not re-run here.

---

## Sources

**Read for this chapter, from full text:**

- de Vilhena, Pottier. *A Separation Logic for Effect Handlers.* POPL 2021. §3.1.1, Fig. 3 (A1), §3.3, §4.2.2, §4.2.4, Thm 4.1. https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf
- de Vilhena, Pottier. *A Type System for Effect Handlers and Dynamic Labels.* ESOP 2023. Thms 1–3, §3. https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-tes.pdf
- Mathiasen, Timany, Birkedal. *Yarrow.* arXiv 2607.15876v2. §1, §3.1, §4.1, Figs. 6–9, §8. https://arxiv.org/abs/2607.15876
- Jung, Jourdan, Krebbers, Dreyer. *RustBelt.* POPL 2018. §5, Fig. 4, Thms 7.1–7.2. https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf
- Jung. *Understanding and Evolving the Rust Programming Language* (PhD thesis). Fig. 11.1, §9.2, Figs. 9.6, 12.1, 12.5, Thm 5. https://research.ralfj.de/phd/thesis-screen.pdf
- Timany, Guéneau, Birkedal. *The Logical Essence of Well-Bracketed Control Flow.* POPL 2024. Thm 3.1, §10. https://iris-project.org/pdfs/2024-popl-wbcf.pdf
- Fluet, Morrisett, Ahmed. *Linear Regions Are All You Need.* ESOP 2006. Thm 1, §5. https://www.khoury.northeastern.edu/home/amal/papers/linrgn.pdf
- van Rooij, Krebbers. *Affect.* POPL 2025. §2.2, Thm 2.1, Fig. 7. https://iris-project.org/pdfs/2025-popl-affect.pdf
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki. *Effects, Capabilities, and Boxes.* OOPSLA 2022. TR: Thms 3, 5; Lemmas 4, 6, 7; Def 8; Cor 9; [Try], [BoxIntro], [BoxElim]; Example 10; §5.2. https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects.pdf
- Osvald, Essertel, Wu, González Alayón, Rompf. *Gentrification Gone too Far?* OOPSLA 2016. Lemma 3.1, Thms 3.2, 3.3, 3.5, Cors 3.4, 3.6. https://www.cs.purdue.edu/homes/rompf/papers/osvald-oopsla16.pdf
- Müller, Schuster, Starup, Ostermann, Brachthäuser. *From Capabilities to Regions.* OOPSLA 2023. Lemma 3.5, Thms 3.6, 3.7. https://pure.au.dk/ws/files/404551780/3622831.pdf
- Xie, Brachthäuser, Hillerström, Schuster, Leijen. *Effect Handlers, Evidently.* ICFP 2020 (extended). §2.2, Thms 2–8. https://www.microsoft.com/en-us/research/wp-content/uploads/2020/07/evidently-with-proofs-5f0b7d860b387.pdf
- Xie, Cong, Leijen. *First-class Names for Effect Handlers.* MSR-TR-2021-10 v1. Thms 3.1, 3.3, 3.4, 4.1–4.3. https://www.microsoft.com/en-us/research/wp-content/uploads/2021/05/namedh-tr.pdf
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Binders by Day, Labels by Night.* POPL 2020. Thms 1–5. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl20.pdf
- Brachthäuser, Schuster, Ostermann. *Effects as Capabilities* (System Ξ). OOPSLA 2020. Def 4.2, Thms 4.3, 4.4, 5.1. https://infoscience.epfl.ch/bitstreams/d8c0cff1-6103-46c7-acb6-c9cc3dbb2704/download
- Odersky, Boruch-Gruszecki, Lee, Brachthäuser, Lhoták. *Scoped Capabilities for Polymorphic Effects.* arXiv 2207.03402. Thms 4.6, 4.8, Lemmas 4.11–4.15. https://arxiv.org/abs/2207.03402
- Boruch-Gruszecki, Odersky, Lee, Lhoták, Brachthäuser. *Capturing Types.* TOPLAS 45(4), 2023. Thms 4.6, 4.8, 4.14, Lemmas 4.11–4.13, §7 Thms 7.1–7.4. https://plg.uwaterloo.ca/~olhotak/pubs/toplas23.pdf
- Boruch-Gruszecki et al. *Tracking Captured Variables in Types.* arXiv 2105.11896. Thms 2.3, 2.4, Lemma 2.5, Cor 2.6, §3 (handle). https://arxiv.org/abs/2105.11896
- Fourment, Xu. *A Mechanized Theory of the Box Calculus.* EPFL TR 2023. https://infoscience.epfl.ch/record/302949
- Xu, Bračevac, Pham, Odersky. *What's in the Box* (System Capless). OOPSLA 2025. Thms 5.1–5.3, §5.2, §9. https://arxiv.org/abs/2509.07609 ; Lean: https://reservoir.lean-lang.org/@Linyxus/capless
- Xu, Boruch-Gruszecki, Odersky. *Degrees of Separation.* OOPSLA 2024. Thms 4.1–4.4. https://arxiv.org/abs/2308.07474
- Xu, Bračevac, Pham, Zhao, Odersky. *System Capybara.* arXiv 2607.09383. Thms 5.1, 5.2, 5.4, 5.5, 5.7, 5.8, Cor 5.3. https://arxiv.org/abs/2607.09383
- Wei, Bračevac, Jia, Bao, Rompf. *Polymorphic Reachability Types.* POPL 2024. Thms 4.6, 4.7, Cors 4.8, 4.9. https://www.cs.purdue.edu/homes/rompf/papers/wei-popl24.pdf
- Deng, He, Jia, Bao, Rompf. *Capture Now, Consume Later.* arXiv 2510.08939v2. Thms 3.1, 3.2, Lemma 3.3, Cor 3.4, §6.2. https://arxiv.org/abs/2510.08939
- Scala 3 capture checking reference: separation-checking, scoped-capabilities, classifiers, mutability. https://docs.scala-lang.org/scala3/reference/experimental/cc.html (pages under `scala-lang.org/api/3.x/docs/experimental/capture-checking/`)
- Hylo specification (`spec.md`: Subscript implementations ¶6–7, Yield statements ¶1–3, Projections ¶6–10) and language tour (Subscripts, Bindings). https://github.com/hylo-lang/specification/blob/main/spec.md ; https://github.com/hylo-lang/hylo-lang.github.io
- Racordon, Shabalin, Zheng, Abrahams, Saeta. *Implementation Strategies for Mutable Value Semantics.* JOT 2022. Def 4.1, Lemmas 4.1–4.2, Thm 4.1. https://www.jot.fm/issues/issue_2022_02/article2.pdf
- Swift Evolution SE-0474 (Yielding accessors), SE-0176 (Enforce exclusive access to memory), SE-0306 (Actors, "inout parameters"), SE-0296 (async/await). https://github.com/swiftlang/swift-evolution/tree/main/proposals
- Rust RFC 2394 (async_await), RFC 1598 (GATs), RFC 2033; error code E0626; clippy `await_holding_refcell_ref`, `await_holding_lock`. https://github.com/rust-lang/rfcs ; https://github.com/rust-lang/rust/blob/master/compiler/rustc_error_codes/src/error_codes/E0626.md
- Jane Street `handled_effect` (README; `oxcaml` branch `handled_effect_intf.ml`) and OxCaml docs (`stdlib/effect.mli`, modes intro, uniqueness/borrow). https://github.com/janestreet/handled_effect ; https://github.com/oxcaml/oxcaml
- Effekt tour, regions. https://github.com/effekt-lang/effekt/blob/master/examples/tour/regions.effekt.md
- Koka book §§3.2.4, 3.4.10, 3.4.11. https://koka-lang.github.io/koka/doc/book.html
- Flix book: Regions, Effects and Handlers, Primitive Effects. https://github.com/flix/book

**Relayed:**

- Ante: homepage, language tour, ideas page, blog posts (2024-02-20, 2025-05-21), compiler at `3e680ef3`, probes `p1`, `p4`, `q2`, `q2b`, `q4`, `q5`. Via `~/repos/borrow-core/research/effects/ante-deep-dive.md`, which lists the URLs.
- Survey A4, A5, T5, P5–P8, P10, P13, §1.7, §1.11: `research/effects/survey.md`.
- Lucassen, Gifford, polymorphic effect systems (masking): via the notebook.

**Local sources:**

- `~/repos/borrow-core/docs/effects-state/BRIEF.md` §§1–4, 7; `05a-open-questions-1-34.md` (OQ-3, OQ-9, OQ-28, OQ-29); `05b-open-questions-35-68.md` (OQ-56, OQ-57, OQ-58).
- `~/repos/borrow-core/experiments/HandlersAsBorrows/README.md`; `experiments/SecondClass/README.md`.
- Core: `Core/RelationFacts.lean:479` (`vC_outlives`), `:575` (`vC_outlivesLe`); `Core/EffBorrow.lean:118` (`ewp_box_end`), `:133` (`Row.Unwind`), `:163` (`Row.Unwind.out`); `Core/Invariant.lean:1836` (`TI`), `:2702` (`TW.inv`); `Core/EffDefs.lean:144` (`contShare`); `Core/Types.lean:1730` (`VOutlivesR`, no `U C` case).
- [TR] `3764117-supplement.pdf`: Lemma 6.60, Theorem 6.65 (Mut Frame), Theorem 6.66 (Anti Frame).
- Targets (`~/repos/borrow-core-targets/experiments/Targets`):
  - `Targets/B/Guarantees.lean` (`LifetimeSound`, `ExclusiveB`, `Guarantees`);
  - `Targets/I/Interface.lean` (`Exclusive`, `Arises`, `AntiFrameW`, `FramesW`, `SpanBorrows`, `admClosedOp`, `RowSpan`);
  - `Targets/I/World.lean` (`SemWorld.held`);
  - `Targets/I/Programs.lean` (AT02, AT04–AT08, AT12, AT13, AT17, `Rejects`, `RejectsAT07`);
  - `Targets/B/BoLo.lean` (`lifetimeSound_core`, `exclusiveB_core`);
  - `Targets/I/Restricted/Core.lean` (`exclusive_core`, `arises_core`);
  - `Targets/Base/Typing.lean` (`OutJ`);
  - `AGREE.md`.
- Notebook: `intro.md`, `system-a.md`, `system-b.md`, `interaction.md`, `decisions.md`, `foundations/{second-class,bolo,freeze-binder}.md`, `properties/{exclusivity,lifetimes,i2-capture-resume,i4-answering-borrows}.md`, `tracks/worldw-batch1.md`.
