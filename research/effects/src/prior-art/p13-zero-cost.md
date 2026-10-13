# Prior art: P13, zero-cost lowering (effect handling erased)

This chapter surveys the literature for one System A property, [P13](../properties/zero-cost.md). It ends in a menu of options with their trade-offs. It does not recommend one.

**The property.** Each lowering class preserves behaviour:
- a tail-resumptive (answering) operation becomes a direct call;
- an abortive operation becomes a branch;
- a suspension becomes a state machine.

None of them allocates or indirects beyond what hand-written C or Rust would. The lowering is chosen by specialisation, so there is no function colouring. OQ-23 asks whether lowering correctness is a theorem.

**Decisions that bound the menu** ([decided constraints](../decisions.md)):
- **Effect handling is erased.** In the user's words: "Part of 18 needs to be effect handling is erased." The relayed refinement: "erased" does not mean "always a direct call"; "The criterion is cost parity. A handler never adds cost of its own." (`docs/effects-state/04-decisions.md` L1)
- **L2, portable lowerings.** No Wasm feature without a plain LLVM counterpart. Handlers lower to stackless state machines. Stack switching may only be an optimisation with a portable fallback.
- **L3, the zero-cost target.** Allocate and indirect only where C or Rust would, measured by corpus counts.
- **No function colouring.** Lowering is chosen by specialisation.
- **The core is linear**, and discard is an explicit cancel. Handlers are deep. Cancellation is what SPEC §19 builds.
- **Multi-shot is ignored** (decision 63). It appears here only as context.
- **Nothing breaks the borrow calculus.** Lowering is below the model, so it touches B only through placement (§5).

**L4 is not reconciled.** The returning/suspending split is polarity, "decided by shift cancellation read off the handler's type, with no operation-kind annotation". Today an operation declares `fn` or `ctl`. No record reconciles the two (04-decisions L4). The C options in §6 are where this lands.

**Verification marks** (as in [rows-vs-capabilities](rows-vs-capabilities.md)):
- **[read]**: the statement was read in the primary full text for this chapter, by me or by a retrieval agent I ran, and the quote is copied from that text.
- **[relayed]**: from a sibling chapter, the survey, the Ante deep dive, or a secondary source.
- **[unverified]**: not checked.
- **[local]**: read off this repository's code or documents.
- **[synthesis]**: my reading, not a source's claim.

Theorem numbers follow the version named in the sources list. Several are numbered from technical reports.

---

## 0. Menu at a glance

The menu has three parts, and each part's axis is independent of the others:
- **Z: what P13 states and how it is proved.** This is OQ-23.
- **C: where the lowering gets a callback's control class.** This is the specialisation key, and it is fed by the [rows-vs-capabilities](rows-vs-capabilities.md) options.
- **P: where suspended state is placed.** This is where tier 2 (lends across a suspension) lands in the lowering.

The lowering *mechanisms* in the literature (§2) are context, not options: L1 and L2 already fix calls, branches and stackless state machines. Cross-menu codes refer to the sibling chapters:
- R/S: [P2](p2-effect-safety.md);
- 8.x/5.x/X.x/F.x: [P8/P5](p8-p5-linearity-drop.md);
- M/T: [I2](i2-capture-resume.md);
- X/L: [P10/P9](p10-p9-exclusivity-lifetimes.md);
- O: [rows-vs-capabilities](rows-vs-capabilities.md).

| # | option | statement shape | buys | main cost | nearest literature | ours today | requires / excludes / favours |
|---|---|---|---|---|---|---|---|
| **Z0** | **Counts + reports** (decision 48's acceptance) | no theorem; `counts.expected` and `kernel-counts.expected` gate at "at most"; `bcc check` prints each handler's lowering | regressions caught on every corpus program, today | the lowering's meaning is checked only by stages agreeing with the interpreter on the corpus | Koka, Effekt and Lexa measure cost and never prove it (§1.3) | **operating**: the gate (`compile-corpus.sh`, `compile-kernel.sh`) | none; compatible with all |
| **Z1** | **Per-class laws at the source** | for each class, an equation or run fact over the kernel: tail clause ≡ call; abortive clause ≡ catch-and-branch; capture ≡ the frame-by-frame state relation | names what each class must preserve, without a compiler proof | at `hnd`, these are binary or run-level laws, which A₂ leaves out of the first pass | Xie–Leijen 2021 Thm 5 (the tail-resumptive optimisation is sound, `e ≅ctx e`); libhandler Thm 1 | `op_tail` and `op_answer` hold at the `withswap` encoding only (`Core/Handlers.lean`); nothing at `hnd` | favours P11's laws (A₂); needs "binary laws optional" lifted for this purpose |
| **Z2** | **Whole-pipeline semantic preservation on complete runs** | A₃'s `LoweringCorrect`: source run to `v` with io trace `tr` ⇔ `Tgt` run to `enc v` with `enc tr` | the target observes exactly what the source does, for terminating programs | a proof per backend pass (Convert, Capture, Unwind, Collapse, 0-CFA soundness, layout types, Flat.Lower); no mechanised precedent for handlers | CompCert Defs 1–5 and Thm 3 (forward simulation plus target determinism gives backward); Lexa Thm 2; Ma et al. 2025 Cor 1 (paper proofs) | **stated** (`Targets/A/Lowering.lean`), out of the first pass; no theorem in `Backend/` | needs S-g's trace reading (P2) for io; the cancel entry needs 5.1's traces (P5) to be observable beyond io |
| **Z2⁺** | Z2 **with diverging and reacting runs** | behaviours `Terminates / Diverges / Reacts`, with coinductive traces | covers div as codata: E3's loops and E10, the reconciler | coinductive traces, or a per-iteration statement | CompCert `Behaviors.v` (`Reacts : traceinf`); CertiCoq Cor 8.3 (divergence preserved); ITrees `eutt` | not stated: `ZeroCost` and `LoweringCorrect` read complete runs only; RESTRUCTURE §1.7 plans a per-iteration statement | required if E10 is to be covered; same proof as Z2 with a coinductive simulation |
| **Z3** | **Validated passes** as Z2's proof route | some passes proved, others checked per program by a verified checker | the 0-CFA solution and the layout types are checked, not proved general; a solution is easier to check than to compute | a checker per validated pass; a compile-time cost | CompCert's validated passes (relayed); CerCo labelling (Props 16, 21) | the README says "Nothing checks the solution at run time" for the flow analysis | a route to Z2; independent of C and P |
| **Z4a** | **Cost parity on a fixed corpus** | A₃'s `ZeroCost`: each lowered corpus program's allocations and dispatches are ≤ those of its fixed hand-written reference | the decision's criterion, read literally; padding a lowering is excluded | references not written (`refCost` is `(0,0)` and unchecked); the corpus omits driven and tier-2 programs | none for handlers; Schuster 2020 Thm 5.5 is syntactic ("no residual lambda") | **stated**, unchecked | favours P2 (Rust's reference for a tier-2 program is a pinned frame) |
| **Z4b** | **General cost refinement: "a handler adds no cost of its own"** | for every program, the target's allocations and dispatches are ≤ a source-level cost that charges handler constructs 0 and charges `alloc`, arrays, boxes, recursion through a resumption point and unknown-code calls their cost | the user's sentence as a theorem over all programs, not a corpus | a cost semantics on the source; the exceptions (Box::pin, `dyn`) have to be visible in it | Quantitative CompCert Thm 1 (stack weight ≤ under refinement); CerCo Props 16, 21; CertiCoq Cor 8.2 (space ≤ source + an additive constant) | not stated | stronger than Z4a; needs Z2's simulation instrumented with counters |
| **Z5** | **Erasure by the target's shape** | `Tgt` has no instruction that captures, saves, restores or searches a stack, so every correct lowering is erased | "no runtime handler" with no extra theorem | erasure in this sense still allows a heap-allocated handler runtime; only Z4 rules that out (`not_zeroCost_of_heapRuntime`, to build) | WasmFX and Salt are the opposite: targets with stack instructions | **stated** (part of A₃) | needs Z4 to exclude heap runtimes; excludes the K4 lowerings below as the semantics |
| **C1** | **Instantiated row's profile** | specialise `h` per (function, profile of the instantiated row) | exact class at every instance, with no grade | copies per profile (typing instances per row shape until a row-extension lemma) | Koka's two translations plus a run-time test (one bit); Schuster 2020 stack-shape monomorphisation | **as built**: one copy per effect assignment (SPEC §18) and per callback computation type (§14) | O1/O4; with R1's static names, routing is static |
| **C1b** | C1 plus a **class bound on row variables** | one shared body compiled at the bound `RowCon.cls` | an un-specialised body that is still not the worst class | one more annotation; not consumed by any lowering statement yet | none found; "a class in the type would be ours" (rows-vs-capabilities §0.2) | `RowCon.cls` exists in the targets, unused by A₃ | O1-ε-bounded |
| **C2** | **Value-keyed specialisation** | specialise per callback value (block code plus the handlers its captures are bound to), as Rust does per closure type | no effect in HOF types (contextual polymorphism) | an un-specialised body must compile every block call as a possible resumption point | Schuster 2020 (static handlers, second-class capabilities, full elimination); Lexa reads the class from a run-time header-frame annotation | the 0-CFA already finds the code at most calls ("Every other call of the corpus is direct") | O2/O3-surface; favours L.1 (second-class resume) |
| **C3** | **A class grade on blocks and boxes** | the class is in the callback's or box's type | restores C1's information to O2 | a grade former and its subsumption | none found | none | O2-g, O3 (EffModel's `inst E b`) |
| **C4** | **The class read off the handler** (L4: polarity / shift cancellation; EffModel's `susp`) | the exact class is the handler's, not the declaration's; the declaration gives only a bound | a `ctl` handled by a tail-resumptive clause is a call (SPEC §19 already does this) | needs the handler statically: static names (R1) or lexical binding (O2) | Koka's run-time `tail`/`normal` dispatch; Lexa's header-frame annotation; Ante "largely determined by the handler" | **as built** for tail clauses: "the same closed clause … a direct call" | combines with any of C1–C3; reconciles L4 |
| **C5** | **Fallback when unknown** | (a) worst class; (b) two versions plus a run-time bit (Koka); (c) dispatch through a tag | separate compilation, smaller code | (b) is a run-time test, which erasure forbids if it reads handler information; (c) costs one `switch` | Koka TR §5.3.2; evidence passing §6.3 | (c) for closures (`apply`); `two-callees` dispatches "as `Box<dyn Future>` does" | (b) conflicts with "no effect information at run time" |
| **P0** | **No lend spans a suspension** (tier 1) | nothing placed beyond the state's words | nothing to prove | rejects `gen-self-borrow` and AT02/AT04/AT12/AT17 | rustc's E0626 for movable coroutines | **as built** (T1 conjunct 40, `↭` conjunct 37) | M0 |
| **P1** | **Spanned places stay heap cells; the state is freely movable** | the state machine's state holds only words, and a spanned place is a cell whose address does not move | tier 2 needs no Pin in the lowering; T3's location half is trivial at run time | one allocation per spanned place, which a pinned Rust frame does not pay; this conflicts with L3's escape-analysis placement of cells | OCaml 5 (fibers move because "OCaml does not generate pointers into the stack"); Effekt LLVM (stacks move, behind "prompts with stable addresses") | **the representation as built**: cells are `alloc`ed; closures and `κ` are stack values | M1 or M2; T2; fails Z4a/Z4b against a pinned-frame reference |
| **P2** | **Spanned places inline in a pinned state** (T4) | a frozen state is placed once and never moves; self-borrows point into it | Rust parity: no allocation for a self-borrow | a placement rule; moving a placed κ (task migration) is rejected | Rust `Pin`, E0733/E0626, RFC 2033 ("No implicit memory allocation"); LLVM switched-resume with CoroElide | none | T4; M1 or M2; L.2/L.3 for a boxed κ (the box is the placement) |
| **P3** | **Inline places, relocated on move** | moving a frozen state rewrites its internal addresses | movable and allocation-free | a relocation map at run time, which C/Rust do not pay | none found for interior pointers; OCaml relocates only because it has none | none | excluded by L3 in practice [synthesis] |
| **P4** | **Stackful, non-moving** | each suspension gets its own stack | tier 2 by construction | a stack per handler instance; excluded as the semantics by L2 | Ante (minicoro), Lexa (stacklets), WasmFX (`cont.new`), libmprompt | none; L2 allows it as an optimisation only | excluded as the semantics |

**Where our target sits (§7).**
- **Z.** In Lean, A₃ is Z2 + Z4a + Z5, stated and out of the first pass. In practice Z0 operates.
- **C.** C1 with C4 for tail clauses, as built.
- **P.** P0 by the typing, over a representation that is already P1.

---

## 1. Canonical statements

### 1.1 Compiler correctness: the shapes

- **CompCert** (Leroy, JAR 2009) [read]. Behaviours are `converges(t, n) | diverges(T) | goeswrong(t)`, with `T` "finite or infinite trace (coinductive)".
  - Definitions: "Definition 2 (Backward simulation) ∀B, C ⇓ B =⇒ S ⇓ B"; "Definition 4 (Forward simulation) ∀B, S ⇓ B =⇒ C ⇓ B".
  - On determinism: "even if forward simulation holds, the compiled code C could have additional, undesirable behaviors … However, this cannot happen if C is deterministic … 'forward simulation' implies 'backward simulation'."
  - Theorem 3 (lock-step simulation) and Theorem 4 (star simulation) are the per-pass tools.
  - The current statement (`driver/Complements.v`): `transf_c_program_preservation : … program_behaves (Asm.semantics tp) beh -> exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh`. `Behaviors.v` has `Reacts : traceinf`.
  - On stack space (§17): it "is a program property that is not naturally preserved by compilation".
- **CakeML** (Tan et al., JFP 2019) [read]. `semanticsB ffi new_prog = semanticsA ffi prog` when the source does not fail, or else `⊆ extend_with_resource_limit`. The paper says this weaker form "allows for a trivial compiler implementation that always outputs a program that immediately cause an out-of-memory error". Exceptions are compiled by "assigning a stored value to the stack pointer and jumping to a stored code pointer". There are no effect handlers. Pancake (PLOS 2023) [read] has `Raise` and handlers in `ret`, and a verified stack bound, but no effect handlers.
- **Interaction Trees** (Xia et al., POPL 2020) [read]. `Theorem compile_correct (s : stmt) : equivalent s (compile s)`. The comparison is `eutt` *after* `interp` applies each side's state handler: "the bisimulation does not hold over the uninterpreted ITrees." Handling is interpretation, applied before comparing.
- **Defunctionalisation** (Pottier–Gauthier, HOSC 2006) [read]. "Theorem 5.5 p ⇑ implies ⟦p⟧ ⇑. p ⇓ implies ⟦p⟧ ⇓." It is proved by forward simulation. Our backend defunctionalises every closure (Backend README, *Representation*) [local].

### 1.2 Cost as a theorem

- **Quantitative CompCert** (Carbonneaux, Hoffmann, Ramananandro, Shao, PLDI 2014) [read].
  - Quantitative refinement: "For every behavior B′ ∈ ⟦s′⟧ there exists B ∈ ⟦s⟧ such that B = B′ and W_M(B′) ≤ W_M(B) for all stack metrics M". Cost is made observable as call and return events.
  - Theorem 1: under a stack of size `sz`, "T refines S in the sense of CompCert … In particular, T cannot go wrong and thus does not stack overflow."
- **CerCo labelling** (Amadio, Ayache, Régis-Gianas, Saillard, arXiv 1010.1697) [read].
  - "Proposition 16 If M is soundly labelled and (M, m) ⇓ (m′, λ) then the cost of the computation is bounded by κ(λ)".
  - Proposition 21 lifts the target cost back to a source cost variable, bound or exact.
  - The FOPARA 2013 Matita compiler is [relayed].
- **CertiCoq, safe for space** (Paraskevopoulou–Appel, ICFP 2019) [read].
  - Corollary 8.2: "c1 ≤ c2 ≤ k_time ∗ c1 and m2 ≤ m1 + cost^space_exp(e) + 1".
  - Corollary 8.3 preserves divergence with the same space bound.
  - Composing with other passes "cannot happen at the level of logical relations".
  - The ICFP 2021 pipeline theorem (Thm 6.2, Cor 6.3) carries no cost bound at the top level.

**Shape note** [synthesis]. Every cost theorem found is a *refinement*: target cost ≤ source cost (+ a constant). A₃'s `ZeroCost` is an *absolute* bound against fixed reference programs on a corpus. Z4b is the refinement form.

### 1.3 Effect-handler compilation: what is proved and what is measured

| source | what is proved (statement, number) | where proved | cost claims | what allocates |
|---|---|---|---|---|
| Xie et al., ICFP 2020, *Evidently* [read] | Thm 5 (evidence corresponds to the dynamic context); Thm 8 (coherence, up to `≅`); Thm 9 (to multi-prompt control, `⌈e1⌉ ↦→* ⌈e2⌉`); Thm 11 (monadic translation coherent) | paper; proofs in a TR | "a cost similar to a virtual method call" (measured, argued) | the monadic bind "takes an allocated lambda"; §6.4 drops binds for "total functions … effects provided by the host … statically guaranteed to be tail resumptive" |
| Xie–Leijen, ICFP 2021 [read] | Thm 5 "(Tail-resumptive Optimization is Sound) If ∅ ⊢ e : σ \| ϵ, then e ≅ctx e"; Thm 7 (semantics preserving, closed `int` programs, termination and divergence) | paper; TR | counter: "libhandler … 1.5× faster … it does no allocation at all. In contrast, both Koka and OCaml still allocate at each operation" | yield path: `yield_extend(alloc_closure_join1(x,ctx),ctx)`, heap closures built "piecemeal while bubbling up" |
| Leijen, MSR-TR-2016-29 [read] | only source soundness (Thm 1); **no theorem for the selective CPS or the two-version scheme** | paper | "the code size increased by a modest 20%" | CPS'd functions |
| Perceus, MSR-TR-2020-42 [read] | Thm 4 (precise and garbage free), for λ1 with **no handlers, resumptions or references** | paper | — | — |
| Schuster et al., ICFP 2020 [read] | Thm 5.1 (typability); Cor 5.2 (effect safety); Thm 5.4 (full residualisation); Thm 5.5 "(Full elimination) … do not introduce any residual lambda abstractions or applications"; **no semantics-preservation theorem**: the source semantics *is* the translation | paper (Idris implementation) | "up to 409x" against Koka 0.9, Multicore OCaml and Chez | "one additional continuation argument per stack shape entry" |
| Schuster et al., TR 2019, *Zero-cost by staging* [read] | Thm 5 "(Zero overhead)", worded as ICFP Thm 5.5; assumes "(a) all used handler implementations and (b) the order in which they enclose the effectful computation" are static | paper | — | monomorphisation "rules out separate compilation" |
| Schuster et al., PLDI 2022 (TR) [read] | Thm 8 (typing, **Coq**); Thm 10 "(Simulation) If ⊢ M ok and M → M′, then M⟦M⟧ →* M⟦M′⟧" (paper) | Coq for typing only | — | uniform CPS, not selective |
| Müller et al., OOPSLA 2023 [read] | Thms 15, 17: CPS and direct style are inverses on pure code; Cor 20 | Idris for typing; paper | — | — |
| Lexa, OOPSLA 2024 [read] | Thm 2 "The translation from Lexa to Salt is semantics-preserving" (Leroy's forward-simulation criterion, Thm 1) | paper (appendix) | "tail-resumptive and abortive handlers do not incur any heap allocation" | a heap stack per general `handle`; class dispatch reads "the annotation in the handler's header frame" at run time |
| Ma, Ge, Jung, Zhang, OOPSLA 2025 [read] | Thm 1 (simulation); Cor 1 (semantics preservation); **no zero-overhead theorem**: "code should not pay for exceptions unless they are actually raised" | paper | mainline cost measured against Direct Lexa | tables in the data section; nothing on the stack "besides the return address" |
| Hillerström et al., FSCD 2017; JFP 2020 [read] | FSCD Thm 7 (simulation) and Cor 8 (backward, "as our semantics is deterministic"); JFP Thms 7, 8 and Cor 1 "⟦M⟧ ⇝* V if and only if M ⇝* V" | paper | — | — |
| Kobayashi–Kameyama, APLAS 2025 (arXiv 2509.11901) [read] | "Theorem 4. EFFone is macro-expressible in AC"; "Corollary 1. EFFone cannot macro-express AC" | paper | — | — |
| WasmFX (OOPSLA 2023); Iris-WasmFX (PLDI 2026) [read] | Thms 3.1, 3.2 (preservation, progress); WasmFXCert Thm 3.1 (type safety, **Rocq**); Iris-WasmFX Thm 4.2 (adequacy) | paper; Rocq | — | "cont.new … creates a new continuation (i.e., a stack)" |

**Search result** (verified-compilation agent, [read] negative). No mechanised end-to-end correctness theorem was found for compiling algebraic effect handlers, coroutines or async/await to a lower-level target. This is a search, not a proof of absence. The nearest mechanised neighbours are the typing of a CPS translation (Coq, PLDI 2022), a target semantics (WasmFXCert) and verified effect libraries (Iris-WasmFX). **A Lean `LoweringCorrect` for a handler lowering would be new** [synthesis].

**No zero-cost theorem for handlers exists in this reading** [synthesis, from the rows above]:
- Schuster's "zero overhead" is a syntactic statement: no residual λ.
- Ma 2025's "zero-overhead" is a design principle.
- Koka's costs are measured.

---

## 2. How prior systems lower, by class

| system | tail-resumptive | abortive | suspension | where the class is decided | HOF instances | proof |
|---|---|---|---|---|---|---|
| Koka (evidence passing) [read] | in place, through an evidence vector at a constant offset (closed rows) or `find_ev` (polymorphic rows) | yields to the handler | monadic bubbling; continuation closures heap-allocated on the yield path | at run time: `case h.op of tail f → … \| normal f → yield …`; static only for `fun`-declared or linear effects | Koka 2016: two versions and a run-time test | paper, TRs |
| Effekt (ICFP 2020; current) [read] | eliminated when static | eliminated when static | CPS; LLVM backend uses segmented, growable stacks with "prompts with stable addresses" | statically: stack shapes plus static handlers | monomorphisation per stack shape | paper; Coq for typing |
| Lexa [read] | a call on the parent stack | stack cut to the header frame | a heap stacklet per `handle` | run time, from the header-frame annotation | — | paper |
| OCaml 5 [read] | as a general perform | as a general perform | a malloc'd fiber per handler ("initially 16 words"), grown by copying; a heap continuation object per perform; one-shot checked dynamically | none: one mechanism | — | semantics only, "no theorem" |
| WasmFX [read] | as general | `resume_throw` | a stack per `cont.new` (4 KiB in the prototype) | none | — | Rocq type safety |
| Rust coroutines / async [read] | — | `Result` and `?` | a state machine; "MIR locals which are live across a suspension point are moved to the coroutine struct"; variants overlap where storage does not conflict | the programmer (async colour) | monomorphisation per closure type | none |
| LLVM switched-resume, C++20 [read] | — | — | frame in a "coroutine object", **heap unless CoroElide applies** ("for recursive or mutually recursive functions this elision is usually not possible") | the programmer | — | none |
| Kotlin [read] | — | — | one state-machine object "when suspending function is invoked", reused across its suspending calls | `suspend` colour | — | none |
| Ante (`3e680ef3`) [read, source] | inlined: "`resume v` … becomes a jump to the continuation block" | `setjmp`/`longjmp`: "an abort implementation skips any drops on the call stack" | minicoro stackful coroutines | the handler's shape | monomorphised evidence | none |
| **ours** [local] | a direct call when every handler of the name has "the same closed clause" (SPEC §19) | branch per call, `inl`/`inr` sums (`Clos/Unwind.lean`) | a stackless state machine: an `n`-ary sum state, nested through calls, `κ` of static size (`Clos/Capture.lean`) | statically: the closure flow's least solution, "the rows' information, recovered after erasure" | copies per effect assignment and per callback type (SPEC §14, §18) | none in `Backend/`; obligations listed in the README's *Verification* |

**What is unique to ours** [synthesis]:
- No other system in this table lowers every class with no stack instruction and no run-time class test, while also being polymorphic over callbacks without colour.
- Rust and Kotlin get stackless state machines by colouring.
- Koka gets no colour, but pays a run-time test and heap continuations.
- Effekt gets full elimination by static handlers and monomorphisation, and pays nothing on the static path. Its residue is the higher-order value parameter (§4.3: "we cannot define handlers as handler functions in λλCap").
- Kobayashi–Kameyama Thm 4 is the expressiveness warrant: one-shot handlers are macro-expressible in asymmetric coroutines, which are what a state machine implements. Reading this as "stackless state machines suffice for every one-shot program" is my inference, not the paper's.

---

## 3. Ours today: the backend and its counts

**The pipeline** [local]: closure IR, then layout types, then 0-CFA, then flat IR, then Wasm (`Backend/README.md`).
- There is no handler stack and no search.
- `Tgt` in A₃ is modelled on the flat IR.
- Every stage is checked against `Support`'s interpreter on the corpus.
- `Backend/` contains no theorem.

**Counts against the hand-written equivalents** [local: `corpus/kernel-counts.expected`, `corpus/counts.expected`, SPEC §18–§19]:

| program | ours (allocs, dispatches) | hand-written | reading |
|---|---|---|---|
| `log-outside-native`, `fail-outside-native`, `tick-native` | 0, 0 | 0, 0 | parity at `hnd` with state passed (decision 59) |
| `log-outside`, `fail-outside`, `tick-answering` | 1, 0 | 0, 0 (the flag passed by hand) | the answering encoding `with h(e)` = `borrow mut (alloc(e))` allocates the state's cell |
| `effects-map` / `effects-map-hand` | 11, 0 | 11, 0 | parity (state lent from a cell in both) |
| `effects-fold` / `effects-fold-sum` | 7, 0 | 7, 0 | parity for abortive |
| `take` / `capture-take-hand` | 2, 2 | 1, 0 | SPEC attributes the extra allocation and the dispatches to the program (its unary count and a handler answering one of two closures) |
| `store-cancel` | 2, 0 | 2, 0 | parity |
| `loop-tail`, `loop-captured`, `resume-tail` | 0, 0 | — | direct calls; constant stack |
| `recursive-yield` | 20, 0 | Rust needs `Box::pin` per level (E0733) | "one frame object per level, reused at each resume" |
| `two-callees` | 0, 3 | `Box<dyn Future>` | dispatch at the call and at each resume |
| `forward` | 4, 0 | — | two objects per level: "One per level would box one edge of the cycle … only" |
| `clause-captures` | 6, 3 | — | "a native handler parameter is not built" |

**Three gaps against L3, by reading** [synthesis; no Lean or counts run for this chapter]:
1. **An answering handler over a fresh state costs one cell.** Rust passes `&mut` to a stack slot. `docs/effect-polymorphism.md` §10 names the same cost for a re-lent callback environment ("The one cost Rust does not pay"). Both are the **cell-placement question** (README *Open*: "Placement of the objects that remain (stack, frame arena or heap, by escape analysis) is also open"). It is not a handler cost; it is a borrow cost that answering handlers inherit through X.1's reborrow encoding.
2. **A clause that captures values is a state machine**, with dispatched state-passing answers. SPEC §19 *Open* lists "compiled as a direct call with its captures passed to the operation as evidence".
3. **`forward` costs two objects per level where one would do.**

---

## 4. Pitfalls

1. **"Zero cost" measured against the wrong baseline.**
   - Schuster's baseline is "no residual λ" (syntactic).
   - Ma 2025's is Direct Lexa.
   - Koka's is its older runtime ("nqueens: evidence 46.09×", JS backend).
   - L1's baseline is the hand-written Rust or C program. A₃ fixes the baseline as reference programs in A, which is the only form that cannot be gamed by the instance ([read] for the sources; [local] for A₃).
2. **Run-time class tests disguised as erasure.** Koka (`tail`/`normal`), Lexa (header-frame annotation) and Koka 2016 (the `k?` test) all read handler information at run time. Our decision forbids "effect information at run time" [local: memory]. So C5(b) is out unless the test reads only a closure tag.
3. **Correctness on terminating runs only.**
   - Xie–Leijen Thm 7 covers divergence. CompCert covers `Reacts`.
   - A₃'s `LoweringCorrect` quantifies over `RunsTo`, complete runs, so it says nothing about the io trace of a reconciler loop. With div as codata, that is the main program shape (E10).
3a. **CakeML's escape hatch.** A theorem that allows a resource-limit behaviour is met by a compiler that always runs out of memory. A₃'s `Tgt` has an unbounded heap and no stack bound, so it avoids this and also says nothing about stack depth (`fold_imm`'s native frames) [synthesis].
4. **Heap allocation hidden in the "zero-cost" coroutine.**
   - C++20 and LLVM switched-resume allocate the frame unless CoroElide applies, which needs an inlined ramp, no escape, and no recursion.
   - Kotlin allocates one object per suspending invocation.
   - Rust allocates nothing implicitly (RFC 2033 goal: "No implicit memory allocation"), and `Box::pin` is explicit for recursion (E0733).
   - Our `recursive-yield` is the Rust case, made implicit.
5. **Moving frames with interior pointers.**
   - OCaml 5 moves fibers only because "OCaml does not generate pointers into the stack".
   - Effekt's LLVM backend moves stacks and indirects through "prompts with stable addresses".
   - libhandler restores "a stack at the exact same location" by copying, "around 300× times slower".
   - Rust forbids self-borrows in movable coroutines (E0626).
6. **Abort that skips destructors.** Ante's `setjmp`/`longjmp` "skips any drops on the call stack". Our branch-per-call runs finalisers on the `inr` path, so this is avoided by construction [local].
7. **Dynamic scoped-resumption guards.** Evidence passing needs `guard`, and "If the evidence does not match, the evaluation is stuck" (Xie 2020 §4.5). That is a run-time check, so it cannot carry an erased lowering. The static form is L.5 / D-ORD [read; synthesis].
8. **One-shot enforced by a run-time flag.** OCaml 5 overwrites `ke` with NULL, and WasmFX traps on a dead continuation. P8's option 8.3 (a one-shot cell in the machine) would be a store per resume unless it is ghost [read; synthesis].
9. **Selective CPS that colours.** Rompf et al. 2009's transform is "driven entirely by effect-annotated types" [read: abstract]. The claim that its `@cps` annotations colour higher-order functions is [unverified].

---

## 5. Borrows, lifetimes and tier 2 in the lowering

**The literature.** No source in §1–§2 states a lowering theorem in the presence of borrows. Rust is the only production system with borrows across suspension, and it is unproved engineering:
- E0626 forbids self-borrows in movable coroutines;
- `Pin` makes static coroutines immovable;
- the layout pass stores "the locals that are needed to continue the coroutine".

Ante relies on minicoro stacks never moving and has no proof (relayed: ante-deep-dive §5).

**Ours: where tier 2 lands** [synthesis, from `Backend/README.md` *Representation* and SPEC §19 *Lowering*]:
1. **Lifetimes are erased.** A lend at run time is an address word, and the borrow world is below the model. So the I2 options **M1** (ghost end, re-lend fresh) and **M2** (carry the lend open) lower to **the same code**: the state holds the place's address across the stop either way. The tier-2 choice among M1, M2 and M3 is a proof choice, invisible to P13.
2. **Places are cells, and cells are heap objects.** The state machine's state, closures and `κ` are words moved freely ("a closure is a stack value", "`κ` is a value of statically known size"). A place lent across a suspension is a cell whose address does not change when the state moves. So **as built, the representation is P1**. Self-reference needs no Pin, and the location half of freeze-as-binder (T3) has nothing to rename at run time.
3. **The cost is the cell's allocation.** A Rust `async fn` holding `&local` across `.await` puts `local` inline in the pinned frame and allocates nothing. Under P1, `genSelf` and AT17 lowered against a pinned-Rust reference **fail Z4a and Z4b** by one allocation per spanned place.
4. **L3 pushes towards P2.** L3 wants cells "placed by escape analysis", meaning in frames. Once a spanned cell is placed inside the state, the state becomes self-referential, and the lowering needs T4 (placement once, never moved after) or T3 at run time (P3, which C and Rust never pay).
   - **Second-class κ (L.1, T2):** the placement is the stack frame that owns it.
   - **Boxed κ (L.2/L.3):** the box is the placement, and Rust's `Box::pin` is the precedent.
5. **A₃ is silent on tier 2.** Its corpus is the terminating (E) programs. `Tier2Programs` (AT02, AT04, AT12, AT17, `genSelf`) are not in it, so the P1-versus-P2 cost is not stated even as a target.
6. **Cancel is the state's destructor.** Its correctness obligation is the README's: "its cancel entry simulates the cancel run `K[raise (⊥, s)]` to `ccatch`". For a spanned lend, the lend ends when the cancel runs the borrow's unwinding finaliser. That is a lowering-level form of P5's "ends every lend" (5.6).

**What would be new** [synthesis]:
- (i) A lowering-correctness theorem for a handler lowering at all, which nothing found mechanises.
- (ii) Any lowering statement over a calculus with borrows across suspension.
- (iii) A cost statement whose reference is a pinned Rust frame.

---

## 6. The menu, in detail

### Part Z: what is stated and proved (OQ-23)

**Z0. Counts and reports (the status quo; decision 48).**
- *Shape:* `counts ≤ expected` per corpus program, with an "at most" gate; per-handler `lowering` lines in `bcc check`.
- *Cost:* nothing new.
- *Buys:* every corpus program, including tier-1 effect programs and the driven ones the A₃ corpus omits.
- *Interactions:* decision 48's premise, that erasure is "true by definition" of elaboration, was removed by effects-are-core (05a OQ-23). Z0 alone therefore no longer has its stated justification.
- *Evidence:* the gate; §3's table.

**Z1. Per-class laws at the source.**
- *Shape:* per class, a law over the kernel relation:
  - tail-resumptive: `hnd n h K[perform (n,i) v] ≡ hnd n h K[clause v]` when the clause is closed and resumes in tail position;
  - abortive: the unwind reaches the catching frame through finalisers;
  - control: the state relation of README *Verification* ("the state relating to `K` frame by frame").
- *Cost:* the tail and abortive laws are A₂-shaped binary laws, out of the first pass ("optional unless safety needs them"). Unary run-fact forms like `op_tail` are cheaper.
- *Buys:* per-class meaning, independent of the backend's passes, and reusable as Z2's lemmas.
- *Interactions:* favours P11's laws at the kernel (A₂ `HandlerLaws`) and I5's β (`I5beta`). Needs C4's "closed clause" side condition as a hypothesis.
- *Evidence:* Xie–Leijen Thm 5 and libhandler Thm 1 are exactly this shape for the tail-resumptive optimisation [read]. Ours: `op_tail`, `op_answer` at `withswap` only [local].

**Z2. Whole-pipeline preservation on complete runs (A₃'s `LoweringCorrect`).**
- *Shape:* both directions on complete runs at data answers, io traces encoded, for every target platform simulating the runner.
- *Cost:* a simulation per pass. The README lists the obligations: defunctionalisation (Pottier–Gauthier Thm 5.5 shape), 0-CFA soundness, layout typing, native fixed points, pointer reversal (Schorr–Waite), state machines, collapsing.
  - CompCert's route applies: forward simulation per pass, then backward from `Tgt`'s determinism.
  - `Tgt` is deterministic given the platform [synthesis: `Call` is a big-step relation over a functional `co`].
- *Buys:* E1–E9 run identically. It is the only option that proves "no runtime handler" means the *same* program.
- *Interactions:*
  - It needs S-g ([P2](p2-effect-safety.md) §6.2: "the property P13 lowering preserves") for the io reading.
  - The cancel entry's correctness is visible only through answers and io unless P5's 5.1 traces are observable.
  - It favours the R1 static names (P2), which make routing a compile-time constant.
- *Evidence:* nothing mechanised for handlers (§1.3); Lexa and Ma 2025 on paper.

**Z2⁺. With diverging and reacting runs.**
- *Shape:* CompCert's `Reacts` with coinductive traces, or RESTRUCTURE's per-iteration statement for `iterOpen`.
- *Cost:* coinduction over `Tgt`; the drive is a loop of tail calls.
- *Buys:* E3, E10 and every `Loop_Σ` program. With "divergence is codata", these are the north-star shape.
- *Interactions:* the same as Z2.
- *Evidence:* CompCert `Behaviors.v`; CertiCoq Cor 8.3; Xie–Leijen Thm 7's divergence clause; ITrees `eutt`.

**Z3. Validated passes (a proof route to Z2).**
- *Shape:* a Lean checker per hard pass. The candidates are the 0-CFA solution ("each set over-approximates") and the layout unification.
- *Cost:* a checker and its soundness; a compile-time cost.
- *Buys:* removes the two most global analyses from the general proof.
- *Interactions:* none with B.
- *Evidence:* CompCert's validated passes [relayed]; CerCo's labelling is a validated cost (Props 16, 21) [read].

**Z4a. Corpus cost parity against fixed references (A₃'s `ZeroCost`).**
- *Shape:* as stated.
- *Cost:* writing `Tgt.ref` and `refCost_spec`. Today `refCost` is `(0,0)` everywhere and is "not checked".
- *Buys:* the criterion read literally, which no instance can pad.
- *Interactions:*
  - The corpus omits the driven programs and tier 2.
  - The references are hand-written Rust/C equivalents. For a tier-2 program the reference would be a pinned frame, so Z4a extended to tier 2 requires P2.
  - Our surface `with h(e)` costs one cell (§3), so a corpus program written through the answering encoding would need the cell placed (P2's placement, or a native handler).
- *Evidence:* §3's counts, by reading only.

**Z4b. "A handler adds no cost of its own", as a refinement.**
- *Shape:* `allocs(lower e) ≤ A(e)` and `dispatches(lower e) ≤ D(e)` for every typed closed `e`.
  - `A` charges `alloc`, arrays, boxed fields, and one per level of recursion through a resumption point (the Box::pin analogue).
  - `D` charges calls of a closure of a type whose union the flow cannot resolve.
  - Handler, perform, raise, cancel and κ are charged 0.
- *Cost:* the source cost functions must be stated over the kernel, which needs a cost semantics. Z2's simulation is instrumented with counters.
- *Buys:* the user's sentence over all programs, including the ones no corpus foresees. It also replaces corpus maintenance as the criterion.
- *Interactions:*
  - It makes the C5(c) dispatch and the recursion allocation **visible source costs**, as Rust makes them visible (`dyn`, `Box::pin`).
  - Under P1, a spanned place's cell is charged at its `alloc`, so Z4b holds where Z4a-against-Rust fails. The difference between Z4a and Z4b is exactly the P1/P2 question.
- *Evidence:* Quantitative CompCert Thm 1, CerCo Prop 21 and CertiCoq Cor 8.2 are this shape for stack, cycles and space [read]. None covers handlers.

**Z5. Erasure by the target's shape.**
- *Shape:* `Tgt` has no stack-capturing instruction.
- *Cost:* none beyond Z2.
- *Buys:* L2 as a fact of the statement.
- *Interactions:* it excludes P4 as the semantics. It needs Z4 to exclude a heap-allocated handler runtime (`not_zeroCost_of_heapRuntime`, planned in RESTRUCTURE §1.7).
- *Evidence:* stated.

### Part C: where the class comes from (the specialisation key)

These options are the [rows-vs-capabilities](rows-vs-capabilities.md) options read from the lowering's side. Its §0.2 finding stands: "No published system passes the class to a HOF through its types", and "borrow-core's elaborator already specialises per callback type and per handler assignment (SPEC §14, §18), which is further than any of these compilers goes for HOFs". This chapter's reading adds Effekt's stack-shape monomorphisation (Schuster 2020: "This specializes effectful programs to their stack shape") as the nearest precedent for type-keyed specialisation. A stack shape counts handlers; it does not classify them.

- **C1, the instantiated row's profile** (O1, O4).
  - *Key:* (function, profile of the instantiated row). The profile is which of abort and suspension the row contains (`docs/effect-polymorphism.md` §5.8).
  - *Cost:* code copies per profile. The typing instances per row shape remain until a row-extension lemma exists.
  - *Buys:* the exact shape at every instance.
  - *As built:* yes, keyed more finely (per assignment and per callback type).
- **C1b, the bound on ε** (O1-ε-bounded, `RowCon.cls`).
  - *Buys:* a shared body compiled at the bound, the only way to have *one* body that is not worst-case.
  - *Cost:* a class annotation. Not consumed by A₃.
- **C2, value-keyed** (O2, O3-surface).
  - *Key:* (function, block code plus its captures' handlers). This is Rust's per-closure-type monomorphisation.
  - *Cost:* without specialisation, every block call is a possible resumption point, so the body is a state machine (the worst class).
  - *Buys:* annotation-free HOFs.
  - *Fits:* our 0-CFA already resolves "every other call of the corpus" to one code. Second-class blocks (L.1) are only passed down, so the key is always known at the call. That is Schuster's "full elimination" condition.
- **C3, a grade** (O2-g, O3's element bound, EffModel's `inst E b`). The class is in the box's type, so a *stored* callback (`[@c] U C`) keeps it. Without it, O2-lt's lifetime bound "forgets *which* capabilities, so it forgets the class too" (rows-vs-capabilities §2.2).
- **C4, from the handler** (L4 polarity; EffModel `susp` by `Tm.tailOnly`).
  - The exact class is a property of the handler in scope.
  - The declaration (`fn`/`ctl`) gives only a bound.
  - SPEC §19 already lowers a `ctl` whose handlers share one closed tail clause to a call.
  - C4 needs the handler statically: R1's static names, or O2's lexical binding.
  - It is the option that reconciles L4 with decision 55 [synthesis].
- **C5, the fallback.**
  - (a) Worst class.
  - (b) Koka's two versions with a run-time bit, excluded by "no effect information at run time" when the bit reads handler state.
  - (c) Tag dispatch (`apply`, `two-callees`), the `Box<dyn …>` analogue, which Z4b charges to the source.

**How each rows-vs-capabilities option feeds the lowering:**

| | key at a HOF instance | un-specialised fallback | stored callback (`U C` boxed) | static routing |
|---|---|---|---|---|
| O1 | C1; C1b with a bound | bound or worst | the row in the stored type: class kept | R1 static names |
| O2 | C2 | worst (C5a) or dispatch | lifetime bound only: class lost (needs C3) | lexical binding |
| O2-g | C2 or C3 | the grade | the grade | lexical |
| O3 | C1 over instances, or C3 | the join of bounds; EffModel's "indirect call" per unknown instance | the row of lends: class and lifetimes kept | instances are binders |
| O4 | C1 at the ambient context | as O1 | `[E]` modality or a variable | per `X` |

### Part P: placement of suspended state (tier 2)

- **P0. No span** (M0).
  - *Buys:* nothing to place.
  - *Costs:* the I2 programs.
  - *Requires:* M0. *Excludes:* T4's purpose.
- **P1. Heap cells for spanned places; movable state.**
  - *Buys:* T3's location half free at run time; κ movable (scheduler migration, threads).
  - *Costs:* one allocation per spanned place; fails Z4a against a pinned reference; conflicts with L3's placement of cells.
  - *Requires:* M1 or M2 (indistinguishable here), and T2 or L.2/L.3 for stored κ.
  - *Evidence:* the representation as built. OCaml 5 and Effekt LLVM are the movable-runtime precedents, made safe there by having no interior pointers or by an indirection.
- **P2. Inline places, pinned state** (T4).
  - *Buys:* Rust parity (RFC 2033: "No implicit memory allocation").
  - *Costs:* a placement rule (the I2 chapter's T4); no move after placement.
  - *Requires:* T4. *Favours:* L.1 (stack placement) and L.2 (box placement), and threads only as "a placed κ sent to another thread stays at its address" (I2 chapter T4).
  - *Evidence:* Rust E0626/E0733 and `Pin`; LLVM CoroElide conditions [read]. No proof anywhere.
- **P3. Inline places, relocation.** No precedent for interior pointers. It is a run-time cost C/Rust do not pay. Listed for completeness.
- **P4. Stackful.**
  - *Buys:* tier 2 by construction (Ante, Lexa).
  - *Excluded as the semantics* by L2. Permitted as an optimisation only with a portable fallback, so it never discharges P13.

### Interactions with the other menus, collected

| other menu | option | P13 effect |
|---|---|---|
| P2 | R1 static names | makes routing a constant (Z2 easier, C4 available) |
| P2 | R4 scoped rows / masking | masking is static (an index shift in Koka's evidence) [synthesis]; compatible |
| P2 | R5 capabilities, generative names | runtime labels would need comparison; SPEC §19 *Open* confines them behind a scoped continuation |
| P2 | S-g | Z2's io reading |
| P8/P5 | 8.3 one-shot cell | a store per resume unless ghost; disfavoured by Z4 |
| P8/P5 | 8.4 ghost obligation | free at run time; favoured |
| P8/P5 | 5.1 cancel traces | makes the cancel entry's correctness observable in Z2 |
| P8/P5 | F.2 resuming finalisers | a suspension inside the cancel entry: κ's state holds `cfin` frames; the resume code's `inr mask` entry would itself suspend [synthesis] |
| P10/P9 | X.1 reborrow encoding | as built it allocates the state's cell (`log-outside` 1 vs 0); needs cell placement for parity |
| P10/P9 | X.2 / decision 59 state passing | 0 allocations at `hnd` (`*-native`) |
| P10/P9 | L.1 second-class resume | stack-placed κ: P2 by construction, C2 always keyed |
| P10/P9 | L.2/L.3 boxed κ | the box is the placement (`Box::pin`) |
| P10/P9 | L.4 handler lifetime | erased; no cost |
| P10/P9 | L.5 D-ORD static | required by erasure: Koka's dynamic `guard` is the alternative, excluded |
| I2 | M1 vs M2 | identical code (§5.1) |
| I2 | T3 | free at run time under P1; a run-time cost (P3) under inline places |
| I2 | T4 | P2 |
| rows-vs-capabilities | O1–O4 | Part C table |

---

## 7. Where our current target sits

### 7.1 Position

- **Z.** A₃ (`Targets/A/Lowering.lean`) states Z2 (complete runs only), Z4a and Z5, out of the first pass. `LowClass` names the three classes (`Instance/ZeroCost.lean`). Z0 is what operates.
- **C.** C1 at a finer key (per assignment and per callback type), plus C4 for tail clauses, as built. `RowCon.cls` (C1b) exists in the targets and is unused by A₃.
- **P.** P0 by the typing (T1, `↭`), over a representation that is P1.

### 7.2 Observations from reading, with no Lean checks run

1. **`LoweringCorrect` is about complete runs.** By reading, a reconciler's (E10) io trace is outside it, and the corpus omits driven programs. Z2⁺ is the candidate. I have not built an instance showing a lowering that meets `LoweringCorrect` and mis-orders a driven loop's io, and have not verified that any gap is real.
2. **`ZeroCost`'s references are unchecked.** `refCost` is `(0,0)` at every entry with no `Tgt.ref`. One E1′ claim, "a state machine whose state lives in the caller's frame", is the P2 placement. Our backend's κ is a stack value of known size, so by reading this is met for tier-1 programs.
3. **The answering encoding allocates.** By the counts, the surface answering handler over a fresh state costs one cell that the native `hnd` form does not. Which form A₃'s instance lowering would use for E4/E5 is not fixed. The kernel `*-native` programs suggest `hnd` meets `refCost`.
4. **Tier 2's cost is unstated.** The I2 `Tier2Programs` are not in the A₃ corpus. Whether P1's per-place allocation is acceptable is a user question in the shape of Z4a-against-Rust versus Z4b.
5. **OQ-23's premise.** Decision 48 replaced the erasure theorem with laws, counts and reports because elaboration made erasure "true by definition". With effects in the kernel (`hnd`, `perform` as Core primitives, lowered by `Capture.lean`), that premise is gone (05a OQ-23). Z1–Z4 are the theorem shapes on offer. The user decides.

### 7.3 Inventory

- **Unspent hypotheses and unused results we have:**
  - `RowCon.cls` (C1b);
  - EffModel's `susp` and `inst E b` (C3/C4);
  - `op_tail`/`op_answer` (Z1, at `withswap` only);
  - `Core/Fix.lean`'s `selfV_steps_in`, which the README names as the source side of the native-fixed-point simulation;
  - the determinism of Core's machine (`Core/Steps.lean`), the source half of CompCert's backward argument.
- **Untranscribed literature results in the run-up:**
  - CompCert's Thm 3/Thm 4 simulation diagrams;
  - Pottier–Gauthier Thm 5.5 for our defunctionalisation;
  - Xie–Leijen Thm 5 (the tail-resumptive optimisation) for C4's direct call;
  - Quantitative CompCert's weighted refinement for Z4b;
  - Kobayashi–Kameyama Thm 4 as the expressiveness warrant for stackless lowering.
- **Not checked:**
  - whether `Tgt.Run` is deterministic as stated;
  - whether the backend's flat IR embeds into `Tgt` as RESTRUCTURE claims;
  - the rustc-dev-guide prose (the compiler's module docs were read instead);
  - Rompf et al. 2009's body text;
  - the appendices of Lexa 2024 and Ma 2025;
  - the ACM numbering of the PLDI 2022 and Perceus theorems.

---

## Sources

Read for this chapter (primary full text by me or a retrieval agent; numbering as in the version named):
- Leroy. *A formally verified compiler back-end.* JAR 2009. arXiv:0902.2137 (Defs 1–5, Thms 3, 4, 7; §17). CompCert sources `common/Behaviors.v`, `driver/Complements.v`, https://github.com/AbsInt/CompCert
- Carbonneaux, Hoffmann, Ramananandro, Shao. *End-to-end verification of stack-space bounds for C programs.* PLDI 2014. https://flint.cs.yale.edu/flint/publications/veristack.pdf (§3.1, Thm 1)
- Amadio, Ayache, Régis-Gianas, Saillard. *Certifying cost annotations in compilers.* arXiv:1010.1697 (Def 15, Props 12, 16, 18, 21)
- Paraskevopoulou, Appel. *Closure Conversion Is Safe for Space.* ICFP 2019. https://www.cs.princeton.edu/~appel/papers/safe-closure.pdf (Cors 8.2, 8.3)
- Paraskevopoulou, Li, Appel. *Compositional Optimizations for CertiCoq.* ICFP 2021. https://www.cs.princeton.edu/~appel/papers/comp-opt-certicoq.pdf (Thm 6.2, Cor 6.3)
- Tan et al. *The verified CakeML compiler backend.* JFP 2019, doi 10.1017/S0956796818000229 (§2.3)
- Åman Pohjola et al. *Pancake: Verified Systems Programming Made Sweeter.* PLOS 2023. https://cakeml.org/plos23.pdf
- Xia et al. *Interaction Trees.* POPL 2020. arXiv:1906.00046 (`compile_correct`)
- Pottier, Gauthier. *Polymorphic Typed Defunctionalization and Concretization.* HOSC 2006. http://cambium.inria.fr/~fpottier/publis/fpottier-gauthier-hosc.pdf (Thms 4.3, 5.5)
- Hillerström, Lindley, Atkey, Sivaramakrishnan. *Continuation Passing Style for Effect Handlers.* FSCD 2017 (Thm 7, Cor 8). Hillerström, Lindley, Atkey. *Effect handlers via generalised continuations.* JFP 30 e5, 2020 (Thms 7, 8, Lemma 7, Cor 1)
- Xie, Brachthäuser, Hillerström, Schuster, Leijen. *Effect Handlers, Evidently.* ICFP 2020. https://xnning.github.io/papers/icfp20evidently.pdf (Thms 4–11; §§2.2, 4.5, 6.2–6.5)
- Xie, Leijen. *Generalized Evidence Passing for Effect Handlers.* ICFP 2021. https://xnning.github.io/papers/multip.pdf (Thms 1–7; §§2.7–2.11, 5)
- Leijen. *Type Directed Compilation of Row-Typed Algebraic Effects.* MSR-TR-2016-29 (Aug and Dec 2016 versions; Thm 1; §§5.1.1, 5.3.2)
- Reinking, Xie, de Moura, Leijen. *Perceus.* MSR-TR-2020-42 v4 (Thms 1–4; §2.7.1)
- Leijen. *Implementing Algebraic Effects in C.* MSR-TR-2017-23 (Thm 1). libmprompt README, https://github.com/koka-lang/libmprompt
- The Koka book, https://koka-lang.github.io/koka/doc/book.html (§3.4)
- Schuster, Brachthäuser, Ostermann. *Compiling Effect Handlers in Capability-Passing Style.* ICFP 2020. https://se.cs.uni-tuebingen.de/publications/schuster20capability.pdf (Thm 5.1, Cor 5.2, Thms 5.3–5.5; §4.3)
- Schuster, Brachthäuser, Ostermann. *Zero-cost Effect Handlers by Staging.* TR 2019. https://pl.cs.uni-tuebingen.de/publications/schuster19zero.pdf (Thm 5; §6)
- Schuster, Brachthäuser, Müller, Ostermann. *A Typed Continuation-Passing Translation for Lexical Effect Handlers.* PLDI 2022; TR https://se.informatik.uni-tuebingen.de/publications/schuster22typed.pdf (Thms 8, 10, Cor 11)
- Müller, Schuster, Brachthäuser, Ostermann. *Back to Direct Style: Typed and Tight.* OOPSLA 2023 (Thms 8, 9, 15, 17, Cor 20)
- Muhcu et al. ICFP 2025, https://se.cs.uni-tuebingen.de/publications/muhcu2025multiple.pdf; effekt-lang.org/evolution; Effekt sources (JS and CPS generators)
- Ma, Ge, Lee, Zhang. *Lexical Effect Handlers, Directly.* OOPSLA 2024. https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf (Thms 1, 2; §§5, 7.5)
- Ma, Ge, Jung, Zhang. *Zero-Overhead Lexical Effect Handlers.* OOPSLA 2025. https://cs.uwaterloo.ca/~yizhou/papers/zero-oopsla2025.pdf (Thm 1, Cor 1)
- Sivaramakrishnan et al. *Retrofitting Effect Handlers onto OCaml.* PLDI 2021. arXiv:2104.00250 (§§2.2, 3, 4.2, 5.2, 5.4, 6.3)
- Phipps-Costin et al. *Continuing WebAssembly with Effect Handlers.* OOPSLA 2023. arXiv:2308.08347v3 (Thms 3.1, 3.2; §§3, 5, 6)
- Legoupil, Pedersen, Birkedal, Lindley, Pichon-Pharabod. *Iris-WasmFX.* PLDI 2026. https://iris-project.org/pdfs/2026-pldi-iriswasmfx.pdf (Thms 3.1, 4.1, 4.2, 5.1, 5.2)
- Kobayashi, Kameyama. *Expressive Power of One-Shot Control Operators and Coroutines.* APLAS 2025. arXiv:2509.11901v1 (Thms 1–7, Cor 1)
- Rust: `compiler/rustc_mir_transform/src/coroutine/{mod,layout}.rs` (master, 2026-10-06, unpinned); error codes E0626, E0733; RFC 2033; RFC 2394
- LLVM Coroutines, https://llvm.org/docs/Coroutines.html; Smith, Nishanov, P0981R0 (HALO)
- Kotlin KEEP *coroutines*, https://github.com/Kotlin/KEEP/blob/master/proposals/coroutines.md
- Ante, github.com/jfecher/ante at `3e680ef3`: `src/mir/effects/{tail_resume_optimization,abort_handler_optimization,effect_lowering}.rs`

Abstract only: Rompf, Maier, Odersky, ICFP 2009 (selective CPS). Relayed: CerCo FOPARA 2013 (Matita); CompCert validated passes.

Local:
- `~/repos/borrow-core/Backend/README.md` (*Pipeline*, *Representation*, *Stack*, *Counts*, *Verification*)
- `docs/pipeline.md`
- `SPEC.md` §14 (*Higher-order functions*), §15 (*Self-reference*, *Lowering*), §18 (*Elaboration*, *Laws*), §19 (*Lowering*, *Open*)
- `corpus/counts.expected`, `corpus/kernel-counts.expected`, `corpus/capture-*-hand.bc`
- `Core/EffPrograms.lean` (`logOutside`, `nLogOutside`)
- `docs/effect-polymorphism.md` §0, §5.8, §10
- `docs/effects-state/BRIEF.md`, `04-decisions.md` L1–L6, `05a-open-questions-1-34.md` OQ-23
- `research/effects/ante-deep-dive.md` §4
- `~/repos/borrow-core-targets/experiments/Targets/Targets/A/Lowering.lean`, `Targets/Instance/ZeroCost.lean`, `Targets/Base/Rows.lean`, `RESTRUCTURE.md` §1.7, `AGREE.md`, `Targets/Status.lean`
- this notebook's sibling chapters and `survey.md` C1–C5
