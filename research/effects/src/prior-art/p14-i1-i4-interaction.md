# Prior art: P14 well-bracketing conservativity, I1 a suspension is a value, I4 answering effects are borrows

This chapter covers the literature for the three remaining interaction properties. It ends in one menu per property and a table of how the menus constrain each other and the five menus already written. It does not recommend an option.

- **P14, well-bracketing conservativity** ([chapter](../properties/conservativity.md); survey A7). Proofs and library reasoning that assume well-bracketed control still hold wherever a callback's operations preserve well-bracketing. Tier 2 must also say what it gives up, and for which operation classes.
- **P3 / I1, a suspension is a value** ([chapter](../properties/i1-suspension-value.md); survey A1, T2). A captured continuation is a value of the resource world, with a well-defined semantic type that accounts for the loans it holds. The question is whether it is second-class or a boxed first-class value, and what bounds it.
- **P6 / I4, answering effects are borrows** ([chapter](../properties/i4-answering-borrows.md); survey A5). A handler of a tail-resumptive effect lends a capability to its body for the body's extent, and an operation is a call on a reborrow of that capability. OQ-1 asks whether an answering handler is a tail-resumptive `[handle]`.

**Decisions that bound the menus** ([decided constraints](../decisions.md)):
- nothing breaks the borrow calculus: its guarantees, not BoLo's text;
- the core is linear, and discard is an explicit cancel;
- cancellation is what SPEC §19 builds;
- handlers are deep;
- multi-shot is ignored (decision 63) and appears only as context;
- errors are `raise`;
- divergence is codata;
- handling is erased at runtime;
- no function colouring;
- binary laws are optional unless safety needs them;
- row variables (decision 62) are an implementation choice, not a goal.

Defaults that bear on these menus, at the strength the user gave them: runners are not user-facing, and BoLo-as-runner as an internal architecture is "not yet decided"; interior mutability is open; threads are required eventually.

**Verification marks.**
- **[read]** means the statement was read in the primary full text for this chapter, by me or by a retrieval pass I ran, and the quote is copied from that text.
- **[relayed]** means it was taken from the survey, the Ante deep dive, or a sibling prior-art chapter, and was not re-read here.
- **[unverified]** means it could not be checked.
- **[local]** means it was read off this repository's Lean or documents.
- **[synthesis]** marks my reading, not a source's claim.

Theorem numbers are those of the version named in the sources list.

---

## 0. The menus at a glance

### 0.1 P14: well-bracketing conservativity (rows W.x)

A7 has three halves (survey §1.3):
- (i) a library proved against well-bracketed contexts stays sound when its callbacks' operations are restricted;
- (ii) a library can demand that restriction in its type;
- (iii) a continuation holding the library's frames is never dropped without unwinding, and never forgotten.

The literature adds a fourth risk: re-entry, where a library's private transition is observed partway through (DNB 2010; survey P2 S5). The options below are not exclusive. Most designs take several of them.

| # | option | statement shape | buys | main cost | literature | ours today |
|---|---|---|---|---|---|---|
| **W0** | **Tier 1 by construction: keep T1 and `↭` at every stop** | `WBCore`: every run's record list at a stop equals the list at entry | every Core proof stands verbatim; P14 is trivial | rejects every tier-2 program (AT02, AT04, AT12, AT17, `genSelf`) | TGB 2024 wbHoare-access-stack ("returned untouched") | **`wbCore` PROVED** (companion lemma, Core σ=[]) |
| **W1** | **Class-restricted embedding (survey T7)**: Core's relation embeds into W at types whose callbacks are abortive or answering | `ConservativeWB`: `A.AbortRows → vCE none … → ∀ i', M.Ext (ls, nil) i' ρ → M.val … i' …`; `EmbedsNil` at the nil index | library proofs at those types transfer to W unchanged, whatever tier 2 adds | at W, `Mono`, and a check against each OQ-8 clause set (`EmbedsNil`) | DNB 2010 §8 (exceptions keep the STS method); GITrees ESOP 2025 ("our extension is conservative"); Evidently (tail-resumptive operations run in place) | **PROVED AT σ=[]** (`conservativeWB_core`, `embedsNil_core`); open at W; in the device |
| **W2** | **Every-type embedding (A7 in full)** | `Conservative`: the same at every type | every Core-proved value is a W value, including one whose callbacks suspend across its lends | this is exactly where tier 2 gives something up; its status at resuming callback types is the open question | none: TGB §10 *conjectures* the handler case | **PROVED AT σ=[]** (`conservative_core`); beside done; open at W |
| **W3** | **Well-bracketing as a type-level bound (A7 (ii))**: a library demands that its callbacks' rows sit in a class | `RowCon.cls ≤ c` at the library's row variable, with W1 at that class | a library that relies on well-bracketing says so, and tier 2 costs it nothing | a class lattice that includes "answering" (today `RowClass` = abortive / resumeOnce / any); under capabilities, a grade on blocks (O2-g) | effect exclusion (Lutze et al. 2023, [relayed]); survey C6 | `RowClass`, `RowCon.cls` exist (`Targets/Base/Rows.lean`); no library-facing statement |
| **W4** | **A context-local / ghost-stack wp as the proof device** | define `clwpW`, or a ghost-stacked `wbwpW`, over W; Core's rules hold for it, and tier-1 code satisfies it | the bind and frame rules for code that captures nothing; private transitions as fresh-pushed ghost state | a second wp beside `ewpW`, which ONEW and BRIEF §10 forbid unless it is a definition over `ewpW` | Timany–Birkedal 2019 Def 4.1; TGB 2024 §9 (wbwp), Thm 3.1 | none; M1's re-lend has the same shape (synthesis) |
| **W5** | **The leak/abort half from linearity and §19 (A7 (iii))** | B4 (leak freedom) with P5's cancel: no `forget`; a dropped κ is cancelled and its finalisers run | `thread::scope`, `replace_with` and `Pin`'s drop guarantee keep their contracts | every κ must be consumed; finalisers are F.1-restricted | RFC 1066; scoped-task trilemma; RustBelt "give back all the lifetime tokens" | **built**: SPEC §19, `ewp_kappa_cancel`, `NoOwn`/`reclaim` (Core σ=[]) |
| **W6** | **The re-entry half from exclusivity** | under B6, a private transition's state is a `Mut` lend or an owned cell captured in κ, so no handler path reaches it while κ is suspended | DNB's private transitions survive one-shot re-entry without restricting the operation class | holds only while there is no shared interior mutability; must be checked in Lean, and has not been | survey P2 S5 ("an FnMut receiver captured in k already makes the borrow checker reject re-entry"); Hazel frame rule ("holds because our definition of ewp imposes an affine usage of continuations") | not stated; P10's X.6 enforces the clause half |

**What tier 2 gives up, by operation class** (§5.1 has the detail):

| class | Core's proofs | library reasoning (A7) | what tier 2 changes |
|---|---|---|---|
| answering (`fn`) | stand: an operation is `withswap`, a call (I4) | stands: the operation is a call | nothing |
| abortive (`raise`) | stand: `Row.Unwind`, frame lemmas at abortive tables | DNB: exceptions are "a 'well-bracketed' kind of control effect"; the method survives, some equivalences do not | nothing; §19's cancel is a forced unwind |
| once-resuming (`lin`/`aff` `ctl`) | 6.64 and 6.65 hold at a stop only by T1 and `↭` | control leaves the library's frame while its lends live; private transitions are at risk only through re-entry, which W6 addresses | T1 and `↭` at the stop (OQ-9: M1 re-lends, M2 carries) |
| `unr` (multi-shot) | ignored | DNB §5.1: "every time we pass control to the context may be the last!" | ignored (decision 63) |

### 0.2 I1: a suspension is a value (rows V.x)

| # | option | κ's type and bound | buys | main cost | literature | ours today |
|---|---|---|---|---|---|---|
| **V1** | **Second-class κ only** | κ is a block at the frame's lifetimes; never stored | P9 for κ is escape analysis; κ on the stack | **fails E9** (κ stored after its handler returned, in done) and `I1Prog`; no scheduler | System Ξ; System C's [Try] (`k :^C τ0 → τ`); Schuster 2020 ("resumptions as capabilities, which makes them second class") | not the kernel: κ is a thunk value |
| **V2** | **First-class κ as a linear object with two observations** (today) | `kTy`: `U((B ⊸ F_Σ R) & ⊤)` at `lin`, `U((B ⊸ F_Σ R) & F_Σ 1)` at `aff`; semantic type `KapRel` | E9, `storeCancel` and `at17` at tier 1; cancel is an observation of κ | no outlives rule at `U C`, so κ cannot be put under a box | Affect (`−⊸`, Fig. 7); Tang et al. (linear `r_i`); OCaml `continue`/`discontinue`; handled_effect (`@ unique`) | **`i1_core` PROVED** (Core σ=[]); E1′, E9 open at our instance |
| **V3** | **Boxed κ with a bound: a `[gen]` rule** (OQ-28 (a), L.2) | `[@c] U(Aff^c A B)`, `c` the meet of what κ borrows | schedulers and stored generators that hold external lends | a new rule; T14.4's coinduction | System C Example 10 (`box {p, schedule} { () ⇒ resume(true) }`) | ATTEMPTED (`lift-stage1`, `ewp_gen` L14.3), stopped |
| **V4** | **An outlives rule at `U C`** (OQ-28 (b), L.3) | `Δ ⊢ U C ⊐ @a` from what `C` captures; κ inherits it as a thunk | one rule for closures and κ; V3 derived | 6.60's induction at `U`, under the Kripke quantifier (T2, #173) | CC<:□ capture prediction ([relayed]); Rust coroutine witness types | `OutJ.core` has no `U C` rule (`thunk_not_outlives`) |
| **V5** | **κ as a heap object with a one-shot cell** | κ carries a location that resume or cancel flips or frees | at most once from safety, exactly once from the empty heap | a machine change (OQ-50 (b)); excluded by S4 as stated (AGREE Q9) | Hazel R6; Affect §3.1; WasmFX `ref.cont` with a trap; Lexa | excluded (= P8 menu 8.3) |
| **V6** | **κ's type closed over internal names (freeze as binder)** | κ's type mentions only external lifetimes; internal lifetimes, locations and instances are bound and instantiated at resume or placement | moving κ (AT17) and re-lending at resume (M1) by one argument | the lifetime half: no precedent for ordered names; `NotVDenNaturalArises` open | rustc `CoroutineWitness` ("higher ranked lifetimes bound by the witness itself"); Pitts–Stark ν ([relayed]) | `FreezeBinder` stated, open (= I2 menu T3) |
| **V7** | **κ's type records its witness or loan set** | κ's type carries the loans of its frames, not only their meet | `Send` derived from the witness (threads, survey C5); finer exclusivity counting | a loan-set type former; heavier types | rustc witness ("all locals live across suspend points", [relayed]); Oxide closure loan sets ([relayed]) | none |

### 0.3 I4: answering effects are borrows (rows B.x)

| # | option | statement shape | buys | main cost | literature | ours today |
|---|---|---|---|---|---|---|
| **B1** | **The borrow form is pinned, with no relation to `hnd`** | `I4a`: the borrow form `ansRun d s₀ body` of a typed answering body is typed by the borrow rules | answering effect safety = no use after a lifetime; X.1 (two `&mut` from one handler rejected) | two handler mechanisms stay unrelated (BRIEF §3 item 5) | Ξ (Thms 4–5); HandlersAsBorrows | **`i4a_tier1` PROVED AT A RESTRICTION** (tier 1, abortive rows) |
| **B2** | **One mechanism: an answering handler *is* a tail-resumptive `[handle]`** (OQ-1 (a)) | `I4Typing` (unary): a typed control form `ctlForm` has a typed borrow form; optionally `I4c` (binary): the two are contextually equivalent | one kernel mechanism; the lowering's "tail-resumptive → call" becomes a theorem, not an optimisation | `capPass`'s spine only; I4c is binary (optional) | Evidently §1, §6.2 (in-place rule, an optimisation); Koka `fun` ⤳ `ctl … resume(f())`; Schuster 2020 Thm 5.5 | `I4Typing`, `I4c` stated, OPEN |
| **B3** | **Two mechanisms under one signature: models and comodels** (OQ-1 (b), the sign-off's structure) | one `Sig`; `hnd` is a model (`ewp_handle` as initiality); a capability's co-operations `co_j : !U(S ⊗ A_j ⊸ F(S ⊗ B_j))` are a comodel on the carrier `S` | the signed-off architecture; both forms interpret one `opTable` | one `IsModel`/`IsComodel` pair over the kernel; no theorem relates them unless B2 is added | Plotkin–Power Def 3.1; Ahman–Bauer Def 1, Prop 3; Uustalu (talk abstract); Katsumata–Rivas–Uustalu §4.1 | `ImplTyped`'s `co` type is a linear-use co-operation (synthesis); no comodel statement |
| **B4** | **Answering is a borrow in the relation**: `hnd` at a tail-resumptive table opens a lifetime and lends its state | `ewp_handle` at answering tables follows from 6.65 (`wpG_M_frameX`); `handle_is_shift` at Core | I4 holds for `hnd` itself, with no translation; effect safety for answering operations from B7 | OQ-3 (c) at Core; `effHandle` opens none today | Müller et al. 2023 (a region per handler, [relayed]); HandlersAsBorrows `handle_is_shift` | `handle_is_shift` at PAPER only |
| **B5** | **Runner architecture: BoLo as the outermost runner, answering handlers as user runners** | answering handler = stateful runner with linear state; finalisation as Ahman–Bauer Thm 7 | finalisation exactly once and zero-cost answering, from one structure | a denotational layer; runners are not user-facing; BoLo-as-runner undecided | Ahman–Bauer ("a restricted form of handlers, which apply the continuation at most once in a tail call position"); Møgelberg–Staton Thm 4.3, Thm 8.1 | none |
| **B6** | **How the capability reaches the operation** (sub-axis, from the rows/capabilities menu) | (a) implicitly, by row and evidence (O1); (b) as an explicit second-class argument (O2); (c) as a `local`-moded argument | (a) no annotation burden; (b) and (c) lexical binding, so no accidental handling | (b) the H4 colouring test; (c) a mode axis | Evidently Thm 5 (evidence); Ξ; handled_effect README | decision 57 (capability arguments); O1 rows in Core |
| **B7** | **Capability mode** (sub-axis) | `Mut 'h S` (today), `Imm 'h S` (read-only), or `!` code (stateless) | `Imm`/`!` allow aliasing: System C's two blocks on one capability | three entries in `ImplTyped`; aliasing a `Mut` is refused (`twoBlocks_refused`) | System C ([relayed] via HandlersAsBorrows §5) | `Mut` only; `Imm`/`!` "not built" (HandlersAsBorrows §5 item 1) |

### 0.4 Cross-menu relations

"R" means the option requires the other one, "X" that it excludes it, and "F" that it favours it. Option names from the other menus:
- **[I2](i2-capture-resume.md):** M0–M3, T1–T4.
- **[P10/P9](p10-p9-exclusivity-lifetimes.md):** X.1–X.7, L.1–L.7.
- **[P8/P5](p8-p5-linearity-drop.md):** 8.1–8.6, 5.1–5.6, X.1–X.3 (written P5-X.x here, to avoid a clash), F.1–F.3.
- **[P2](p2-effect-safety.md):** R1–R6, S-a–S-g.
- **[Rows vs capabilities](rows-vs-capabilities.md):** O1–O4.

| option | requires | excludes | favours |
|---|---|---|---|
| W0 | M0 | M1, M2, M3 as tier 2; `Tier2Programs` in done | L.1; F.1 |
| W1 | `Mono` at W; OQ-8's clause set checked (`EmbedsNil`) | — | M1 (keeps `↭`'s printed meaning) over M2; R1/R3 with a class bound; B1/B2 (answering is in the class) |
| W2 | W at every type; at resuming callback types, a lifted 6.64/6.65 (`FramesW`) | — | M1 + T3; is hardest under M2 (`carryW` fails 6.50 and 6.27) |
| W3 | O1-ε-bounded (`RowCon.cls`), or O2-g | — | R3 (lacks/class-kinded variables); L.6 (a) at the bounded callback |
| W4 | a definition over `ewpW`, not a new relation | a parallel wp (BRIEF §10) | M1 (re-lend = push fresh, pop at stop) |
| W5 | 8.5 or 8.4 with lin/aff; 5.1; P5-X.1 ∩ P5-X.2 (§19 as built) | P5-X.3 (interceptable cancel) | F.1 |
| W6 | X.6 (clauses touch no body place); B6 exclusivity; no shared interior mutability | interior mutability as an unrestricted cell type | X.4 (ghost end: nothing held) |
| V1 | L.1; T2's second-class half | E9 and `I1Prog` in done | O2-pure (Ξ) |
| V2 | contShare/KapRel (8.4's wand) | V5 | 8.5; T2's first-class half |
| V3 | L.2; T14.4 | V4 as the primary rule (either/or) | M1 (bound over external lends only) |
| V4 | L.3; OQ-58 | V3 as primary | O1 and O2 alike; HandlersAsBorrows precondition 2 |
| V5 | 8.3; a relaxed S4 (AGREE Q9) | V2's machine | W5 for free (empty heap) |
| V6 | T3; M1 | — | T4 if V6's location half is not built |
| V7 | V3 or V4 with a loan-set bound | — | threads (survey C5); X.3 |
| B1 | X.1; L.4 (c) | — | R5 as a proof route for answering operations; P13 (call) |
| B2 | B1; `capPass` spine; S4's deep handler | — | W1 (answering = call is then a theorem); P13 |
| B3 | one `Sig` (BRIEF §5 item 1); P11's initiality | the split OQ-1 (c) | B5 |
| B4 | L.4 (a) or (c) at Core; 6.65 at answering tables | — | R5 (S-d); X.1 at `hnd` |
| B5 | B3 | — | 5.2 (Ahman–Bauer Thm 7); P13 |
| B6 (a) | O1 | — | R1–R4 |
| B6 (b) | O2; L.1 | — | R5 |
| B7 `Imm`/`!` | 6.64 for `Imm` lends | — | O2-C-style aliasing (System C) |

**Three couplings that cut across all three menus** [synthesis]:
1. **E9 forces a first-class κ (V2–V7, not V1).** At tier 1 that is compatible with W0, because T1 and `↭` constrain lends, not control. A κ stored after its handler returned holds no internal lend at tier 1 (`i1_core` at σ=[]). So **our well-bracketing condition is lend-bracketing, not TGB's control-bracketing.** Control-bracketing is lost as soon as E9 is in done, and every Core proof survives that loss, because no Core proof assumed it. P14's real content is the lend half.
2. **Answering operations are inside the well-bracketed class by construction.** Under decision 57 they are capability calls (`withswap`), not row entries. So `ConservativeWB`'s guard `AbortRows` (every effect layer abortive) is already survey T7's `{fn, abort}` class: answering operations reach the callback as `Mut 'h S` arguments, which `AbortRows` admits. B1/B2 is what makes that reading sound, and W1 inherits it.
3. **I1's choice of bound decides how much tier 2 can store, and P14's W3 decides who may refuse it.** V3/V4 let κ carry external lends. W3 lets a library say "my callbacks never suspend", which is how `thread::scope`-style APIs protect a lend that must not be carried.

---

## 1. Canonical statements

### 1.1 P14: well-bracketing and conservativity

**Dreyer, Neis, Birkedal, ICFP 2010** [read]
- **Definition.** It is informal; there is no numbered definition. §5: "In the absence of call/cc, however, computations are 'well-bracketed'. Here, this means that whenever x is set to 0, it will eventually be set to 1—no matter what the callback function does." §1: "the absence of control operators can be modeled by restricting game strategies to be well-bracketed."
- **What survives, and under what.** Thm 2 (Fundamental Property), Thm 3 ("≾log ⊆ ≾ctx") and Thm 4 (Completeness) are stated for the whole family. The reasoning principle that depends on well-bracketing is: "private transitions and inconsistent states—which are only sound in the absence of call/cc" (§1).
- **Exceptions, §8:** "raising an exception causes a 'well-bracketed' kind of control effect, in the sense that it passes control to the exception handler that was most recently pushed onto the control stack. Thus, the presence of exceptions does not per se restrict our STS model". But the equivalences change: "in the presence of exceptions, it is not hard to find program contexts that distinguish the higher-order functions in those examples", except for callback-with-lock.
- **What is lost under call/cc, §5.1:** "every time we pass control to the context may be the last! Therefore, the requirement that the extensional behavior of a term must appear like a public transition would essentially imply that every internal transition must be public as well."
- **Open:** "We leave consideration of other control effects, such as delimited continuations, to future work." (§8)

**Timany & Birkedal, ICFP 2019** [read]
- **Definition 4.1:** "clwp e Φ ≜ ∀K, Ψ. (∀v. Φ(v) −∗ wp K[v] Ψ) −∗ wp K[e] Ψ". The paper's gloss: "clwp e Φ holds if the bind rule holds for e, which intuitively means that e behaves context-locally."
- **What it recovers:** the bind rule; "the 'standard' rules for the basic language constructs (excluding call/cc and throw, of course) can also be derived for context-local weakest preconditions, as shown in Figure 5"; and the bridge "clwp e Φ implies wp e Φ".
- **What is lost:** "there are no context-local reasoning rules for call/cc and throw, we have to unfold the definition".

**Timany, Guéneau, Birkedal, POPL 2024** [read]
- **Definition (abstract):** "A program is said to be well-bracketed if every called function must return before its caller can resume execution."
- **§9:** "wbwp e ⟦Φ⟧^O ≜ ∀S. AllStacksExcept(S, O) −∗ wp e {x. ∃S′. S ⊆ S′ ∗ AllStacksExcept(S′, O) ∗ Φ(x)}". The postcondition requires "that the map of stacks has only grown but not changed in any other way".
- **§3:** "The well-bracketed program logic satisfies all the rules satisfied by the ordinary Iris program logic for HeapLang, except the fork rule". Also Hoare-wbHoare: "if one is able to verify a triple without leveraging ghost stacks, then the same triple should also hold in the well-bracketed program logic".
- **Theorem 3.1 (Adequacy):** "⊢ |⇛ SI(σ) ∗ ⟦True⟧ e ⟦x. ⌈φ(x)⌉⟧ ⟹ Safe_φ(σ, e)".
- **§10, a conjecture:** "We conjecture that such logics can serve as a basis for a well-bracketed program logic that can reason about well-bracketedness in the presence of innocuous uses of control effects."

**Stepanenko, Nardino, Frumin, Timany, Birkedal, ESOP 2025** [read]
- **Abstract:** "our extension is conservative: the reasoning principles (and the Coq implementation) for context-independent effects remain the same." §3.2: "we recover previous case studies … with minimal modifications."
- **What is lost:** "In the presence of context-dependent effects, wp-hom is not sound!" It is replaced by Lemma 5 (Limited bind rule): "If E(P)(α, e) and K(P)(κ, K), then O(κ α, K[e])."
- **Numbering.** The ESOP version has only "Definition 1 (Homomorphism)". The `clwp` definition is Definition 6.1 of the arXiv extension (2512.11577). The I2 chapter's "Definition 2" is not in the ESOP text.

**blaze: de Vilhena, van Collem, Wright, Krebbers, POPL 2026** [read]
- §4.3: "Taking m = ms yields Rule monotonicity, while taking m = os eliminates the persistently modality, thereby allowing ephemeral resources to be used".
- Theorem 4.1: "If ⊢ e_l ≾ e_r ⟨⊥⟩ {True}, then either e_l diverges or both e_l and e_r terminate."
- The text never uses "bracket". Its refinements are against concurrent implementations, not well-bracketed ones.

**Survey T7** [relayed] states the target: "for every library L proved sound against well-bracketed contexts: L remains sound in every context whose operations, as observable from L's callbacks, are in {fn, abort}". **No source read for this chapter proves a theorem of that shape for handlers.** The retrieval pass for P14 searched for one and found none. The closest results are DNB's exceptions paragraph (the method survives) and GITrees' conservativity (old context-independent results survive).

**Rust, the leak half** [read]
- RFC 1066: "It has never been a guarantee of Rust that destructors for a type will run, and this aspect was overlooked with the `thread::scoped` API which requires that its destructor be run!"
- without.boats, *The Scoped Task Trilemma*: "Any sound API can only provide at most two of the following three desirable properties: … Concurrency … Parallelizability … Borrowing".
- RustBelt §5.1: "In our proofs, we will always be forced to give back all the lifetime tokens that we obtained; this makes sure that we properly close all borrows again." §3: "ϝ has to be still alive when the continuation is invoked."

### 1.2 I1: continuations as values

**System C (OOPSLA 2022, TR)** [read]
- [Try], Fig. 2, layout reconstructed: `Γ, xi : τi, k :^C τ0 → τ ⊢ s2 : τ | C`. §4.3: "the continuation is marked as transparent and annotated with the capability set C … the continuation closes over both the handled statement as well as the handler statement".
- [BoxIntro] `Γ ⊢ b : σ | C` gives `Γ ⊢ box b : σ at C`. [BoxElim] allows `unbox` "only when the annotated capability set is compatible with the requirements in the current context C".
- Example 10 (§5.2) stores continuations: `q = enqueue(q, box {p, schedule} { () ⇒ resume(true) })`. The text says "In order to be able to store a second-class continuation in a Queue, we need to explicitly box it. Boxing reifies the capability set of the continuation into the type".
- The system is multi-shot, and soundness is syntactic. No semantic model of the continuation type is given.

**System Ξ / Effekt (OOPSLA 2020, TR)** [read]: "we separate functions from values and treat all functions as second-class." Schuster et al. (ICFP 2020) [read]: "We model resumptions as capabilities, which makes them second class."

**Affect (POPL 2025)** [read]
- §2.1: "Affect gives continuations the affine function type −⊸ instead of the unrestricted function type −→".
- Semantic model, Fig. 7: `τ −⊸^ρ κ := λ v. ∀ w. τ w −∗ ewp v w ρ {κ}`. The wand is not persistent.
- One-shot is static, backed by a stuck state: "a location ℓ is associated with continuation values cont ℓ N" (§3.1).
- Storing a continuation: "The load operation (!e) is limited to unrestricted types … otherwise one can put a continuation in a reference, load it multiple times" (§2.2).

**Hazel (POPL 2021)** [read]: Try-With-Shallow, Fig. 7: "the absence of a persistence modality □ in front of ewp E (k w) ⟨Ψ⟩{Φ} means that this assumption about k can be exploited at most once". R6: "ℓ is updated with false, so another attempt to apply this continuation will be stuck. This is the one-shot check."

**Tang, Hillerström, Lindley, Morris (POPL 2024)** [read]
- T-Handler: "when Yi = ◦, the continuation of ℓi may use some linear resources. Making ri linear guarantees that they are used exactly once."
- Thm 3.4(2): "Unlimited continuations are unlimited: if Δ; Γ ⊢ E[(do ℓ V)^E] : C … then there exists Δ ⊢ Γ = Γ1 + Γ2 such that Δ ⊢ Γ1 : • and Δ; Γ1, y : B ⊢ E[(return y)^E] : C."

**Timany & Birkedal 2019** [read]: the continuation type is interpreted through the evaluation-context relation, Fig. 4: "⟦cont(τ)⟧Δ(v, v′) ≜ ∃K, K′. v = cont(K) ∧ v′ = cont(K′) ∧ K⟦τ⟧Δ(K, K′)", with "K⟦τ⟧Δ(K, K′) ≜ ∀v, v′. ⟦τ⟧Δ(v, v′) ⇒ O(K[v], K′[v′])". The language is multi-shot, and the interpretation is persistent.

**WasmFX (OOPSLA 2023)** [read]
- `C ⊢ resume ft h* : t1* (ref cont ft) → t2*`.
- One-shot is dynamic: "any attempt to consume a continuation that is already dead causes a trap." "Correct code is expected to consume all continuations linearly".

**OxCaml `handled_effect`** [read]
- `val continue : ('a, 'b, 'es) Continuation.t @ unique -> 'a @ once unique -> 'es Handler.List.t @ local -> 'b @ once unique`.
- "Exception raised when a continuation is continued or discontinued more than once. Only achievable with [Obj.magic_unique] or similar escape hatches."

**rustc** [read]
- `CoroutineWitness`: "Unlike upvars, the witness can reference lifetimes from inside of the coroutine itself. To deal with them in the type of the coroutine, we convert them to higher ranked lifetimes bound by the witness itself … `for<'a> [Vec<i32>, &'a Vec<i32>]`".
- E0626: "At present, it is not permitted to have a yield in a movable coroutine that occurs while a borrow is still in scope."

**Muhcu et al. (ICFP 2025)** [read]: "multiple resumptions require stack copying, which invalidates any pointers to this stack. We introduce prompts with stable addresses". **Lexa (OOPSLA 2024 TR)** [read]: "We enforce dynamically that the resumption is resumed at most once".

### 1.3 I4: answering handlers as calls, capabilities, comodels

**Evidently (ICFP 2020)** [read]
- §1, the condition: "their operation clauses have the form op → λx.λk. k e with k ∉ fv(e)".
- The rule: "perform op (m, h) v ⟶ f v (λx. x) (op_tail → f) ∈ h. This is an important optimization that enables truly efficient effect operations at a cost similar to a virtual method call".
- Thm 5 (Evidence Correspondence): the evidence "corresponds exactly to dynamic execution context such that w.l = (m, h)".
- §6.4: "all effects that are statically guaranteed to be tail resumptive (called linear effects)".
- **There is no numbered theorem that in-place execution equals the general semantics.** It is an optimisation argued from Thm 5.

**Koka book** [read]
- §3.4.3 gives the desugaring `fun op(<args>){<body>}` ⤳ `ctl op(<args>){ val f = fn(){<body>}; resume(f()) }`, and: "when the operation is a tail-resumptive fun, it calls it directly as a regular function".
- §3.4.12: "Use linear effect to declare effects whose operations are always tail-resumptive and use only linear effects themselves".

**Ξ (TR)** [read]
- §1.4: "Explicit capability passing is essential to establish a lexical connection between an effect handler and the operations it handles."
- Thms 4–5: "programs are never stuck on an undelimited label".
- Thm 6: "Translation preserves well-typedness". The TR prints Theorems 4/5/6 but cites them in prose as 4.3, 4.4 and 5.1. The ACM numbering is [unverified].

**Schuster et al. (ICFP 2020)** [read]
- Cor 5.2 (effect safety).
- Thm 5.5 (Full elimination): "capability passing is performed statically, handlers are fully inlined, local continuations are fully inlined".

**Runners: Ahman & Bauer (ESOP 2020)** [read]
- §1: "runners are simply a restricted form of handlers, which apply the continuation at most once in a tail call position", and "Runners guarantee linear usage of resources not through a linear or uniqueness type system … but rather by a design based on the linear state-passing technique studied by Møgelberg and Staton".
- Def 1: "A runner R for a signature Σ is given by a carrier set |R| together with, for each op ∈ Σ, a co-operation op_R : A_op → (|R| ⇒ B_op × |R|)."
- §2: "Runners are equivalent to the concept of comodels".
- Prop 3: "the monad morphisms Tree_Σ(−) → T are in one-to-one correspondence with T-runners for Σ."
- Thm 7 (Finalisation): "A well-typed run factors through finalisation".

**Comodels: Plotkin & Power (MFPS 2008)** [read]
- Def 3.1: "A comodel of a countable Lawvere theory L in a category C with countable coproducts is a countable coproduct preserving functor from L^op to C."
- The cooperations of global state: "a_Y : (Loc × V) × Y → Y, d_Y : Loc × Y → V × Y".

**Katsumata, Rivas, Uustalu (LICS 2020)** [read]: "runners of T are essentially the same as objects Y endowed with a monad map ϑ : T → St_Y". **Uustalu (MFPS 2015)** [read, talk abstract only; paper unverified]: "to be a stateful runner … is the same as to be a comodel of the theory".

**Møgelberg & Staton, LMCS 2014** [read]
- Abstract: "every monad is a linear state monad … There is a bijective correspondence between generic effects in the source language and state access operations in the enriched call-by-value calculus."
- Thm 4.3 (Full completeness), (2): "If Γ ⊢p M, N : σ and Γ^S | s : S ⊢ M^S_s ≡ N^S_s : !σ^S ⊗ S then Γ ⊢p M ≡ N : σ".
- §8: "it is necessary and sufficient to supply the chosen state type S with the structure of a comodel". §8.1: "state is linear and cannot be discarded or duplicated".
- The paper says nothing about handlers.

**OxCaml `handled_effect`** [read]: "Each effect handler can be represented as a `local` argument, which is needed to perform its operations. Functions accepting `local` functions are then effect-polymorphic".

**Ante** [read]
- "If the handler does not have any code after resume (i.e. it is tail-resumptive) it can actually be optimized into a normal function call."
- "it is possible to specify when declaring the effect that all handlers for it must be tail-resumptive."
- The phrase "every perform of the same effect borrows from the same handler" is not on the current tour page; the deep dive relays it from the 2024 post ([relayed]).

**Expressiveness** [read]
- Forster, Kammar, Lindley, Pretnar, Thm 6.10: "The following macro translations do not exist: • typed eff→typed mon … • typed eff→typed del". The theorem is about general handlers; tail-resumptive ones are not singled out.
- Biernacki et al. POPL 2020, Thm 5, relates lexical and generative semantics, not tail-resumption.
- **No source read states, as a theorem, that a tail-resumptive deep handler is equivalent to a capability, dynamic-binding or reader-with-state form.**

---

## 2. How prior systems realise and prove each

| system | P14: what survives control | I1: κ's type and bound | I4: answering ops | mechanised |
|---|---|---|---|---|
| DNB 2010 | STS private transitions without call/cc; exceptions keep the method | — | — | paper |
| Timany–Birkedal 2019 | clwp: bind and standard rules for context-local code | `cont(τ)` via K⟦τ⟧, persistent | — | Coq/Iris |
| TGB 2024 | all Iris rules except fork, via ghost stacks | — | conjecture only | Coq/Iris |
| GITrees ESOP 2025 | old context-independent results; limited bind | — | — | Coq |
| Hazel | frame rule, from the affine wand | protocol wand, one-shot flag | — | Coq/Iris |
| Affect | EWP-Frame under `ρ mono` | `−⊸`, non-persistent wand; one-shot cell | — | Coq/Iris |
| System Ξ / C | — | second-class `k`; `box … at C` | capabilities, lexical | Coq (C) |
| Evidently / Koka | — | — | `fun` = in-place call (optimisation) | paper; Koka |
| Ahman–Bauer | finalisation (Thm 7) | runners: κ used once, in tail position | runners = comodels | paper; Coop |
| Møgelberg–Staton | — | — | linear-use state ≅ comodel (Thms 4.3, 8.1) | paper |
| WasmFX / Lexa | — | `ref cont`, dynamic one-shot | — | spec; Racket |
| rustc | E0626 + Pin; leak not prevented | witness, HRTB over internal lifetimes | — | none |
| OxCaml | — | `unique` κ, `once` body | `local` handler capability | modes (Iris for DRF) |
| **ours** | `wbCore`, `conservative*_core` (Core σ=[]) | `kTy`, `KapRel`, `i1_core` (Core σ=[]) | `i4a_tier1` (Core σ=[], abortive); `translate_typed`, `effect_safety` (PAPER) | Lean |

---

## 3. Pitfalls

1. **Conflating control-bracketing with lend-bracketing.** TGB's definition is about control. Our T1 and `↭` are about lends at a stop. E9, which is in done, breaks control-bracketing at tier 1 already, and no Core proof notices (§0.4 coupling 1). Reading P14 as TGB's property would make done self-contradictory. Reading it as lend-bracketing does not. [synthesis]
2. **"Conservative" means different things.**
   - GITrees: old *context-independent* proofs survive.
   - DNB: the *method* survives exceptions, but equivalences do not.
   - Our `Conservative`: Core's *relation* embeds into W.
   None of these is survey T7's library statement. Our W1/W2 are relation-level, so they cover library proofs only when those proofs are Core-relation proofs. A library proved in some other logic, such as a RustBelt-style `unsafe` proof, is not covered.
3. **A trivial embedding at σ=[].** `conservative_core` and `conservativeWB_core` are proved by `vC_local` at `coreB`, where `M.val` is Core's relation and `Ext` is Core's [local]. So at σ=[] they say "Core's relation is stable along Core's `Ext`". Their content is entirely at W. The status column "PROVED AT σ=[]" must not be read as evidence about tier 2.
4. **The leak half is cheap only because the core is linear.** Affect's affine continuations "need no `discontinue`" ([relayed], survey P2) and are memory-safe, but not library-safe (S1–S3). Our W5 holds because κ owes `cancelOwed`. An `unr` κ may be forgotten, but it holds nothing (`contShare` at `unr` is `ρ = PMap.empty`).
5. **Re-entry is the half that linearity does not remove.** DNB's private transitions are broken by re-entry before resume, which is a one-shot phenomenon (survey P2 S5). Our W6 argument depends on there being no aliased mutable cell. If interior mutability is added (open), W6 needs a W3-style bound on that type.
6. **"Tail-resumptive = call" is an optimisation in the literature, not a theorem.** Evidently and Koka implement it, and neither proves an equivalence (§1.3). Using it as a law in our kernel (B2's `I4c`) would be ours. It is binary, so it is optional unless safety needs it. The unary `I4Typing` is the safety-relevant half.
7. **One-shot by a dynamic check is a machine change.** WasmFX traps, Hazel and Lexa get stuck, OCaml raises. The typed versions (Affect, handled_effect, Tang) still need a semantic or dynamic backstop. Ours is the relation's non-persistent `contShare`, with no cell (the P8 menu's 8.4). V5 would change B's machine.
8. **Second-class κ colours if higher-order code cannot abstract over it.** Ante abandoned second-class references for this reason ([relayed]). V1 alone also fails E9.
9. **Aliased capabilities.** System C allows two blocks on one stateful capability. B1 with `Mut` refuses it (`twoBlocks_refused`). SecondClass P5 recovers the program by putting the state behind control. B7's `Imm` and `!` modes are the route for read-only and stateless handlers.
10. **Runners exclude control.** Ahman–Bauer's restriction ("at most once in a tail call position") is exactly the answering class. A runner architecture (B5) covers I4 and P5's finalisation, but not `ctl` operations, which stay with `hnd`.

---

## 4. With borrows and lifetimes: what the literature has, and where we would be new

- **Well-bracketing with lifetimes.** RustBelt's call rule returns every lifetime token at return ("give back all the lifetime tokens that we obtained"). That is lend-bracketing at calls, the same shape as our `↭`. No published work states what happens to it under handlers. Survey A7's borrow-interaction paragraph ([relayed]) is synthesis. **New:** a conservativity statement, at the relation level, for a lifetime calculus extended with one-shot handlers (W1/W2 at W).
- **Continuation values holding loans.** rustc gives the coroutine type a witness with higher-ranked internal lifetimes, which is the closest *typed* precedent for V6 and V7, but it has no soundness proof. System C bounds by capability sets, Affect by affinity, and Hazel by protocol. **New:** a semantic type (`KapRel` at W) for a κ that holds lifetime-indexed borrows, and an outlives rule at `U C` covering κ (V4).
- **Answering handlers as borrows.** Ξ and System C treat capabilities as second-class labels. OxCaml uses `local` modes. Ante has an unenforced rule ([relayed]). Runners and Møgelberg–Staton give the linear-state comodel reading, with no borrows. **New:** effect safety as "no use of a borrow after its lifetime" (HandlersAsBorrows, PAPER), and its kernel form (`I4a`, `I4Typing`).
- **The comodel/borrow link** [synthesis]. `ImplTyped`'s co-operation type `!U(S ⊗ A_j ⊸ F(S ⊗ B_j))` is Møgelberg–Staton's linear-use state access operation and Ahman–Bauer's co-operation with the carrier `S` threaded linearly. `withswap` on `Mut 'h S` is what makes "linear" a borrow rather than a type discipline on `S`. Nothing found states this correspondence.

---

## 5. The menus in detail

Each entry gives **shape**, **cost**, **buys**, **interacts** and **evidence**.

### 5.1 P14

**W0. Tier 1 by construction.**
- *Shape:* `WBCore` (`Targets/B/Conservativity.lean`): `wpG ls e Q ρ → wpG ls e (fun ls' t ρ' => Q ls' t ρ' ∧ ∀ x, x ∈ ls' ↔ x ∈ ls) ρ`. This is conjunct 40 of `wpG`, read back out.
- *Cost:* the tier-2 programs.
- *Buys:* every printed proof verbatim. TGB's wbHoare-access-stack is literally this.
- *Interacts:* M0; L.1; F.1. E9 is compatible (coupling 1).
- *Evidence:* `wbCore` (Core σ=[]); `Restricted/RunEnd.lean` shows `↭` alone stops a Mut lend spanning a stop.

**W1. Class-restricted embedding.**
- *Shape:* `ConservativeWB M` and `EmbedsNil M`, as in the table. `AbortRows` is hereditary: every `CTy.eff` layer must be abortive (`B.isZero && q != .lin`).
- *Cost:* at W, `Mono` (review [18]). `EmbedsNil` has not been checked against OQ-8's clause sets. Under any clause set with a future-world quantifier in a value clause, `EmbedsNil` at a thunk type already asks for `ConservativeWB`'s content (RESTRUCTURE §3.6).
- *Buys:* T7's shape. By coupling 2, answering operations are inside the class without any extension, because they are `Mut` arguments, not row layers.
- *Interacts:*
  - It is cheapest under M1, where `Upd` is Core's `↭` at every index (`updRefl_of_core` … `updLendBack_of_core`).
  - Under M2, `carryW` fails 6.50 and 6.27, so the embedding's target relation has different run-end laws.
  - With R1, the class is not in the type unless O1-ε-bounded is taken (W3).
- *Literature:* DNB §8 (exceptions); GITrees (conservative over context-independent effects).
- *Evidence:* `conservativeWB_core`, `embedsNil_core` (Core σ=[], trivial there: pitfall 3).

**W2. Every-type embedding.**
- *Shape:* `Conservative M`.
- *Cost:* at types whose callbacks may suspend at a once-resuming operation, a Core-valid library value was proved with the callback keeping T1 and `↭`. At W the callback may hold a lend across its stop. The embedding then needs the library's own frames (6.64, 6.65) to hold across a callback's stop. That is `FramesW` at resuming tables (I2 menu, M1/M2), open. I have not derived `Conservative` at W and have not verified that any obstruction is real.
- *Buys:* A7 (i) with no class restriction.
- *Interacts:*
  - Under M1 the library's lends are internal to the callback's *caller*, not the callback. So the question is whether a stop inside the callback crosses the library's frame. GhostEnd's `callee_spans_yields` and `closure_spans_yield` (Core σ=[]) are instances where it does, and is handled by re-lend.
  - That suggests W2 at W reduces to GFPA / `RelendOfTyped` (open). This is a reading; no Lean check was run.
- *Literature:* TGB §10's conjecture is the nearest.
- *Evidence:* `conservative_core` (trivial at σ=[]).

**W3. Well-bracketing as a type-level bound.**
- *Shape:*
  - add `answering` below `abortive ∪ answering` in `RowClass`, or keep answering outside rows as decision 57 has it;
  - a library's row variable carries `RowCon.cls`;
  - W1 is stated at that class.
- *Cost:* the class lattice; inference of the bound. Under O2, a control-class grade on blocks (O2-g).
- *Buys:* A7 (ii). A `scope`-like API that must not have its lend carried can refuse once-resuming callbacks. This is the only W-option that gives a library a choice.
- *Interacts:* R3 (class-kinded variables); O1-ε-bounded; L.6 (a). Against no colouring: a bound is a constraint on a row variable, not a second function, so `map` is still written once.
- *Literature:* survey C6 and the effect-exclusion line ([relayed]); clippy's `await_holding_*` lints as the informal analogue.
- *Evidence:* `RowClass`, `RowCon` (`Targets/Base/Rows.lean`).

**W4. A context-local or ghost-stack wp as the proof device.**
- *Shape:* `clwpW e Φ ≜ ∀K Ψ. (∀v. Φ v −∗ ewpW K[v] Ψ) −∗ ewpW K[e] Ψ`, a definition over `ewpW`. Core's rules are then lemmas about it.
- *Cost:* it must be a definition, not a relation family (BRIEF §8 pattern 4, §10).
- *Buys:* the bind rule for callback-free fragments at resuming tables. TGB's ghost stacks give private transitions inside it.
- *Interacts:* M1 (ghost-end) is TGB's "push fresh, pop" (I2 menu §1.3). W4 is the logic-level statement of what M1 does at the relation level.
- *Literature:* Timany–Birkedal Def 4.1; TGB §9; GITrees' arXiv Def 6.1.
- *Evidence:* none.

**W5. Leak and abort from linearity and §19.**
- *Shape:* B4 with P5's S5 `NoIntercept`.
- *Cost:* explicit cancels; finaliser rows F.1.
- *Buys:* survey S1–S3 (`thread::scope`, `replace_with`, `Pin`'s drop guarantee) for every operation class.
- *Interacts:* 8.4/8.5; 5.1; P5-X.1 ∩ P5-X.2.
- *Evidence:* `ewp_kappa_cancel`, `Core/EffCancel.lean`, `NoOwn`/`reclaim` (Core σ=[]).

**W6. Re-entry from exclusivity.**
- *Shape:* for any configuration W reaches, a cell lent `Mut` to a suspended frame is reachable by no handler clause and no other κ. This is P10's `Exclusive` at W with X.6.
- *Cost:* the statement is P10's. The only new obligation is that it covers private transitions, which needs no shared interior mutability.
- *Buys:* A7's re-entry half with no operation-class restriction.
- *Interacts:* X.6; X.4; interior mutability (open; an opaque-handle library type would need W3).
- *Literature:* the survey's restoring condition for S5; Hazel's frame rule.
- *Evidence:* none stated as P14. `exclusive_core` (Core σ=[], nothing held).

### 5.2 I1

**V1. Second-class κ only.**
- *Shape:* κ is a block bound by `[handle]`, used only inside the clause.
- *Cost:* E9 and `I1Prog` are in done, so V1 alone fails done. It survives only as a mode beside V2–V4 (T2: "second-class unless boxed").
- *Buys:* stack-allocated κ; P9 for κ by escape; no outlives rule needed.
- *Interacts:* L.1; O2-pure; H4.
- *Evidence:* SecondClass `handleAt_compatC` (Core σ=[]).

**V2. First-class linear object (today).**
- *Shape:* `kTy` and `KapRel`. `KapRel` gives resume at every answer in `PB` and cancel at `F_Σ 1`, at every `Ext` extension, and is empty at `unr`. Device `I1 M`: the share closed by its handler is a value of `kTy`.
- *Cost:* no bound, so a κ holding a lend cannot be boxed. Storing κ in a cell (`at17`, `storeCancel`) works at tier 1 only because κ holds no internal lend.
- *Buys:* E9; cancel as an observation (matches §19); `ewp_kappa_resume`/`ewp_kappa_cancel` as the elimination lemmas.
- *Interacts:* 8.4's wand; T3/M1 for κ holding re-lent cells.
- *Literature:* Affect's `−⊸` interpretation is the same shape (a non-persistent wand into `ewp`). Ours adds the cancel conjunct, which Affect's affine `−⊸` does not need.
- *Evidence:* `i1_core` (Core σ=[]); `i1Prog_of_combined`.

**V3. A `[gen]` rule.**
- *Shape:* κ at `[@c] U(Aff^c A B)` (SPEC §22's affine closure, `Core/Aff.lean`).
- *Cost:* T14.4/T14.6 and the rule.
- *Buys:* System C Example 10 in our terms; generators stored in data.
- *Interacts:* L.2; AT07 must stay rejected; under M1, `c` ranges over external lifetimes only.
- *Evidence:* `ewp_gen` (`lift-stage1`, Core σ=[]); `box_lolli_outlives_iff` (PAPER).

**V4. Outlives at `U C`.**
- *Shape:* L.3, with κ an instance because `kTy` is a thunk.
- *Cost:* 6.60's `U` case at every extension (OQ-58).
- *Buys:* V3 derived; one rule for closures and κ.
- *Interacts:* it is either/or with V3, and `LifetimeSound` then fires on κ (P9 menu §6).
- *Evidence:* `thunk_not_outlives`, `lolli_not_outlives`.

**V5. One-shot cell.** This is the P8 menu's 8.3, listed for completeness. It is excluded by S4 as stated (AGREE Q9).

**V6. Freeze as binder.**
- *Shape:* κ's semantic type is invariant under location bijections and forward lifetime instantiation (`FreezeBinder`).
- *Cost:* T3's costs; `NotVDenNaturalArises`.
- *Buys:* AT17 and M1's re-lend as one argument.
- *Literature:* rustc's witness binds internal lifetimes as higher-ranked, `for<'a>`. That is the typed counterpart of the lifetime half, as a universal at the type, with no soundness proof [synthesis].
- *Evidence:* `Targets/I/Binder.lean` (stated, open).

**V7. Witness or loan-set types.**
- *Shape:* κ's type lists the loans its frames hold, as Oxide closures carry a frame ([relayed]).
- *Cost:* a new former; type size.
- *Buys:* `Send` for κ from its witness (threads); exclusivity counted per loan (X.3).
- *Interacts:* threads are required eventually, so this is the option to keep open if V4's meet is too coarse to decide thread-safety.
- *Evidence:* none.

### 5.3 I4

**B1. The borrow form, pinned.**
- *Shape:* `I4a J Adm c` (`Targets/I/Interface.lean`).
- *Cost:* paid at PAPER. At Core it is proved at abortive rows only. AGREE notes `ImplTyped` is a dead hypothesis in `I4a`, and the non-vacuity witness exercises no operation.
- *Buys:* effect safety for answering effects from B7 (`effect_safety`, PAPER); AT05 rejected by `Mut` (X.1); a capability first-class within `'h` (HandlersAsBorrows (c)).
- *Interacts:* X.1; L.4 (c); R5 as a proof route; P13's "answering → call" with no handler at run time.
- *Evidence:* `i4a_tier1` (Core σ=[], abortive); `translate_typed`, `effect_safety`, `effect_safety_open`, `handle_is_shift`, `capability_not_outlives`, `twoBlocks_refused` (PAPER).

**B2. One mechanism (OQ-1 (a)).**
- *Shape:* `I4Typing` (unary) over `capPass`, `ctlForm`, `ctlClause` and `ansRun` (`Targets/Base/Programs.lean`). `ctlClause co = λ(a, κ). λs. let (s', b) = co(s, a) in κ.resume b to f. f s'` is the state-passing deep handler (decision 59). `I4c` is binary.
- *Cost:* the typing translation on `capPass`'s spine. `I4c` needs a binary relation, which is optional.
- *Buys:* OQ-1 settled as one mechanism, so `withswap` is a compiled form of `[handle]`. The lowering's direct call is justified by the kernel's own semantics, which Evidently and Koka do not prove.
- *Interacts:* with B3, the comodel is then a derived view. With W1 the class argument becomes a theorem. Decision 55 ("`fn` is answering, `ctl` control. An effect has one kind of operation") fixes the class per effect, so `capPass` can be keyed by declaration.
- *Literature:* Koka's printed desugaring of `fun` to `ctl … resume(f())` is exactly `ctlForm`'s direction. Evidently Thm 5 is the dynamic counterpart of `capPass`'s static one.
- *Evidence:* `handle_fold` (`Core/Handlers.lean`, run facts), `ewp_handle` (Core σ=[]), unrelated.

**B3. Models and comodels of one `Sig` (OQ-1 (b)).**
- *Shape:* `IsModel` for `hnd` clauses (`ewp_handle` as initiality) and `IsComodel` for capability co-operations over one `opTable`. The co-operation type is `ImplTyped`'s.
- *Cost:* the two structure lemmas.
- *Buys:* the sign-off's architecture (BRIEF §5 item 2: "Handlers are models and capabilities are comodels of the same signature; `withswap` is the co-operation carrier").
- *Interacts:* it excludes OQ-1 (c). B2 is compatible, and makes B3's two forms provably one. B5 builds on it.
- *Literature:* Plotkin–Power Def 3.1; Ahman–Bauer Def 1, Prop 3; Møgelberg–Staton Thm 8.1 (state access operations ≅ generic effects ≅ algebraic operations, given a comodel on `S`).
- *Evidence:* EffModelRel has capabilities as comodels at SIB (BRIEF §4; `docs/effects-tr/08-decisions.md`, [relayed]).

**B4. Answering is a borrow in the relation.**
- *Shape:* at a table whose entries are all answering, `ewp_handle`'s `[op]` case is discharged by `wpG_M_frameX` (6.65) on the state cell, with `handle_is_shift` lifted to `CDerives`.
- *Cost:* OQ-3 (c) at Core: `effHandle` opens a lifetime at answering sites.
- *Buys:* I4 for `hnd` directly; P2 for answering operations as B7 at W (R5/S-d) with no translation.
- *Interacts:* L.4 (c), or (a) if every site opens one. GhostEnd's handler extent (`frozen_above_extent`) needs (a).
- *Evidence:* `handle_is_shift` (PAPER); `effHandle` opens none (`Core/Fundamental.lean:367-372`).

**B5. Runner architecture.**
- *Shape:* the platform and heap as the outermost runner, answering handlers as user runners, and finalisation by Ahman–Bauer Thm 7.
- *Cost:* a denotational layer; BoLo-as-runner is "not yet decided", and runners are not user-facing.
- *Buys:* P5's finalisation and I4 from one structure; zero cost by construction (runners never capture κ).
- *Interacts:* B3; the P8 menu's 5.2. It does not cover `ctl` (pitfall 10).
- *Evidence:* none.

**B6. Capability transport.**
- (a) Rows and evidence: today's O1, Evidently's evidence vectors.
- (b) Explicit second-class capability arguments: Ξ, decision 57.
- (c) Moded arguments: OxCaml `local`.
- This is the rows-vs-capabilities menu's axis restricted to answering effects. I4 holds under all three; they differ in who proves P2.

**B7. Capability mode.**
- `Mut` (built), `Imm` (read-only handlers; 6.64), `!` (stateless).
- `Imm` and `!` allow two blocks to share one capability, which recovers System C's aliasing for handlers whose operations do not write state.
- `Mut` keeps X.1's "two `&mut` from one handler" rejection.

---

## 6. Where our current targets sit

| property | Lean target | menu position | status (world) |
|---|---|---|---|
| P14 | `WBCore` (companion) | W0 | PROVED (`wbCore`, Core σ=[]) |
| P14 | `ConservativeWB`, `EmbedsNil` (device) | W1 | PROVED AT σ=[], trivially (pitfall 3); open at W |
| P14 | `Conservative` (beside done) | W2 | PROVED AT σ=[], trivially; open at W |
| P14 | none | W3, W4, W6 | not stated |
| P14 | B4 in `B.Guarantees`; S5 | W5 | B4 proved for today's rules; S5 open at our instance |
| I1 | `I1 M` (device) | V2 | PROVED AT σ=[] (`i1_core`) |
| I1 | E9 `StoredK`, E1′, `I1Prog` (done) | requires V2–V4, excludes V1 | E9, E1′ open at our instance; `I1Prog` from `Combined` |
| I1 | `J.out` at κ | V3 or V4 (OQ-28) | open; `OutJ.core` has no `U C` rule |
| I1 | `FreezeBinder` (beside done) | V6 | stated, open |
| I4 | `I4a` (Pins, done) | B1 | PROVED AT A RESTRICTION (tier 1, abortive rows) |
| I4 | `I4Typing` (beside done), `I4c` (binary) | B2 | stated, OPEN |
| I4 | none | B3, B4, B5 | not stated; B3 is the signed-off architecture |

**Observations from reading, with no Lean checks run:**
1. **P14's proved statements carry no tier-2 content yet.** At `coreB`, `M.val` is Core's relation and the proofs are `vC_local`. That is right for a statement meant to bite at W, but the register's "proved for tier 1 by construction" should be read as W0, not W1/W2.
2. **`ConservativeWB`'s class is already T7's `{fn, abort}`** under decision 57 (coupling 2). If answering operations ever enter rows as layers (B2 with answering in rows, or B6 (a)), `AbortRows` would exclude them. W1 would then need an `answering` class in the guard. I have not checked whether `AbortRows` admits every type at which `i4a_tier1`'s borrow forms live.
3. **No P14 statement is at the library level** (pitfall 2). W1/W2 transfer Core-relation proofs only. A library proved in Core's relation is the only kind we have, so this is not a gap today. It becomes one if `unsafe`/extern contracts are verified elsewhere (B4′'s externs read W's contract through `EmbedsNil`: `contractsW_of_meets`).
4. **`I4a`'s `ImplTyped` is dead** (AGREE §5). So `I4a` as stated does not mention the co-operations' types, and B3's comodel reading of `co` is not yet connected to any target.
5. **E9 in done excludes V1 as the sole mechanism.** That is consistent with T2's "second-class unless boxed". At tier 1, `kTy` stored in a cell is enough. At tier 2 a κ holding external lends needs V3 or V4.

**Inventory (CLAUDE.md §5, as it applies to a survey chapter):**
- **Untranscribed literature results in the run-up:**
  - Timany–Birkedal Def 4.1 and TGB's wbwp have no counterpart (W4).
  - Møgelberg–Staton Thm 8.1 and Ahman–Bauer Prop 3 have no counterpart (B3).
  - Evidently Thm 5 has no counterpart. `capPass` is its static analogue and is unproved as a translation (`I4Typing` open).
- **Unspent hypotheses:** `I4a`'s `ImplTyped` (dead, per AGREE).
- **Unused results we have:**
  - `handle_fold` (`Core/Handlers.lean`), the state-passing fold of answering clauses. It is the natural first lemma for B2 or B3.
  - `handle_is_shift` (PAPER), for B4.
  - `RowCon.cls`, for W3.
- **Printed BoLo lemmas in the run-up that are untranscribed:** 6.40 (the one untranscribed `Paper/INDEX.md` row, per the P10/P9 chapter); 6.150 at a resuming table (I2 chapter). Neither is needed by W0, V2 or B1 as they stand.
- **Obstructions claimed: none.** Every "open" above means I have not derived it and have not verified that any obstruction is real.

---

## 7. What could not be verified

- The ACM numbering of Ξ's theorems. The TR prints them as Thm 4/5/6 and cites them as 4.3/4.4/5.1.
- Uustalu, *Stateful runners of effectful computations*, MFPS 2015: only the talk abstract was read.
- DNB's JFP 2012 version and technical appendix.
- RFC 2394 (async/await).
- The Ante 2024 post's "same handler" rule. It is relayed through the deep dive and is not on the current tour page.
- Koka's `final ctl`: its non-resuming meaning is not defined in the book's prose.
- The 2-D inference-rule layouts quoted from System C, Affect and Tang. Premises and conclusions were re-linearised from extracted text.
- Lutze et al. 2023 (effect exclusion), Oxide, CC<:□, and Müller et al. 2023, relayed from the survey and sibling chapters.

---

## Sources

Read for this chapter, from full text:
- Dreyer, Neis, Birkedal. *The Impact of Higher-Order State and Control Effects on Local Relational Reasoning.* ICFP 2010. §1, §5, §5.1, §8; Thms 2–4. https://people.mpi-sws.org/~dreyer/papers/stslr/icfp.pdf
- Timany, Birkedal. *Mechanized Relational Verification of Concurrent Programs with Continuations.* ICFP 2019. §2, Fig. 1, Fig. 4, Def 4.1, Fig. 5, §8. https://cs.au.dk/~timany/publications/files/2019_ICFP_logrelcc.pdf
- Timany, Guéneau, Birkedal. *The Logical Essence of Well-Bracketed Control Flow.* POPL 2024. Abstract, §3, Thm 3.1, §8, §9, §10. https://cpv.au.dk/pdfs/2024-popl-well-bracketed.pdf
- Stepanenko, Nardino, Frumin, Timany, Birkedal. *Context-Dependent Effects in Guarded Interaction Trees.* ESOP 2025. Abstract, §3.2, Def 1, Lemma 5. https://iris-project.org/pdfs/2025-esop-gitrees.pdf ; extended version, Def 6.1, Lemma 6.2: https://arxiv.org/pdf/2512.11577v1
- de Vilhena, van Collem, Wright, Krebbers. *A Relational Separation Logic for Effect Handlers* (blaze). POPL 2026. §4.3, Thm 4.1, §7. https://iris-project.org/pdfs/2026-popl-blaze.pdf
- Xie, Brachthäuser, Hillerström, Schuster, Leijen. *Effect Handlers, Evidently.* ICFP 2020. §1, §2.2, §4.5, §6.2–§6.4, Thms 4–11. https://www.microsoft.com/en-us/research/uploads/prod/2020/07/evidently.pdf
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Abstracting Algebraic Effects.* POPL 2019. Abstract. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl19.pdf
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Binders by Day, Labels by Night.* POPL 2020. Thms 2, 5; §7. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl20.pdf
- Zhang, Myers. *Abstraction-Safe Effect Handlers via Tunneling.* POPL 2019. Abstract. https://www.cs.cornell.edu/andru/papers/tunnel-eff/tunnel-eff.pdf
- Jung, Jourdan, Krebbers, Dreyer. *RustBelt.* POPL 2018. §3, §5.1. https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf
- RFC 1066, *Safe mem::forget.* https://rust-lang.github.io/rfcs/1066-safe-mem-forget.html
- without.boats, *The Scoped Task Trilemma.* https://without.boats/blog/the-scoped-task-trilemma/
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki. *Effects, Capabilities, and Boxes.* OOPSLA 2022 (TR). Fig. 2 ([Try], [BoxIntro], [BoxElim]), §3.3, §4.3, §5.2 Example 10. https://se.informatik.uni-tuebingen.de/publications/brachthaeuser22effects.pdf
- Brachthäuser, Schuster, Ostermann. *Effects as Capabilities* (TR, *Effekt: Lightweight Effect Polymorphism for Handlers*). OOPSLA 2020. Abstract, §1.4, §4, Thms 4–6, §7. https://se.cs.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf
- Schuster, Brachthäuser, Ostermann. *Compiling Effect Handlers in Capability-Passing Style.* ICFP 2020. Thm 5.1, Cor 5.2, Thms 5.4–5.5. https://se.cs.uni-tuebingen.de/publications/schuster20capability.pdf
- van Rooij, Krebbers. *Affect: An Affine Type and Effect System.* POPL 2025. §2.1, §2.2, §3.1, Fig. 3, Fig. 7, §5.3. https://iris-project.org/pdfs/2025-popl-affect.pdf
- de Vilhena, Pottier. *A Separation Logic for Effect Handlers.* POPL 2021. §2.1 (R6), §3, Fig. 7, §4.2.2. https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf
- Tang, Hillerström, Lindley, Morris. *Soundly Handling Linearity.* POPL 2024. Fig. 4 (T-Handler), Thm 3.4(2). https://arxiv.org/pdf/2307.09383
- Phipps-Costin et al. *Continuing WebAssembly with Effect Handlers.* OOPSLA 2023. Fig. 2, Fig. 4, §2.4, §3. https://arxiv.org/pdf/2308.08347
- Muhcu, Schuster, Steuwer, Brachthäuser. *Multiple Resumptions and Local Mutable State, Directly.* ICFP 2025. §1, §2. https://se.cs.uni-tuebingen.de/publications/muhcu2025multiple.pdf
- Ma et al. *Lexical Effect Handlers, Directly.* OOPSLA 2024 (TR CS-2024-04). §3.1, §3.2, §7.2. https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024-tr.pdf
- Ahman, Bauer. *Runners in Action.* ESOP 2020. §1, §2, Defs 1–2, Prop 3, Thms 6–7, §6. https://arxiv.org/pdf/1910.11629v2
- Plotkin, Power. *Tensors of Comodels and Models for Operational Semantics.* MFPS 2008. Abstract, §1, Def 3.1, Thm 4.4. https://homepages.inf.ed.ac.uk/gdp/publications/Tensors_Comodels_Models.pdf
- Katsumata, Rivas, Uustalu. *Interaction Laws of Monads and Comonads.* LICS 2020. §4.1. https://arxiv.org/pdf/1912.13477
- Møgelberg, Staton. *Linear Usage of State.* LMCS 10(1), 2014. Abstract, §1.2, §1.3, Thms 4.1–4.3, §8, Thm 8.1. https://arxiv.org/pdf/1403.1477
- Forster, Kammar, Lindley, Pretnar. *On the Expressive Power of User-Defined Effects.* Thms 6.3, 6.7, 6.9, 6.10. https://arxiv.org/pdf/1610.09161v2
- Koka book, §3.4.3, §3.4.12. https://koka-lang.github.io/koka/doc/book.html
- Ante language tour. https://antelang.org/docs/language/
- janestreet/handled_effect, README and `raises_in_jsoo/handled_effect_intf.ml` (branch `oxcaml`). https://github.com/janestreet/handled_effect ; OxCaml `stdlib/effect.mli`. https://github.com/oxcaml/oxcaml
- rustc E0626. https://doc.rust-lang.org/error_codes/E0626.html ; `rustc_type_ir` `TyKind::CoroutineWitness`; Unstable Book, *coroutines*; `core::pin` documentation.

Read, talk abstract only:
- Uustalu, *Stateful runners of effectful computations*, MFPS 2015. https://kodu.ut.ee/~vlaan/kaariku/2015/abstracts/abstract_Uustalu.pdf

Relayed, not re-read here:
- Survey A1, A5, A7, C1, C6, T1–T7, §2 P2 (S1–S5): `research/effects/survey.md`.
- Ante's 2024 rule, H1–H4 and the second-class objection: `~/repos/borrow-core/research/effects/ante-deep-dive.md`.
- Lutze et al. 2023, Oxide, CC<:□ and Müller et al. 2023, via the survey and the [P10/P9](p10-p9-exclusivity-lifetimes.md) chapter.

Local sources:
- `experiments/Targets`:
  - `Targets/B/Conservativity.lean` (`WBCore`, `ConservativeWB`, `Conservative`);
  - `Targets/B/BoLo.lean` (`wbCore`, `conservative_core`, `conservativeWB_core`);
  - `Targets/B/Guarantees.lean` (`AbortRows`);
  - `Targets/I/Device.lean` (`EmbedsNil`, `Device`);
  - `Targets/I/Interface.lean` (`I1`, `I4a`, `I4Typing`, `I4c`, `admClosedOp`, `RowSpan`);
  - `Targets/I/Restricted/Device.lean` (`i1_core`);
  - `Targets/I/Restricted/Answering.lean` (`i4a_tier1`);
  - `Targets/I/Programs.lean` (`I1Prog`);
  - `Targets/A/Expressiveness.lean` (E9 `StoredK`);
  - `Targets/Base/Programs.lean` (`AnsImpl`, `ansCall`, `ansRun`, `ctlClause`, `ctlForm`, `capPass`);
  - `Targets/Base/Rows.lean` (`RowClass`, `RowCon`);
  - `AGREE.md` §5; `RESTRUCTURE.md` §3.2, §3.6.
- `~/repos/borrow-core`:
  - `Core/EffDefs.lean` (`wpG`, `contShare`, `opTable`);
  - `Core/EffRules.lean` (`KapRel`, `kTy`);
  - `Core/RelationFacts.lean` (`vC_local`);
  - `Core/Handlers.lean` (`op_tail`, `op_answer`, `handle_fold`);
  - `Core/Aff.lean`;
  - `experiments/HandlersAsBorrows` (README; `Safety.lean`: `effect_safety`, `handle_is_shift`, `capability_not_outlives`; `Sharing.lean`: `twoBlocks_refused`);
  - `experiments/SecondClass` README;
  - `docs/effects-state/BRIEF.md`; `05a` (OQ-1, OQ-3, OQ-28, OQ-29).
- Notebook: `properties/{conservativity,i1-suspension-value,i4-answering-borrows}.md`, `foundations/*.md`, `register.md`, and the five sibling menus in `prior-art/`.
