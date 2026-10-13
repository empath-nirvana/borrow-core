# Prior art: rows versus capabilities as the effect representation

This note compares ways of representing effects in types for borrow-core. It ends in a menu of options with trade-offs. It does not recommend one.

**The goals the options are judged against.** These are the goals, not the means:
- **Effect polymorphism, meaning no function colouring.** One higher-order function, typed once, serves pure, failing and suspending callbacks (System A's E1/E2).
- **Handling is erased, and the lowering is chosen by specialisation.** A tail-resumptive operation becomes a call, an abortive one a branch, and a suspension a state machine.
- **Zero cost** against the hand-written equivalent (P13).
- **Nothing breaks the borrow calculus** (System B's guarantees, B0–B7).

Fixed constraints are a linear core with explicit cancel, deep handlers, and multi-shot ignored (decision 63). **Row variables in the kernel (decision 62) is a means to effect polymorphism, not a goal** (user, 2026-10-06: "It's not a core goal it was an implementation choice to reach a goal."). No option is weighted by it here.

**How claims are marked.**
- **[read]**: I or a reading agent read the statement in the primary source's full text for this note, and the quote is copied from it.
- **[relayed]**: taken from a secondary source, or from another notebook page that marks it [V].
- **[unverified]**: from memory or not checked.
- **[local]**: read off this repository's code or documents. **[synthesis]**: my reading, not a source's claim.

Theorem numbers follow the version named in the sources list.

---

## 0. The menu

### 0.1 Summary table

| | option | how no colouring is achieved | what the lowering sees at a HOF's instantiation | effect safety from | no accidental handling | handler-state exclusivity | tier 2 (lends across a suspension) | proof burden for us |
|---|---|---|---|---|---|---|---|---|
| **O1** | **Rows of labels** (Koka, Links, Frank; today's `CTy.eff` layers + targets' `RowCon`) | a row variable `ε` in the HOF's type, instantiated per use | the instantiated row: its labels, hence each label's declared class, and (with static sites) the handler. Exact when the row is closed at the call; a **bound** on `ε` (`RowCon.cls`) gives the class inside the HOF | the row algebra (Yoshioka Def 5.1), proved separately from lifetimes | needs extra machinery: static per-site names + site freshness (today), lacks constraints, tunnelling, or masking | not from rows: the handler site must also open a lifetime (OQ-3), which rows do not carry | **hidden**: a label says nothing about which lends span the stop; the borrow side must recover it (today's T1/`↭` stop) | lowest for effect safety (`rowAlgSafe_orowRF` proved); row variables in `CDerives` and the relation not built (two `CTy` formers, a row environment `η`, a substitution lemma) |
| **O2** | **Capabilities as borrows** (Effekt / System Ξ / System C; HandlersAsBorrows) | contextual polymorphism: a called-only callback is a second-class block, and its effects are those of the caller's context, not in the HOF's type; stored callbacks are boxed at a capture set, here a **lifetime bound** | **nothing in the HOF's type.** The class comes from the callback value (its code and the handlers its captures are bound to), so specialisation is keyed by the argument, as Rust keys by closure type. A lifetime bound forgets *which* capabilities, so it forgets the class too | **outlives** (B7, 6.60): a capability used after its handler is a borrow used after its lifetime (`effect_safety`, PAPER) | by construction: lexical binding | **free for answering handlers**: two `&mut` from one handler is a reborrow error (B6). Cost: System C's aliased stateful capability is refused (`twoBlocks_refused`) unless the state sits behind control (SecondClass P5) | **explicit**: a stored callback or continuation carries the lifetime of every lend it holds | HandlersAsBorrows covers answering handlers at PAPER only; control operations are not lends today (T1/`↭`); needs block parameters (FnMut-shaped), a box/outlives rule at `U C` (T2), and a decision on aliasing |
| **O3** | **Rows of capabilities**: rows whose elements are lends `(instance, lifetime)`, optionally with a class (EffModelRel `Rw`) | a row variable ranging over sets of lends, or contextual polymorphism for called-only callbacks with rows only on stored ones | the row's instances and lifetimes, and the class if the element carries it (EffModel's `inst E b`, `b = (req, susp)`) | both readings at once: membership (row algebra over instances) and the lifetime component (outlives) | by construction (instances are binders) | the instance's lifetime is the handler's lend; exclusivity as in O2 | **explicit in the lifetime component**; the row's meet is the thunk's lifetime (`Rw.life`) | proved in a sibling calculus (SIB: `safety`, `safety_obs`; no bridge to Core); the lifetime component is read only for scope there |
| **O4** | **Modal effects** (Met, Met(X)) as the common encoding | absolute/relative modalities on the context: a callback under the identity modality uses the ambient effect, so `map` needs no effect variable; effect variables remain for the cases Met lists | the ambient effect context at the call site (a row or set of labels, per the chosen effect structure `X`); class as in O1 if labels carry it | Met(X)'s validity conditions (TL Def 3.5) plus Thms 3.7/3.8, for any effect structure `X` | depends on `X`; local labels give it | not addressed by the modal layer | not addressed by the modal layer | a modal kernel; all evidence is paper proofs; rows (`R_scp`) and System C (`S`) encode into it |

### 0.2 The cross-cutting finding: where the control class lives

The key test (§2) is what the lowering knows about a callback's control class when it compiles a HOF's instance. The class is one of: none (pure or answering), abortive, suspending. It decides whether `h`'s call of `f` is a plain call, a call with a branch after it, or a resumption point that turns `h`'s frame into a state machine. The options differ less in *whether* the information exists than in **which carrier holds it**:

| carrier | O1 | O2 | O3 | O4 |
|---|---|---|---|---|
| the HOF's type | yes, if the row variable is bounded (`RowCon.cls`) | no (contextual) | yes, if the element carries a class | via the effect structure `X` |
| the argument's type at the call | yes: the instantiated row | the block's type has no effects; the capture set says which capabilities, a lifetime bound does not | yes | yes: the ambient context |
| the argument's value | redundant | **required**: the code and the handlers its captures name | redundant | redundant |
| declared per operation (`lin`/`aff`/abort) | yes | yes | yes | yes |
| the handler (tail-resumptive or not) | needed for the exact class; known statically with static sites (SPEC §19 *Lowering*) | needed; lexical binding makes it statically known more often (Lexa; Müller et al.) | needed | needed |

So under O2 the class is **not a type**: specialisation must look at values, and an un-specialised HOF body must assume the worst class (a state machine at every call of a block). O1, O3 and O4 can put an upper bound on the class in the type. O2 can be given the same with one added grade on block and box types (variant O2-g, §0.3), or a coarse version through ICFP 2020's stack shapes. [synthesis]

**No published system passes the class to a HOF through its types** (§2.2, five row-side and four capability-side sources read). Koka's CPS backend gets one bit (yields or not) by compiling two versions of every row-polymorphic function and choosing at run time; evidence passing and Lexa dispatch on a tail/normal tag read at the perform; Karachalias et al. leave HOF parameters alone. borrow-core's elaborator already specialises per callback type and per handler assignment (SPEC §14, §18), which is further than any of these compilers goes for HOFs. A class in the type (O1's bound, O2-g, O3's element bound) would be ours.

### 0.3 Variants worth listing separately

- **O1-a** simple rows over static per-site names (today, R1 of [P2](p2-effect-safety.md)); **O1-b** with lacks constraints (R3); **O1-c** scoped rows with masking (R4). They differ on accidental handling and on the Yoshioka conditions, not on the lowering test.
- **O1-ε-bounded**: row variables carry a class bound (`RowCon.cls ∈ {abortive, resumeOnce, any}`, targets `Base/Rows.lean`). This is what gives O1 the class inside an un-specialised HOF.
- **O2-pure**: System Ξ (blocks second-class, no boxes). **O2-C**: System C (boxes with capture sets). **O2-lt**: System C with capture sets replaced by BoLo lifetime bounds (HandlersAsBorrows' reading). **O2-g**: O2-lt plus a control-class grade on blocks and boxes.
- **O3-surface**: O2 at the surface, elaborated into O3 in the kernel (capabilities for the programmer, rows of lends for the checker and the lowering).

---

## 1. What each option is, precisely

### 1.1 O1: rows of labels

**The literature.**
- Koka: a row is a list of labels with an optional tail variable; `map : forall<a,b,e> (list<a>, a -> e b) -> e list<b>`. Duplicates allowed (scoped rows), so a handler removes one occurrence. [relayed: P2 note §1.3, Leijen 2017 TR, [V] there]
- Links: Rémy rows with presence types `Pre(A) | Abs | θ` (Hillerström–Lindley 2016, Def 3.2, Thm 3.3). [relayed, [V] in P2 note]
- Frank: the **ambient ability**. Frank (Lindley, McBride, McLaughlin 2017) [read]: "Effect typing in Frank employs a novel form of effect polymorphism which avoid mentioning effect variables in source code. This is achieved by propagating an ambient ability inwards, rather than accumulating unions of potential effects outwards." §2.2: "the empty bracket stands for the ambient ability, not for purity; the map operator is implicitly effect-polymorphic." §3.1: `{X → Y} → List X → List Y` "desugars into: ⟨ι⟩{⟨ι⟩X → [ε]Y} → ⟨ι⟩(List X) → [ε](List Y)", where "ε is a distinguished effect variable, the implicit effect variable that is fresh for every type signature". So Frank is still a row system with one hidden variable; Met §1 [read]: "Frank still uses effect variables behind the scenes … this syntactic mechanism is fragile. For instance, effect variables can appear in error messages".
- Koka 2014 (Leijen, MSFP) [read]: `map : ∀αβμ. (list⟨α⟩, α → μ β) → μ list⟨β⟩`, "where the effect of the map function itself is completely determined by the effect of its argument". Two callbacks share one variable: `foo : ∀μ. (() → ⟨exn|μ⟩ (), () → ⟨exn|μ⟩ ()) → ⟨exn|μ⟩ ()`, which works because "we always infer a polymorphic open effect for each expression". Unions were rejected ("constraints of the form μ1 ∪ μ2 ∼ μ3 ∪ μ4 which cannot be solved uniquely"); §3.1 claims "an efficient type inference algorithm that infers principal types and is sound and complete with respect to the type rules".
- Yoshioka, Sekiyama, Igarashi 2024 abstract the algebra: Def 5.1's conditions (1) and (2) are all the progress proof uses; (3) only with lift/masking; (4) only when dispatch ignores type arguments; Table 2: simple and scoped rows have one tail variable, so no `ρ₁ ⊙ ρ₂`. [relayed, [V] in P2 note]
- Accidental handling. Zhang–Myers 2019 §1 [read]: "suppose an implementation of map traverses the list using an iterator object. The iterator throws a NoSuchElement exception when it reaches the end of the list … If the client function f also happens to throw NoSuchElement, the implementation may handle—by accident—an effect it is not designed to handle." The principle: "parametricity of effect polymorphism demands that an effect-polymorphic function should not make decisions based on the effect it is instantiated with. Yet the dynamic nature of algebraic effects runs afoul of this requirement". Their fix is not a row algebra: "Algebraic effects can be handled only by handlers that are statically aware of them; otherwise, effects tunnel through handlers", realised by passing handler variables (`iterate[X, h : Yield[X]](tr) : void / h`), with "an omitted handler … always resolved to the nearest lexically enclosing handler binding". Effects are sets of handler variables. On rows: prior row-based efforts "compromise[] on the expressiveness of effect subsumption and rel[y] on extra programmer annotations". Thm 1 (Parametricity), Thm 2 (Type Safety), Thm 3 (Soundness, `≼log ⇒ ≼ctx`). So tunnelling is itself a capability mechanism layered on an effect system.

**Ours.** Core's computation types carry per-operation layers `CTy.eff n i q A B C` (`Core/Types.lean:92`), a first-match list keyed by `(n, i)`, with continuation qualifier `q ∈ {lin, aff, unr}`. **Main has no row variable former**: the targets library states rows with tails, row contexts and constraints (`RVar`, `RowCon { cls : RowClass, adm }`, `RowClass ∈ {abortive, resumeOnce, any}`; `experiments/Targets/Targets/Base/Rows.lean`), and the elaborator gets polymorphism by copying a function per assignment of its effects (SPEC §18: "A function with a row is elaborated once per assignment of its effects to what serves them in scope") and per callback computation type (SPEC §14, "whole-program monomorphization, with no kernel change"). [local]

### 1.2 O2: capabilities as borrows

**The literature.**
- **System Ξ** (Brachthäuser, Schuster, Ostermann, OOPSLA 2020; extended TR read) [read]. §1.3: "Effekt does not have language constructs for type-level effect variables or quantification over effects. Still, it supports effect polymorphic reuse of functions and guarantees effect safety… Users never have to deal with parametric effect polymorphism as the feature simply does not exist: polymorphism implicitly arises from the calling context." §1.4: "The block passed to eachLine simply closes over the capabilities that are in scope at its definition site." Rule Def (§3.2.2): "programmers can control which effects are handled at the call-site (i.e., ε′), and which effects are free … and need to be handled at the definition site of a block." The limit (§1.6): "blocks are considered second-class and can neither be returned nor stored in data structures … while Effekt supports higher-order functions (like eachLine), it does not support first-class functions." `resume` has type `(τ0) → τ / ∅`: "Typing the continuation with the empty set of effects is safe since it is a block and cannot leave the scope of its definition." §4.2: System Ξ "does not include an effect system. Effect safety is simply established by treating blocks as second class." Effect safety: TR Thm 4 (Progress), Thm 5 (Preservation), "programs are never stuck on an undelimited label" (TR numbering; the TR's prose cross-references 4.3/4.4, presumably the ACM numbers [unverified]). The price (§1.5): "we lose purity guarantees since contextual purity does not imply purity".
- **System C** (Brachthäuser, Schuster, Lee, Boruch-Gruszecki, OOPSLA 2022; extended TR read) [read]. §2.3: "No effect variables show up in types nor error messages. Yet, it features effect polymorphism and guarantees effect safety. This is because effect signatures in Effekt are relative to the calling context." And its cost: "While this leads to concise signatures, it means we cannot require function parameters to not use certain effects!" Boxes (§1.3): "Boxing converts a second-class value to a first-class value, reifying the contextual information annotated on the binder into the boxed value's type (e.g., f :C σ ⊢ box f : σ at C) … we can only unbox … when the capabilities are still in scope." `resume` is transparent at a capability set: "we have box {console, time} resume since the handled program uses console and the handler uses time" (§3.3); the algorithmic rule has a cycle "since we offer support for first-class continuations" (§5.3). §6.7: "In second-class mode, we fully avoid the ceremony of parametric effect polymorphism. However, System C does not improve the verbosity of type-based reasoning with first-class values." Thm 3, Lemma 4, Thm 5, Cor 9, mechanised in Coq. Regions (§5.2, Fig. 4): "every block definitions and effect handlers implicitly creates a new region"; §6.6: "tracked variables serve the dual purpose of regions and handles".
- **Capture checking** (Boruch-Gruszecki, Odersky, Lee, Lhoták, Brachthäuser, TOPLAS 2023, "Capturing Types") [read]. §1: `def map(f: A => B): List[B]` "is exactly the same as the type of map in current Scala, which does not track effects! … In that sense, we get effect polymorphism for free." Lemma 4.12 (Capture Prediction for Terms): capture sets "predict variables that will be captured by the answer those terms reduce to"; Thm 4.14 (Used Capability Prediction). **Capture sets carry no control class**: "the formal treatment presented here does not mention effects. In fact, the effect domains are intentionally kept open … capabilities can delimit what effects can be performed at any point in the program, but they by themselves do not perform an effect." §2.6: "the universal capability cap should conceptually only be available as a parameter to the main program."
- **From capabilities to regions** (Müller et al., OOPSLA 2023) [read]. §2.3: "each call-site region of a block is a subregion of its definition-site region. This is facilitated by the second-class property of blocks in System Ξ." Thm 3.6 (typability preservation), Thm 3.7 (evaluation, `n+2k` steps). The paper's limit: "it [is] less clear to us how to translate the sets of capabilities (e.g., {yield}) to the corresponding region. We leave studying the translation of System C to Λcap to future work."

**Ours.** In BoLo a borrow is a lifetime-polymorphic second-class value: a `withbor` callback receives `'x` and `Mut 'x S`, and 6.60 forbids it to escape. HandlersAsBorrows proves, at the paper layer, that System Ξ's answering handlers are exactly this:
- `handle` is `withbor` form (2) lending the handler state as `Mut 'x S`, an operation is `withswap` on it (`translate_typed`);
- effect safety is the FP plus adequacy (`effect_safety`): "Effect safety therefore becomes **no use of a borrow after its lifetime**";
- System C's box is "an owned thunk whose type records what it borrows", and subcapturing maps to outlives by `C ↦ ⊓{lifetime(f) | f ∈ C}`, which "forgets *which* capabilities were captured, and System C uses that as effect information … so it is not an isomorphism" (README §5, precondition 3). [local]

What stops it today: control operations are not lends (T1 conjunct 40 and `↭` conjunct 37 stop a lend from spanning a stop; BRIEF §3.1), `U C` has no outlives rule (`thunk_not_outlives`, T2), block parameters that capture a `Mut` and are called many times are FnMut-shaped and not covered by `!` (precondition 1), and an aliased stateful capability is refused (`twoBlocks_refused`). [local]

### 1.3 O3: rows of capabilities

The elements of a row are not labels but **lends**: an instance together with the lifetime at which it is lent. EffModelRel's `Rw` is this: "a list of `(instance, lifetime)` pairs, both de Bruijn *levels* … The thunk's lifetime is the meet of the pairs' lifetimes (`Rw.life`) … its effect bound, the join of its instances' declared bounds, is recovered from the row (`Row.mode`)". Its own caveat: "In this calculus the lifetime of a pair is its instance's own level: no rule reads the lifetime component beyond scope. It is where a borrow's lifetime would go." (`docs/effect-model.md` §9.1) [local]

EffModel's instance type `inst E b` carries the bound `b = (req, susp)`: `req` is the join of the effect's continuation qualifiers, `susp` whether the handler may keep a continuation past the operation. "So one type, `inst E b`, covers both implementations. A function that asks for `inst Log ⟨lin, false⟩` accepts a runner's instance or a tail-resumptive handler's." (§1.2) That is a class carried on the element. [local]

Literature: the closest published forms are System C's capture sets on boxes (sets of capabilities, not lifetimes), Met(X) with the set structure `S` (System C's encoding), and Biernacki et al. 2020's lexically scoped instances as type binders [relayed: P2 note §1.5].
- Met(X) with the set structure `S`, the target of System C's encoding: "Theory S allows arbitrary numbers of effect variables while theory R_scp only allows at most one effect variable in each row" (Met(X) §2.1.4) [read]. System C's block type `(A, f : T) ⇒ B` encodes as `∀f*.⟨f*⟩(⟦A⟧ → [f*]⟦T⟧ → ⟦B⟧)` and `T at C` as `[⟦C⟧]⟦T⟧`: one effect variable per capability parameter, so a box's capture set becomes a row of capability variables (§5) [read]. This is O3 without lifetimes.
- Xie et al. 2022 (first-class names): a named handler contributes a row label `ℓ^η` indexed by a rank-2 scope variable, "reflecting the similarity between scoped effects and runST"; "it is important that the effect itself (vec⟨s⟩) includes the scoped type variable. This ensures that we cannot hide the use of an index inside a lambda" (§4, §3.2.2) [read]. A row element indexed by a scope is the nearest published analogue of a row element indexed by a lifetime.
- Zhang–Myers' effects are sets of handler variables (`{ind, io}`, `h.lbl`) [read]: rows of capabilities without lifetimes.
- Degrees of Separation (Xu, Boruch-Gruszecki, Odersky; arXiv 2308.07474v2) adds separation to capture sets: "if f is separated from p, there is no mutable state referred to by both f and p and mutated by either of them"; "Any two reader capabilities are considered to be separated from each other" [read]. That is Imm/Mut exclusivity stated over capture sets.

### 1.4 O4: modal effects

**Met** (Tang, White, Dolan, Hillerström, Lindley, Lorenzen, OOPSLA 2025; arXiv 2407.11816v3) [read].
- §1: "We treat each possible ambient effect context as a mode, and each possible transition between effect contexts as a modality … 1) absolute modalities, which override the ambient effect context; and 2) relative modalities, which describe a local change to the ambient effect context". §4.3: `[E](F) = E`, `⟨L|D⟩(F) = D + (F − L)`.
- No effect variable for `map`/`iter` (§2.2): `iter : []((Int → 1) → List Int → 1)`, and "due to subeffecting, iter is not limited to only the empty effect context". The row-based counterpart is `∀e. (Int −e→ 1) −e→ List Int −e→ 1`. Two callbacks: `compose : forall a b c . []((a → b) → (b → c) → (a → c))` with no variable (§8.2).
- Where variables remain (§2.10): "effect variables are only necessary for use-cases such as higher-order effects in which a computation needs to be stored for use in an effect context different from the ambient one." §8.1: "Met without effect polymorphism is not expressive enough to encode all of Effekt."
- Thm 4.3 (Progress), Thm 4.4 (Subject Reduction).

**Met(X)** (Tang, Lindley, POPL 2026; arXiv 2507.10301v2) [read].
- Def 3.1: "An effect structure X is a tuple ⟨:, ≡⟩ of two relations". Def 3.5 validity conditions (Yoshioka's (1)(2)); Thm 3.7 (Progress), Thm 3.8 (Subject Reduction) "where X satisfies the validity conditions".
- Encodings **preserve types and semantics** (forward simulation): System Fε → Met(R_scp), Thm 4.1 and Thm 4.2 ("If M is well-typed and M ⇝ N in System Fε, then ⟦M⟧ ⇝* ⟦N⟧"); System C → Met(S), Thm 5.1 and Thm 5.2. System Ξ (Thm D.2) and Koka's named handlers (Lemma D.4) also encode. (The [P2](p2-effect-safety.md) note records only the type side.)
- §2.4: "capabilities in System C act as an implicit form of parametric polymorphism, abstracting the capabilities used by each block variable. This explains why capability-based effect systems do not require explicit effect variables in many cases where row-based effect systems do." And: "functions in System Fε can only use those effects specified in their types, whereas blocks in System C can use arbitrary effects from the context unless they are boxed."
- §7: Fε corresponds to CBV ("each function is wrapped in an absolute modality, reminiscent of the CBV-to-CBPV encoding where each function is thunked"), System C to CBN ("thunking of a function is deferred until passing it as an argument").
- §6.3(2): "we need not sacrifice first-class functions in order to obtain the benefits of the contextual effect polymorphism of Effekt." §6.3(5): capabilities can be simulated "by introducing an effect variable for each argument and wrap[ping] the argument into an absolute modality".
- Met(X) has no masking (§6.4) and no linearity (no occurrence of "linear").

---

## 2. The key test: what the lowering gets at a HOF's instantiation

### 2.1 What the lowering needs

The backend lowers by class (BRIEF §1, *Toolchain*; SPEC §19 *Lowering*): "A tail-resumptive operation is a direct call. When every handler of a name whose body may perform an operation has the same closed clause for it (the specialisation: the handler is known statically) … Nothing suspends or resumes, and no continuation is materialised." Abortive operations are a branch per call; control operations a state machine. [local]

For a HOF `h(f)` the question is how to compile `h`'s body around each call of `f`. Three facts decide it:
1. **Does `f` suspend?** Then the call is a resumption point: `h`'s frame becomes a state-machine state, and its locals live in the state record.
2. **Does `f` abort?** Then the call is followed by a branch, and `h`'s live owned locals need landing pads (drop glue).
3. **Neither?** A plain call.

`docs/effect-polymorphism.md` §0 calls this the callback's **profile**: "which of abort, suspension and multi-shot the row contains, because those change drop glue and the state machine". The profile, not the effect identities, is what the code shape of `h` depends on. Effect identities matter only for routing an operation to its handler, and with lexical or static resolution that routing is fixed where the callback was written. [local; synthesis]

Note what is *not* enough: an operation's declared qualifier says whether a handler *may* keep the continuation, not whether the handler in scope does. `Yield` handled by a tail-resumptive clause is a call (SPEC §19). So the exact class needs the handler; the declaration gives an upper bound. EffModel computes it from the handler's clauses (`susp`, by the syntactic `Tm.tailOnly` test) and puts it in the instance's type. [local]

### 2.2 Per option

**O1, rows.** At `h[ε := ⟨exn⟩](f)` the lowering reads the instantiated row. Each label's declaration gives an upper bound on its class; with static per-site names the elaborator knows the site and hence the clauses, so the exact class. This is how the built toolchain works: a copy per assignment of effects, and per callback computation type (SPEC §14 and §18). An **un-specialised** body of `h` (one shared body, as `docs/effect-polymorphism.md` §5.8 proposes) knows only `ε`. With a bounded `ε` (`RowCon.cls`), the body can be compiled at the bound: `ε : abortive` gives branches and no state machine. 

**The row literature does not give a HOF the class at instantiation** (reading of five sources) [read]:
- Koka's 2016 CPS backend (Leijen TR 2016, §5.1.1): "In general we always need to assume a CPS translation is needed for any µ as such variable may get instantiated later on with a user-defined effect." §5.3.2: "The solution is to generate two translations of every function polymorphic in some effect µ – one is the CPS translation (e.g. mapcps), and one is a plain translation (e.g. mapplain). We then use a wrapper that chooses either implementation at runtime based on whether the continuation argument is present." It is one bit (yields or not), chosen by a run-time test; "Since only the tail of an effect row can be polymorphic, there is no risk of exponential code duplication … the code size increased by a modest 20%."
- Evidence passing (Xie et al. ICFP 2020): tail-resumption is decided **at the handler** ("creates tail terms for any clause f that the compiler determined to be tail resumptive") and dispatched **at the perform, at run time** ("performop w x = let (m, h) = w.l in case h.op of | tail f → f x | normal f → yield m (f x)"), "at a cost similar to a virtual method call". Polymorphic rows cost a dynamic lookup: "Only functions that are polymorphic in the effect tail need to index dynamically" (§6.3). §6.4's type-level classification: binds are left out for "all effects that are statically guaranteed to be tail resumptive (called linear effects)" — a per-effect class declaration.
- Xie–Leijen ICFP 2021 §2.11: with "a polymorphic row type ⟨read | µ⟩, the code would instead be find_ev(ctx→w,tag_read) to find the evidence dynamically".
- Karachalias et al. OOPSLA 2021, footnote 2: "If f is a function parameter of a higher-order function, we don't do anything"; polymorphic HOFs are future work.

So O1's class bound on `ε` (`RowCon.cls`) and per-instance specialisation are **ours**: borrow-core's elaborator already specialises (SPEC §14, §18), which none of these compilers does for HOFs; Koka gets one bit by duplication plus a run-time test.

**O2, capabilities.** `h`'s type mentions no effect of `f`: that is the point of contextual polymorphism. The information is at `h`'s call site, in two places: the block literal's code, and the handlers its free capabilities are bound to. Lexical binding makes the handler of every capability statically known whenever the capability is not passed through an unknown function. Specialisation therefore keys on the argument (a known block), as Rust monomorphises per closure type; it is the natural default for second-class blocks, which by construction are only passed down. [synthesis] What the literature does:
- **Capability-passing style with stack shapes** (Schuster, Brachthäuser, Ostermann, ICFP 2020) [read]. The effectful function type `τ → [τ′]τ̄` carries a **stack shape**, "the list of answer types at its enclosing handlers"; "Programs in an empty stack cannot use any control effects and consequently are not CPS translated" (§3.3.2); "We implement stack shape polymorphism by monomorphization" (§1). A stack shape is a coarse class in the type: how many control layers a function may reach, not which kind. With capabilities second-class and static (λλCap), Thm 5.5 (Full elimination): the translations of capability abstraction and application, `do`, `handle` and `lift` "do not introduce any residual lambda abstractions or applications". The limit is at higher-order *value* parameters, which are residual and specialised only to their stack shape (reading agent's synthesis of §4.2.3 and §4.3); §4.3 [read]: "Being a parameter, prog has a dynamic type, but capability application prog[fail] demands that prog has a static type. We thus cannot define handlers as handler functions in λλCap."
- **Zero-cost Effect Handlers by Staging** (TR 2019) [read] states the assumption: "all used handler implementations and (b) the order in which they enclose the effectful computation" are statically known, which "prevents us from abstracting over handlers". Its printed "Theorem 5 (Zero overhead)" (cited in its text as Theorem 5.5) is the same full-elimination statement.
- **Effekt's general path** (From capabilities to regions) [read]: all effectful code goes through iterated CPS to MLton; the HOF abstracts over the callback's region and evidence, supplied at its call site ("we abstract over them in the definition of call. This way, we can provide them at the call-site of call when we know the concrete block argument we pass for f", §2.2); "evidence monomorphization" partially evaluates with respect to evidence; and "native exceptions in OCaml and in the MLton baseline … are very efficient and indeed faster than our approach of translating to CPS".
- **Lexa** (Ma, Ge, Lee, Zhang, OOPSLA 2024) [read]: lexical scoping makes the handler "directly available—no run-time search is needed"; "tail-resumptive and abortive handlers do not incur any heap allocation"; but the class is a run-time annotation: "the raise implementation look[s] up the annotation in the handler's header frame and dispatch[es] accordingly".

So in the capability literature, too, the class reaches the code by static knowledge of the handler or by a run-time tag, and through a type only as ICFP 2020's stack shape. Without specialisation, the body of `h` must treat every block call as possibly suspending.

With capture sets replaced by lifetimes (O2-lt), a box's type says how long its captures live, not what they do: the class is gone from the type, and a stored callback's call must be compiled at the worst class unless a grade restores it (O2-g). [synthesis, from HandlersAsBorrows precondition 3]

**O3, rows of lends.** The instantiated row lists instances, and with EffModel's bound on each instance the class is in the type; the lifetime component adds which lends the callback holds. An un-specialised body compiles at the join of its row's bounds. EffModel's cost table: "an operation on an instance not known statically is an **indirect call** through it … Specialising an instance known at the call site recovers the direct call; this replaces per-row copying as an optimisation rather than a requirement" (`docs/effect-model.md` §6). [local]

**O4, modal.** The callback under the identity modality runs in the ambient effect context at its call site. The lowering sees that context, which is a row or set of labels according to `X`; the class follows as in O1. Neither Met nor Met(X) discusses compilation of modalities; `mod_μ V` and `let mod` are terms with reduction steps (E-Letmod) [read]. Met(X) §7 lists "further developing Met(X) as a uniform intermediate language for type- and effect-directed optimisation" as future work, and its §1 says it "enables us to design type-directed optimisations" [read]. No claim that a modal type tells a compiler a callback's control class was found [read: searched].

### 2.3 Summary of the test

| | the class is in a type the HOF body can read | specialisation key | un-specialised fallback |
|---|---|---|---|
| O1 | with a bounded row variable | (function, instantiated row's profile) | compile at the bound; unbounded `ε` means the worst class |
| O2 | no | (function, block code + its captures' handlers) | worst class at every block call, or iterated CPS (Effekt) |
| O2-g | yes (grade on block/box) | as O2, or (function, grade) | compile at the grade |
| O3 | yes (bound per element) | (function, row's profile) or instance | compile at the join of bounds; indirect call per unknown instance |
| O4 | via `X` | (function, ambient context's profile) | as O1 |

---

## 3. The other criteria

### 3.1 Effect safety

- **O1:** the row algebra's conditions, proved once (`rowAlgSafe_orowRF`), and effect safety by the FL route (`effSafe_tier1`, Core σ=[]). It is a theorem separate from lifetimes: "Rows say nothing about lifetimes" (survey §2 P6). [relayed: P2 note §4, §6]
- **O2:** effect safety *is* the outlives guarantee B7 at capabilities. System C's Lemma 4 ("Labels are delimited") and Corollary 9 ("never results in an undelimited label") [relayed, [V] in P2 note §1.7]; ours `effect_safety` at PAPER, for answering handlers only. For control operations the capability would have to be a lend that spans a stop, which today's stop condition refuses.
- **O3:** both: membership gives Yoshioka's (1)/(2) as facts about sets of instances; the lifetime component gives outlives. EffModelRel proves `safety` ("no operation reaches the top") with rows read as permissions, in SIB.
- **O4:** Met(X) Thms 3.7/3.8 for any `X` meeting TL Def 3.5. [relayed, [V] in P2 note §1.9]

### 3.2 Abstraction: no accidental handling

- **O1** gets it only from something beside the row: static per-site names plus site freshness (Zhang–Myers' `[t-down]` at static names, `docs/effect-polymorphism.md` §5.3), lacks constraints (R3), tunnelling, or masking with scoped rows (R4). Recursion through a site whose callback tunnels the same site is rejected (decision 57; §6.3 there).
- **O2** has it by construction: a block can only reach capabilities lexically in scope where it was written; HandlersAsBorrows' `atSucc` "is how the translation avoids accidental handling".
- **O3** has it by construction: instances are binders.
- **O4** has it with local labels; Met(X) §6.3: "the first-class handler names of Koka offer no extra expressiveness over the second-class local labels of Met(X)" [relayed, [V] in P2 note].

### 3.3 Handler-state exclusivity (two `&mut` from one handler)

The property (survey A5(b)): borrows passed down through `resume` must end before the computation needs the same handler state again; "Two `&mut` obtained from one handler is then a lifetime error". Ante designs it and does not enforce it (probe `q4`, `ante-deep-dive.md`). [local]

- **O2** gives it as B6 directly: the handler lends `cap : Mut 'h S`, an operation reborrows `cap`, and an answer borrowed from the state is a reborrow of `cap` that ends before the next use of `cap`. This is survey A5's "let your existing checker do the work", and HandlersAsBorrows' encoding. The other side of the same coin: a stateful capability captured by two closures at once is refused (`twoBlocks_refused`), which System C accepts because "exclusivity comes from sequential control, not uniqueness". SecondClass P5 types System C's program with the state as the handler's parameter behind a control operation [checker].
- **O1** carries no lifetime for the handler, so an answer borrowed from handler state needs a separate mechanism: the handler site opens a lifetime (OQ-3), and answers are borrows at it. At that point the row element is effectively a lend, which is O3.
- **O3** as O2: the element's lifetime is the handler's lend.
- **O4**: the modal layer does not address it.

### 3.4 Tier 2: lends across a suspension

Tier 2 is a suspended computation holding lends (BRIEF §5; I2, OQ-9). The borrow side must know, at a stop, which lends span it.

- **O1 hides it.** A row says a callback may perform `Yield`; it does not say which lends are open when it does. Today's kernel answers by refusing every span (T1 conjunct 40, `↭` conjunct 37), and the surface rejects a resuming operation inside a borrow block. A tier-2 O1 must recover the spanning lends from the borrow derivation, not from the type.
- **O2 makes it explicit.** A continuation or stored callback is a value whose type is bounded by the lifetime of every lend it holds; survey A4's typing proposal is `Cont<'k, A, R>` with `'k` "outlived by every loan live at the capture point and by every enclosing handler it uses". `resume` second-class means the continuation is stack-placed and cannot outlive its lends. The bound is a lifetime, so it fits BoLo's `[]I` box (`[@a]`), which already crosses scopes for codata (`d_box_codata`, CoeffectsStrict §6 test case 2).
- **O3 makes it explicit** in the row's lifetime component; `Rw.life` is the meet.
- **O4**: not addressed.

The freeze-as-binder reading (resume instantiates bound lifetimes and instances fresh, `foundations/freeze-binder.md`) needs the lifetimes to be *in* the suspension's type to be stated. O2 and O3 put them there; O1 does not. [synthesis]

### 3.5 Inference and readability

- **O1:** principal inference by row unification (Koka, Links). Types mention `ε` in every HOF; Frank and Koka hide a single variable. Two independently polymorphic callbacks need `ρ₁ ⊙ ρ₂`, which one-tail rows lack (Yoshioka Table 2). A bound on `ε` is one more annotation.
- **O2:** called-only callbacks need no effect annotation at all. System Ξ §1.3 [read]: "Users never have to deal with parametric effect polymorphism as the feature simply does not exist." The cost is expressive, not notational: System C §2.3 [read]: "we cannot require function parameters to not use certain effects!" For us that matters for APIs that need well-bracketed control (survey A7, §1.9 item 7: "APIs that rely on well-bracketed control take closures whose effect bound excludes `once` and `many`"); O2 cannot state such a bound without O2-g. Stored callbacks carry a capture set or lifetime, which Rust programmers already read (`Box<dyn Fn + 'a>`).
- **O3:** the kernel types are heavier than either; the surface can be O2's (O3-surface).
- **O4:** Met §1 [read]: "Met works smoothly with pure first-class higher-order functions, which require neither hidden effect variables nor extra annotations"; §8.2: "compared to Koka, Metl provides more succinct types without effect variables for a rich class of programs. Compared to Effekt, Metl supports first-class functions smoothly with no extra restrictions or capability variables in types." Boxing and unboxing are inferred by bidirectional typing in Metl (§7) [read].

### 3.6 The effect / coeffect / scope axes

CoeffectsStrict §2.4 and §4 [local]: "a `Mut` capability is the **effect** `write`, presented in state-passing form" (Møgelberg–Staton Thm 8.1, Thm 4.3); "An `Imm` demand, by contrast, is a genuine coeffect: the reader comonad"; "Borrows are an instance of none of the four … Scope is its own axis." Placed on the options:

| axis | O1 | O2 | O3 | O4 |
|---|---|---|---|---|
| effect (operations, class) | the row on `F` | the `Mut` capability in `Γ`, state-passing; class not in a type (O2-g adds it) | the row's instances and bounds | the effect structure `X` |
| coeffect | not used | an `Imm` capability (a read-only handler) is a reader demand | as O2 | Met: "Modalities are monotone total functions on effect contexts" (§4.3) [read]: a context operation, coeffect-shaped, carrying effect information [synthesis] |
| scope | lifetimes, separately from effects | the capability's lifetime: effect and scope ride on one variable | the row's lifetime component | not addressed |

So O1 keeps the three axes on three carriers; O2 puts effect and scope on one carrier (the borrowed capability) and coeffects on `Imm` capabilities; O3 puts effect and scope into one row element. The CoeffectsStrict verdict that scope "meets [the equational axes] only through the Fundamental Property" is what HandlersAsBorrows instantiates: effect safety came from the FP, not from a law.

### 3.7 Proof burden, given what exists

| | exists | to build |
|---|---|---|
| O1 | Core's per-operation layers, `fundamentalC`, `adequacyD`, `effSafe_tier1`; targets' `orowRF` algebra with `rowAlgSafe_orowRF` | row variables in `CDerives` and the relation: "two `CTy` formers", "a row environment `η : Nat → OpTab`. Every `cC`/`vC`/`SemV` statement in `Core/` changes signature", "a semantic substitution lemma over every former", `Loop_ε` positivity at an abstract row (`docs/effect-polymorphism.md` §4, Option 1); the bridges `rowAlgebra_ourInst`, `effSafe_of_core`; abstraction machinery (site freshness, renamed instances); the handler lifetime for answers (OQ-3); tier 2 entirely on the borrow side |
| O2 | HandlersAsBorrows (PAPER: `translate_typed`, `effect_safety`, `handle_is_shift`); SecondClass (`handleAt_compatC`, Core σ=[]); `[]I` at every value type, `d_box_codata`; Core's `withbor` and the unwinding borrow constants | the CBPV form of HandlersAsBorrows; control operations as lends (exactly tier 2's stop change, OQ-8/9); block parameters (FnMut-shaped); the box/outlives rule at `U C` (T2, OQ-28); aliasing (accept the refusal, or state behind control); the class grade if O2-g |
| O3 | EffModelRel (SIB): rows of `(instance, lifetime)`, `safety`, `safety_obs`, handler laws, `fwd_id`, `hnd_sim`; EffModel's bounds | everything O2 needs at Core, plus the row algebra over instances; the bridge from SIB to Core, which does not exist |
| O4 | nothing at Core | a modal kernel; the borrow interaction is unaddressed by the literature |

### 3.8 Ergonomics: implicit versus explicit passing, and IO bundles

- **IO as a bundle** (memory and SPEC: a separate linear capability per effect, `main` receives the bundle, "`main` may have ambient IO as surface sugar … elaborated to explicit capabilities; no other function gets it"). Under O2 this is the native shape: a bundle is a record of capabilities and the platform supplies it to `main`. Under O1 the bundle is a set of labels in `main`'s row with the platform as the outermost handler; the record-of-capabilities reading is then a second view (`CTy.eff` layers vs. `Mut 'a Output`). Today the kernel already does IO by capability passing (CoeffectsStrict §8: "I/O stays capability-passing. By Møgelberg–Staton that *is* the algebraic effect").
- **Implicit passing.** Effekt passes capabilities implicitly for effects written in a signature: System Ξ §3.2.2, rule Def [read]: effects written in a block's signature become capability parameters, and "all capabilities that are not part of the annotated type need to be provided by the context at the definition site of the block … the block will close over the free effects"; the user never writes the capability argument. Capturing Types §2.6 [read]: "the universal capability cap should conceptually only be available as a parameter to the main program" — the same shape as our "ambient only in main". Explicit passing is the alternative; a surface can elaborate one to the other. Ante's warning against second-class references: "Continuing with this though means dividing the language into two colors: second-class and non-second-class … you'd need another separate map function which takes its argument by reference instead of by value" (`ante-deep-dive.md` §4, quoting Ante's ideas page). In BoLo the split is already lifetime polymorphism over `&'a`, not a second function: a borrow is a lifetime-polymorphic value, and second-class is the case where the lifetime is the frame's. [synthesis]

---

## 4. The no-colouring test program in each style

The program is E1 (`Targets/A/Programs.lean`, `hof`, `threeUses`, `usesS`): `f = λg. g ()`, used three times, with a pure callback, a failing one handled to a sum, and a suspending one handled by a scheduler. Written here as `map` over a borrowed list, since that is the shape that matters for borrows. Syntax is illustrative only.

### 4.1 O1, rows

```
fn map[ε](xs: &List<A>, g: fn(&A) -> B / ε) -> List<B> / ε

map(xs, |x| x + 1)                                   // ε := ⟨⟩
with to_result { map(xs, |x| if *x == 0 { raise Fail } else { 10 / *x }) }   // ε := ⟨Fail⟩
with scheduler { map(xs, |x| { yield(); *x }) }      // ε := ⟨Wait⟩
```

**Lowering.** Three instances keyed by `(map, profile(ε))`: pure (a loop of direct calls), abortive (a branch after each call, landing pad dropping the partial output list), suspending (`map`'s loop becomes a state machine whose state holds the index, the partial list and the lend of `xs`). The suspending instance holds a lend of `xs` across `yield`: tier 2. The row `⟨Wait⟩` does not say so; the borrow side must find it. With `ε` bounded (`ε : abortive`) a shared body could serve the first two without a copy.

### 4.2 O2, capabilities as borrows

```
fn map(xs: &List<A>, g: {&A => B}) -> List<B>        // g is a block: second-class, no effect in the type

map(xs) { x => x + 1 }
try { map(xs) { x => if *x == 0 { fail.raise() } else { 10 / *x } } } with fail: Fail { … }
try { map(xs) { x => { wait.yield(); *x } } } with wait: Wait { … }   // scheduler
```

`fail` and `wait` are capabilities, lent by `try` at fresh lifetimes `'f` and `'w`; the blocks borrow them. **Lowering.** `map`'s type gives the lowering nothing; the call site does: the block literal and the lexically known handler of `fail` or `wait`. Specialising `map` at each block gives the same three bodies as O1. An un-specialised `map` must compile `g(x)` as a possible resumption point. A **stored** variant (E1′: the continuation kept after the scheduler's clause returns while `f` runs again) needs `box g : {&A => B} at 'w`: the box's lifetime bounds it, and under O2-lt that bound no longer says it suspends.

### 4.3 O3, rows of lends

```
fn map[ρ](xs: &'l List<A>, g: fn(&A) -> B / ρ) -> List<B> / ρ

with to_result as fail { map(xs, |x| …fail.raise()…) }   // ρ := {fail @ 'f : abort}
with scheduler as wait { map(xs, |x| …wait.yield()…) }   // ρ := {wait @ 'w : susp}
```

**Lowering.** As O1, with the class read from the element's bound and the instance known lexically (so a direct call, or EffModel's indirect call through the instance when not specialised). The suspending instance's state record holds `xs : &'l`; a stored suspension's type is bounded by `'l ⊓ 'w` (`Rw.life`), so the span is visible in the type.

### 4.4 O4, modal

```
map : [](List A -> (A -> B) -> List B)               // no effect variable; callbacks inherit the ambient effect
```

This is Met's own `iter : []((Int → 1) → List Int → 1)` (§2.2) [read]; the failing and suspending uses are `iter` applied at ambient contexts `Fail` and `Gen Int` by subeffecting. A stored suspension (E1′) needs an absolute modality at the stored type, `[Wait]`, or an effect variable if it is used in a context other than the ambient one (§2.10). **Lowering.** At each call the ambient context is `·`, `Fail` or `Wait`; the class follows as in O1.

---

## 5. The menu, with trade-offs

**O1: rows of labels, with a bounded row variable.**
- *Buys:* principal inference; the class in the HOF's type via the bound; the least effect-safety work, already proved at the algebra; matches the built toolchain's specialisation.
- *Costs:* row variables in the kernel relation (not built); accidental handling needs a separate mechanism; handler-state borrows need a handler lifetime that rows do not carry; tier 2's spanning lends are invisible to the type, so the whole of tier 2 is on the borrow side; one tail variable.

**O2: capabilities as borrows.**
- *Buys:* no effect annotation on called-only callbacks; effect safety, abstraction, handler-state exclusivity and the tier-2 span all from the borrow calculus (B6, B7); handler extents are lifetimes (Müller et al.); IO bundles are native.
- *Costs:* the class is not in any type, so specialisation keys on values and the un-specialised fallback is the worst class; stored callbacks need the `U C` outlives rule (T2) and, under lifetime bounds, lose the class; control operations must become lends, which is the tier-2 stop change itself; aliased stateful capabilities refused unless state goes behind control; a parameter cannot be required not to use an effect ("we cannot require function parameters to not use certain effects!", System C §2.3), so well-bracketed APIs (survey A7) need O2-g; "contextual purity does not imply purity" (System Ξ §1.5); HandlersAsBorrows is at PAPER and answering-only.

**O2-g: O2 plus a class grade on blocks and boxes.**
- *Buys:* restores O1's information to O2 with one grade (three values, the targets' `RowClass`).
- *Costs:* a grade former and its subsumption; it is an effect annotation again, though only a class, not a set of labels.

**O3: rows of lends.**
- *Buys:* every carrier at once: class, instance, lifetime; abstraction by construction; the tier-2 span in the type; the closest model is proved (SIB).
- *Costs:* the heaviest kernel types; the SIB proofs have no bridge to Core; the lifetime component is untested beyond scope in the model; both a row algebra and outlives must be proved.

**O3-surface: O2 for the programmer, O3 in the kernel.**
- *Buys:* O2's annotation-free surface with O3's information for the lowering and the checker; the elaborator infers the row of lends from lexical binding.
- *Costs:* an elaboration whose correctness is one more lemma; two views of one thing to keep in step.

**O4: modal effects as the common encoding.**
- *Buys:* one metatheory parameterised by the effect structure; both rows and System C encode, preserving types and semantics (Met(X) Thms 4.1, 4.2, 5.1, 5.2, forward simulation); annotation-light HOFs.
- *Costs:* a different kernel; no borrow interaction in the literature; paper proofs only; the borrow-side questions (exclusivity, tier 2) remain to be solved inside it.

---

## 6. Inventory

- **Unspent hypotheses and unused results we have:** targets' `RowCon.cls` (a class bound on row variables, which is exactly the lowering's profile and is not consumed by any lowering statement); EffModel's `inst E b` bound; `[]I` at codata (`d_box_codata`) as the box for stored callbacks; `handleAt_compatC` (handling at a run-time name).
- **Untranscribed literature results in the run-up:** System C's Lemma 4 and Cor 9 have no Core counterpart; System Ξ's effect safety has a PAPER counterpart only (`effect_safety`); Met(X)'s encodings have none; Müller et al.'s Thm 3.6/3.7 (capabilities to regions) have none.
- **Not checked:** whether `RowCon.cls` and EffModel's `susp` coincide; whether a class grade on boxes is sound with `[]I` (no Lean built); whether O3's lifetime component can replace T1's syntactic test (EffModel open problem 4).

---

## Sources

Read for this note (full text; [read] items above):
- Brachthäuser, Schuster, Ostermann. *Effects as Capabilities: Effect Handlers and Lightweight Effect Polymorphism.* OOPSLA 2020, doi 10.1145/3428194. Read as the extended TR "Effekt: Lightweight Effect Polymorphism for Handlers": https://se.cs.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf (TR numbering: Def 3, Thms 4–6).
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki. *Effects, Capabilities, and Boxes.* OOPSLA 2022, doi 10.1145/3527320. Extended TR: https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects.pdf (Thm 3, Lemma 4, Thm 5, Lemma 6, Def 8, Cor 9).
- Schuster, Brachthäuser, Ostermann. *Compiling Effect Handlers in Capability-Passing Style.* ICFP 2020, doi 10.1145/3408975. https://se.cs.uni-tuebingen.de/publications/schuster20capability.pdf (Thm 5.1, Cor 5.2, Thms 5.3–5.5).
- Schuster, Brachthäuser, Ostermann. *Zero-cost Effect Handlers by Staging.* TR, Tübingen, 2019. https://pl.cs.uni-tuebingen.de/publications/schuster19zero.pdf (printed Theorems 1–5).
- Boruch-Gruszecki, Odersky, Lee, Lhoták, Brachthäuser. *Capturing Types.* TOPLAS 45(4), 2023, doi 10.1145/3618003. https://plg.uwaterloo.ca/~olhotak/pubs/toplas23.pdf (Thms 4.6, 4.8, Lemmas 4.11–4.13, Thm 4.14, §7). Preprint arXiv 2207.03402 ("Scoped Capabilities for Polymorphic Effects").
- Xu, Boruch-Gruszecki, Odersky. *Degrees of Separation.* arXiv 2308.07474v2. https://arxiv.org/pdf/2308.07474
- Müller, Schuster, Starup, Ostermann, Brachthäuser. *From Capabilities to Regions.* OOPSLA 2023, doi 10.1145/3622831. https://pure.au.dk/ws/files/404551780/3622831.pdf (Lemma 3.5, Thms 3.1, 3.3, 3.6, 3.7).
- Müller, Schuster, Brachthäuser, Ostermann. *Back to Direct Style: Typed and Tight.* OOPSLA 2023. https://pl.cs.uni-tuebingen.de/publications/mueller23continuation.pdf (Thms 15, 17, Cor 20). Not used above: it relates CPS and direct style syntactically and does not choose by effect type.
- Ma, Ge, Lee, Zhang. *Lexical Effect Handlers, Directly.* OOPSLA 2024. https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf (Thms 1, 2; §5, §7.2).
- Tang, White, Dolan, Hillerström, Lindley, Lorenzen. *Modal Effect Types.* OOPSLA 2025. arXiv 2407.11816v3 (Lemma 5.2, Thms 4.3, 4.4; §§2.2, 2.10, 8.1, 8.2).
- Tang, Lindley. *Rows and Capabilities as Modal Effects.* POPL 2026. arXiv 2507.10301v2 (Defs 3.1–3.6, Thms 3.7, 3.8, 4.1, 4.2, 5.1, 5.2; §§2.4, 2.5.4, 6.3, 6.4, 7).
- Lindley, McBride, McLaughlin. *Do be do be do.* POPL 2017. arXiv 1611.09259v2.
- Leijen. *Koka: Programming with Row-polymorphic Effect Types.* MSFP 2014. arXiv 1406.2061v1.
- Leijen. *Type Directed Compilation of Row-Typed Algebraic Effects.* MSR-TR-2016-29 (the POPL 2017 paper's TR; POPL camera-ready not compared). https://www.microsoft.com/en-us/research/wp-content/uploads/2016/08/algeff-tr-2016-1.pdf (§5.1.1, §5.3, Fig. 7).
- Xie, Brachthäuser, Hillerström, Schuster, Leijen. *Effect Handlers, Evidently.* ICFP 2020. https://xnning.github.io/papers/icfp20evidently.pdf (Thms 4–8, 10, 11; §§2.2, 6.2–6.4).
- Xie, Leijen. *Generalized Evidence Passing for Effect Handlers.* ICFP 2021. https://xnning.github.io/papers/multip.pdf (§§2.5, 2.6, 2.10, 2.11).
- Xie, Cong, Ikemori, Leijen. *First-class Names for Effect Handlers.* OOPSLA 2022. https://xnning.github.io/papers/oopsla22namedh.pdf (Thms 4.1, 4.3, 4.4).
- Zhang, Myers. *Abstraction-Safe Effect Handlers via Tunneling.* POPL 2019. https://cs.uwaterloo.ca/~yizhou/papers/abseff-popl2019.pdf (Thms 1–3, Lemmas 5, 6).
- Karachalias, Koprivec, Pretnar, Schrijvers. *Efficient Compilation of Algebraic Effect Handlers.* OOPSLA 2021. https://lirias.kuleuven.be/retrieve/656121

Relayed from [P2](p2-effect-safety.md) (marked [V] there): Yoshioka, Sekiyama, Igarashi, ICFP 2024 (Defs 3.5, 5.1, 7.1, 7.6; Table 2); Hillerström, Lindley, TyDe 2016.

Not read: the ACM camera-ready versions of the two OOPSLA Effekt papers (their numbering may differ from the TRs'); Effekt's current compiler backends.

Local:
- `~/repos/borrow-core/docs/effects-state/BRIEF.md` §1, §3, §5, §6
- `~/repos/borrow-core/SPEC.md` §14 (*Higher-order functions: specialization at the callback's type*), §18, §19 (*Lowering*)
- `~/repos/borrow-core/docs/effect-polymorphism.md` §0, §4, §5, §10
- `~/repos/borrow-core/docs/effect-model.md` §0, §1.2, §6, §9.1
- `~/repos/borrow-core/docs/second-class-and-system-c.md` §0
- `~/repos/borrow-core/experiments/HandlersAsBorrows/README.md` §3, §5
- `~/repos/borrow-core/experiments/CoeffectsStrict/README.md` §2.4, §4, §6, §8
- `~/repos/borrow-core/experiments/SecondClass/README.md`
- `~/repos/borrow-core/research/effects/ante-deep-dive.md`
- `~/repos/borrow-core/Core/Types.lean:92`
- `experiments/Targets/Targets/Base/Rows.lean`, `A/Expressiveness.lean`, `A/Programs.lean`, `A/Lowering.lean`
- this notebook: [P2](p2-effect-safety.md), [Second-class values](../foundations/second-class.md), [Freeze as a binder](../foundations/freeze-binder.md), [P10](../properties/exclusivity.md), [P13](../properties/zero-cost.md), `survey.md` A2, A4, A5, B1, §1.8, §2 P6–P8
