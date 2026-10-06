# Prior art: P12, abstraction safety

This note surveys the literature on one System A property, [P12](../properties/abstraction.md). It ends in a menu of options with trade-offs and does not recommend one. The property has four parts:
- **no accidental handling**: a handler cannot intercept the effects of code it was handed abstractly;
- **effect encapsulation**: effects handled inside a computation are invisible outside it;
- **handler-state representation independence**: two handlers of one interface, with differently represented state, cannot be told apart by their clients;
- **instance generativity**: each run of a handler site is a distinct instance.

The options are stated against the five existing menus: [P2](p2-effect-safety.md) (R1–R6, S-a–S-g), [rows vs capabilities](rows-vs-capabilities.md) (O1–O4), [I2](i2-capture-resume.md) (M0–M3, T1–T4), [P10/P9](p10-p9-exclusivity-lifetimes.md) (X.1–X.7, L.1–L.7) and [P8/P5](p8-p5-linearity-drop.md) (8.x, 5.x, X.x, F.x).

**Marks.**
- **[read]**: I read the statement in the primary source's full text for this note, and the quote is copied from it.
- **[relayed]**: taken from another notebook page that marks it [read] or [V], or from a secondary source.
- **[unverified]**: from memory or not checked.
- **[local]**: read off this repository's code or documents.
- **[synthesis]**: my reading, not a source's claim.

Theorem numbers follow the version named in the sources list.

**A name collision.** Decision 57's site freshness is called "R3" in `docs/effect-polymorphism.md`. The P2 menu's **R3** is Rémy rows with lacks constraints. In this note, site freshness is **SF**, and R3 always means the P2 menu's row.

---

## 0. The menu

The menu has three independent axes:
- **what is stated** (AS0–AS5);
- **what mechanism realises it** (N1–N8);
- **how it is proved** (PR-a to PR-d).

There is also one scope question for the user (§0.4).

### 0.1 What is stated

| | statement | unary or binary | shape | buys | cost | ours today |
|---|---|---|---|---|---|---|
| **AS0** | **E6 `Tunnel`** (expressiveness) | unary | one typing of `fwrap` serves a callback at every row without `fwrap`'s own label (`PolyUseLacks`); the callback's raise of another label runs through (`CallsThrough`, `RunsTo`) | a lower bound with teeth: an instance without effect polymorphism fails it (`not_tunnel_of_monoCallback`, PROVED at every instance) | none beyond E1's polymorphism | **in done**; open at our instance |
| **AS1** | **Scope (escape)**: a handler's name, label or capability never occurs outside the extent that binds it | unary | Zhang–Myers' `[t-down]` side condition; System C's "labels are delimited"; BoLo's 6.60 at a capability (`escape_refused`) | the **safety** half: no operation reaches a dead handler, and no stale label reaches a reused one | under static names, `[handle]`'s `n ∉ Σ` is already this; under generative names or capabilities it is a confinement rule (SPEC §19's T2 former) or B7 | `[handle]`'s `n ∉ Σ` (Core); SF decided, not built |
| **AS2** | **Resolution**: every operation reaches the handler lexically in scope where the code performing it was written | unary, on runs | a provenance-instrumented run invariant, or a "uniqueness of resolution" lemma (`docs/effect-polymorphism.md` §9.2) | states "no accidental handling" without a binary relation; it is what static dispatch in the lowering (P13) needs | an instrumentation (site tags on frames and performs), and an erasure lemma | not stated |
| **AS3** | **Tunnelling, binary** (Zhang–Myers Example 1) | binary | `fwrap g ≡ g` at every row without `li` (A₂'s `TunnelBin`); over Core, `f c ≡ handle_n[c] (f (perform n))` for `f` free of `hnd n` (`Instance/Binary.lean`'s `Tunnel`) | the literature's statement of abstraction safety; it justifies erasing a handler that never catches | a binary relation (§0.3) | **stated, open**, out of the first pass |
| **AS4** | **Instance parametricity** (Staton's `ν` laws; `ν x. handleAt x H M ≡ M`) | binary | a handler of a fresh instance around code that cannot name it is invisible | AS3 for generative instances, with no type abstraction over effects | needs `ν` (N5) and a binary relation with name bijections | **PROVED in SIB** (`no_accidental_handling`, `EffModelRel/Laws.lean`); no bridge |
| **AS5** | **Representation independence and encapsulation** of handler state (`RepInd`, `Encap`) | binary | Mitchell-style: two handlers related by an admissible relation on their state give equivalent handled computations (Cambria Cor. 4.10; ADR 2009) | a library may change a handler's state representation without breaking clients | a binary relation over the world, including lent state | `RepInd := Hiding`, `Encap`: **stated, open** (`Instance/Binary.lean`) |

### 0.2 What realises it

| | mechanism | AS1 (safety half) | AS2/AS3 (no capture) | instances | costs | literature | relation to the other menus |
|---|---|---|---|---|---|---|---|
| **N1** | **Static per-site names + SF + renamed instances; recursion through a site rejected** (decision 57) | `[handle]`'s `n ∉ Σ`, plus SF (`n` free in no type outside its site) | by construction for non-recursive sites | one static name per site; re-entry meets the nearest instance of the name (SPEC §19) | rejects recursion through a site (`corpus/reject/rec-through-site.bc`); copies per name assignment (or a renaming lemma) | Zhang–Myers' unique labels ("Labels bound by different -terms are assumed to be unique"); Effekt's lexical resolution | **requires** P2 R1 or R3, rows O1-a; **favours** I2's T3 without an instance half; **excludes** nothing |
| **N2** | **N1 + lacks constraints on row variables** | as N1 | `n ∉ Σ` survives instantiating `ρ`: E6's `PolyUseLacks` becomes a kinding fact | as N1 | `RowCon` gains a lacks set | Links (Hillerström–Lindley) [relayed] | **requires** P2 R3; **favours** AS0 at our instance (the schema and the kernel rule coincide) |
| **N3** | **Mask / lift / inject / adaptors** | typed; unchanged | by programmer annotation: the HOF masks its own label around the callback | dynamic, by operation name; shadowing counted | **requires** scoped rows and Yoshioka's condition (3); the programmer must remember to mask; the "rather limited" first-match variant loses expressiveness (Biernacki 2018 §5) | Biernacki 2018 (lift); Leijen (inject); Convent et al. (adaptors) | **requires** P2 R4; **conflicts** with R1's first-match `∼` (P2 §5.1); **excludes** nothing else |
| **N4** | **Tunnelling with handler variables** | `[t-down]` | by construction: effects are sets of handler labels | lexical labels | handler polymorphism `Π h:F` in types; Zhang–Myers' types and effects on labels are restricted (Biernacki 2020 §9) | Zhang–Myers 2019 | close to O3 without lifetimes; **favours** rows-vs-caps O3 |
| **N5** | **Generative instances (`ν`)** | needs confinement: a stale label never meets a reused one (SPEC §19, *Why not generative names*) | AS4 holds (SIB) | a fresh runtime instance per handler entry | a machine step choosing names (changes A's S0/S4 machine shape); confinement (T2 former, #173); the label-reuse question under a leak-free heap | Biernacki 2020 (generative semantics); Staton 2013; EffModel `ν` | **requires** I2's T3 **with an instance half** (`FreezeBinder` has none, AGREE §5); **favours** P2 R4 or R6 local labels; unlocks L2 of `docs/second-class-and-system-c.md` |
| **N6** | **Lexical capabilities as borrows** (Ξ / System C; HandlersAsBorrows) | **B7 / 6.60** at the capability (`escape_refused`) | by construction: a block reaches only capabilities in scope where it was written (`atSucc`) | a capability per handler entry, its lifetime the handler's | boxes with lifetime bounds (OQ-28); control operations are not lends today (T1/`↭`); "we cannot require function parameters to not use certain effects!" (System C §2.3) | Brachthäuser et al. 2020, 2022; Müller et al. 2023 | **is** rows-vs-caps O2 and P2 R5; **requires** P10 L.1 and L.4; **favours** X.1 (handler-state exclusivity as B6) |
| **N7** | **Parametrized or existential handlers** (abstract state or parameter types) | as the base mechanism | AS5 by parametricity | parameter types instantiated by the handler | type abstraction over the state type in the kernel; Cambria's Cor. 4.13: no liveness analysis | Cambria 2026; Biernacki 2019 (existential effects) | **orthogonal** to N1–N6; in N6 the abstract state is the lent `Mut 'h S` with `S` abstract (P10 X.1) |
| **N8** | **Named handlers with rank-2 scope variables** | the scope variable cannot escape (`η ∉ ftv`) | by construction | first-class names, one per handler entry | rank-2 types in the kernel; the scope variable must index the effect (`vec^η`) | Xie et al. 2022 [relayed] | **is** rows-vs-caps O3's nearest published form; **favours** P10 L.4 (a) and L.6 (b) |

### 0.3 How it is proved

| | route | what it needs | buys | ours |
|---|---|---|---|---|
| **PR-a** | **By construction, unary only** | AS1 as an escape lemma, AS2 as a typing invariant | no binary relation; AS1 is B7 under N6 | `escape_refused` (PAPER); `handleAt_compatC` (Core σ=[]) |
| **PR-b** | **A binary logical relation over Core / W**, with T3 from its fundamental lemma (Zhang–Myers Thm 1 + Thm 3) | a binary BoLo relation: two runs, two heaps, related lends | AS3, AS5 and P11's binary laws from one relation (survey B1: "Build the logical relation once and reuse it for B3") | **none**: Core's relation is unary; named-only in RESTRUCTURE |
| **PR-c** | **A binary relation in the sibling calculus**, with a bridge | a bridge from EffModelRel to Core | AS4 already, and the handler laws | `no_accidental_handling`, `idem_nu`, `nu_nu`, `new_nu` (SIB); no bridge |
| **PR-d** | **An elaborator check only** (decision 57's SF) | none in Lean | the surface rejects escapes; the FP holds either way (`handle_compatC`) | decided; **no check found in `Frontend/`** (§6.2 (1)) |

### 0.4 The scope question for the user

**Is any binary form of P12 in scope?** The standing decision (2026-10-02) makes binary laws optional unless safety needs them. What this note finds, by reading only:

- **Effect safety (S2, S3) does not need the binary form.**
  - Decision 57: SF "is an abstraction property, not a safety one: the FP holds either way".
  - `handle_compatC` and `handleAt_compatC` take only freshness of the name. Biernacki 2020 says the same of its relation (§2.4).
- **System B's guarantees do not need it at tier 1.** They come from the FP and adequacy, which hold whichever handler catches an operation. The row types the answer.
  - The survey's worry (B1, "an intermediate handler you cannot see can capture a continuation that contains a callee's private `&mut` loans") is about dynamic handlers combined with per-function borrow reasoning.
  - In our kernel that capture is governed by T1/`↭` (I2) whatever the identity of the handler.
  - I have not checked whether tier 2's M1/M2 change this, and I have not verified that any obstruction is real.
- **The unary safety half, AS1, is needed under N5 and N6.**
  - Under N5, SPEC §19's stale-label argument is a safety argument: an operation could reach the wrong handler, with the wrong types.
  - Under N6, AS1 *is* B7.
- **Abstraction-dependent safety arises elsewhere.**
  - Static dispatch in the lowering (P13) needs AS2 (uniqueness of resolution), a unary fact.
  - A library proved sound against well-bracketed contexts (survey A7, P14) is a contextual statement. Whether it needs AS3 has not been checked.

So the question to put is: **AS0 + AS1 (+ AS2 for P13) as the safety-relevant core, with AS3–AS5 deferred; or AS3–AS5 brought in, which commits to PR-b or PR-c.**

---

## 1. Canonical statements

### 1.1 Zhang & Myers, *Abstraction-Safe Effect Handlers via Tunneling* (POPL 2019) [read]

**The problem** (§1):
> "suppose an implementation of map traverses the list using an iterator object. The iterator throws a NoSuchElement exception when it reaches the end of the list … If the client function f also happens to throw NoSuchElement, the implementation may handle—by accident—an effect it is not designed to handle."

**The principle**:
> "parametricity of effect polymorphism demands that an effect-polymorphic function should not make decisions based on the effect it is instantiated with. Yet the dynamic nature of algebraic effects runs afoul of this requirement".

**The fix**:
> "Algebraic effects can be handled only by handlers that are statically aware of them; otherwise, effects tunnel through handlers."

**Labels are static and assumed unique** (§4.1):
> "Labels bound by different -terms are assumed to be unique."

The evaluation of `[e-down-up]` relies on this:
> "since labels bound by -terms are assumed to be unique, the inner context K does not further nest any evaluation context ℓ [·] binding the same label" (§4.2).

**`[t-down]` is the scope rule (AS1)** (§4.3):
> "the label ℓ must not occur free in the result type T and effects e. Otherwise, ℓ could outlive its binding scope."

Here scope is a **safety** condition. Without it, the term evaluates to a handler "without a corresponding ℓ in the dynamic context".

**The theorems** (§5.4):
- **Theorem 1 (Parametricity, a.k.a. Fundamental Property, a.k.a. Abstraction Theorem):** "∆ | P | Γ | Ξ ⊢ t : [T]e ⇒ ∆ | P | Γ | Ξ ⊢ t ≼log t : [T]e".
- **Lemma 6 (Adequacy).**
- **Theorem 2 (Type Safety)**, which "falls out as an easy corollary of Adequacy and Parametricity".
- **Theorem 3 (Soundness):** "≼log ⇒ ≼ctx".

**Example 1** is AS3:
- `f : ∀α. (N → [N]α) → [N]α`, with `t1 = f [∅] (λx. x + x)` and `t2 = … f [h.lbl] (g h) …` under a handler that answers `x + x`.
- "this equivalence should apply to all possible (well-typed) implementations of f, so even if the implementation handles F internally, the clients are unable to make different observations … equivalence results of this kind ensure the correctness of compiler transformations that optimize away uses of effects".

**Example 2** is the same for handler polymorphism `Π h:F`.

**Mechanisation** (§5.5): Coq 8.7 on IxFree, about 4,000 + 4,200 lines. "in our Coq formalization the type and effects attached to a label must be closed."

**On generativity** (§8): "accidental handling can be avoided in SML, because SML exception types are generative … However, the type system does not ensure that accidental handling is avoided or that exceptions are handled at all."

### 1.2 Biernacki, Piróg, Polesiuk & Sieczkowski, *Handle with Care* (POPL 2018) [read]

**Row-based dynamic handlers are parametric.** Accidental handling shows up as a *less polymorphic type*, not as a failure of parametricity (Example 2.4). The attempted `f_cnt` handles the callback's `tick`:
> "Surprisingly, we cannot break parametricity this way: the function f_cnt has type ∀α.(τ1 →⟨T|α⟩ τ2) →α int, so it is authorised to handle effect T of д. If we tried to give f_cnt a more polymorphic type ∀α.(τ1 →α τ2) →α int, we would fail, as we cannot coerce α to ⟨T | α⟩ … This problem can be solved by guarding д x by a lift construct".

So in a row system, abstraction safety is the **expressiveness** question "can a HOF that handles `T` internally still be typed `∀α` over its callback?". That is AS0's shape. [synthesis]

**The lift construct**: "which dynamically creates a new occurrence of a particular effect l in the type, pushing the original occurrences deeper in the row" (§1).

**The theorems**:
- Theorem 8 (fundamental);
- Theorem 9 (type-soundness);
- Theorem 10 (soundness), with a step-indexed relation, mechanised in Coq.

**On Leijen's inject** (§5): "this operator is explicitly discarded from theoretical considerations, and little observation of its role in providing robust parametricity is made."

### 1.3 Biernacki et al., *Abstracting Algebraic Effects* (POPL 2019) [read: author preprint, numbering may differ from the ACM version]

**Two mechanisms**:
> "existential effects (which hide the details of a particular effect from the user) and local effects (which guarantee that no code coming from the outside can interfere with a given effect) … the dynamic nature of handlers is kept in check by typed runtime coercions."

**The example** (§1.2): an abstract `E := Reader Int` from a module "should be treated as fresh with respect to all other effects", and erasing types gives 10 where 6 is intended.

**What it proves**: Theorem 2.7 (Type Soundness), with progress and preservation (Lemmas 2.2–2.6). I found **no parametricity or contextual-equivalence theorem** in the preprint: grep for "parametricity", "logical relation" and "contextual equiv" returned nothing.

So this paper realises N7 for effects at the level of safety only. The abstraction claim is by design, not a theorem. [read; absence by search]

### 1.4 Biernacki et al., *Binders by Day, Labels by Night* (POPL 2020) [read]

Instances are **lexically scoped variables bound by handlers**. There are two semantics:
- **open**: reduction under binders;
- **generative**: "when a handler is encountered in an evaluation position, we pick a globally fresh runtime instance and substitute it for the instance variable" (§5, Fig. 5, rule with `fresh(l)`).

**Why the open semantics fails with polymorphic operations**: "Note how 𝑏 has escaped its lexical scope … Note that the use of resumptions is crucial here: mere exceptions, which may not use the resumption, would never lead to such a problem" (§4).

**Generativity loses an invariant**: "we can duplicate resumptions, and thus handlers decorated with the same label — and we have no coercions or adaptors to distinguish them!" (§5).

**The theorems**:
- Theorem 1 (Fundamental);
- Theorem 2 (Type Soundness);
- Theorem 3 (Soundness: logical approximation entails contextual approximation);
- Theorems 4–5 (the two semantics agree on closed pure programs, under the restriction "disallowing polymorphic operations").

**Freshness is used in exactly one place** (§6.1):
> "the only aspect of the proof where the generativity and the attendant freshness of the instance is important is the compatibility of the inference rule for the handle construct. There, it is used to enforce the fact that the runtime instance picked for the instance variable bound by the handler is distinct from any others that could appear in the remainder of the effect, 𝜀."

This is the shape of our `handleAt_compatC` ("The name enters only through freshness"). [synthesis]

**On Zhang–Myers** (§9): "Our results subsume their solution … their effect signatures can be neither effectful nor polymorphic … In the Coq formalisation of their results, however, Zhang and Myers use a semantics that is closely related to our generative semantics … we fear that this means the formalisation is not adequate with respect to the presentation in the paper – although by itself this does not invalidate the results as presented."

### 1.5 Convent, Lindley, McBride & McLaughlin, *Doo Bee Doo Bee Doo* (JFP 2020; preprint of 16 January 2020) [read]

They call accidental handling **effect pollution**:
> "The bad handler has broken abstraction by leaking its interpretation for an empty list of states and revealing such details in the type of its second argument. We call this phenomenon effect pollution. To prevent such effect pollution we need a way of hiding intermediate effects so that external effects with the same name are not accidentally handled … a generalisation and adaptation of a construct variously called inject (Leijen, 2014, 2018) and lift (Biernacki et al., 2018) … which in this paper we call mask."

**Adaptors have run-time content**: "Dynamically, hiding an effect instance skips the nearest enclosing handler for the specified effect."

**What it proves**: Theorem 5 (Subject Reduction) and Theorem 7 (Type Soundness). No parametricity theorem.

### 1.6 Liell-Cock & Staton, *Cambria* (arXiv 2608.27798v1, 2026) [read]

Handler-state representation independence (AS5), by parametricity.

**The claim**: "Cambria is the first calculus with user-defined resource-allocating effects that guarantees, via parametricity, that client code cannot depend on how a handler represents its resources."

**The theorems**:
- Theorem 4.2 (Fundamental Theorem) and Theorem 4.9 (Adequacy), with a step-indexed binary relation.
- **Corollary 4.10** (representation independence): "Suppose that for every relational interpretation 𝜌 … there exists an admissible relation 𝑅 ∈ Rel such that (ℎ†1[𝛾1], ℎ†2[𝛾2]) ∈ ⟦𝐶 ⇒ 𝐷⟧≈𝜌[𝜓↦→𝑅]. Then (with 𝜎1, ℎ1 handle 𝑐) ≈ (with 𝜎2, ℎ2 handle 𝑐)."
- Theorem 4.12: allocating an unused reference is unobservable.
- **Corollary 4.13 (Vacuousness)**, with its consequence: "naive liveness detection and parametricity are incompatible … Reachability-based garbage collection for parametric local state is thus beyond the scope of this paper. Substructural typing, regions, and built-in reference effects remain possible alternatives".

**Its future work** names our property: "whether parameter abstraction offers an alternative to tunnelling [Zhang–Myers], preventing effect-polymorphic code from accidentally handling effects it is unaware of."

### 1.7 Ahmed, Dreyer & Rossberg, *State-Dependent Representation Independence* (POPL 2009) [read: abstract]

The abstract: "none allows one to prove representation independence results for generative ADTs — i.e., ADTs that both maintain some local state and define abstract types whose internal representations are dependent on that local state". The method is "a possible-worlds model in which relational interpretations of types are allowed to grow over time in a manner that is tightly coupled with changes to some local state", step-indexed.

A stateful handler of an abstract interface is exactly a generative ADT. AS5 at a handler whose state is a lent cell is SDRI at a borrow world. [synthesis]

### 1.8 Staton, instances; Pitts–Stark, freshness [relayed]

- Staton (LICS 2013), §IV–V: the laws `idem-ν`, `ν/ν`, `new-ν` and `ν/op`. These are relayed from `docs/effect-model.md`, which cites line numbers.
- EffModelRel proves `idem_nu`, `nu_nu`, `new_nu` and `no_accidental_handling` (SIB). `ν/op` is refuted at a multi-shot operation and open otherwise (O1 in `docs/effects-tr/07-laws.md`). [local]
- Pitts–Stark (HOOTS 1998), Lemma 1: determinism up to renaming of fresh names (relayed from the [I2 note](i2-capture-resume.md) §1.4).
- EffModelRel's worlds are partial bijections of names, with pending and garbage names (`World.lean`). That is the Pitts–Stark/Benton style. [local]

### 1.9 Lexical capabilities: System Ξ, System C, Lexa [read / relayed]

- **System Ξ and System C**: no accidental handling by lexical binding. Quoted [read] in the [rows-vs-capabilities note](rows-vs-capabilities.md) §1.2.
- **System C's Coq development proves soundness, not parametricity** (survey B1). [relayed]
- **Lexa** (Ma, Ge, Lee & Zhang, OOPSLA 2024) [read], §9: "Zhang and Myers [34] suggest that the loss of local reasoning with dynamically scoped effect handlers can be analogized to a loss of parametricity … Effect polymorphism, while syntactically heavier-weight than second-class values used by Zhang et al. [35], allows more programs to be expressed." On lowering: "When an effect is raised, the control transfer target is directly available—no run-time search is needed".
- **Xie et al. 2022, named handlers**: `withvec : ∀α μ. (∀η. () → ⟨vec^η | μ⟩ α) → μ α`, and "scope safety is subsumed by the type soundness theorem" (relayed [read] from the [P10/P9 note](p10-p9-exclusivity-lifetimes.md) §1.11).
- **Yoshioka et al.'s condition (3)**: masking/lift is sound only for algebras meeting it, and simple rows fail it (Thm 7.2 shape). Relayed from the [P2 note](p2-effect-safety.md) §1, R4.

---

## 2. How prior systems realise and prove it

| system | mechanism (§0.2) | statement (§0.1) | proof | mechanised |
|---|---|---|---|---|
| Zhang–Myers 2019 | N4 | AS1 (`[t-down]`), AS3 (Ex. 1, 2) | binary step-indexed biorthogonal relation | Coq (differs from the paper's semantics, per Biernacki 2020) |
| Zhang, Salvaneschi & Myers 2020 | N4, bidirectional | as Zhang–Myers [relayed: survey] | as Zhang–Myers | Coq [relayed] |
| Biernacki 2018 | N3 (lift), dynamic rows | parametricity of `∀α`; lift examples | binary step-indexed | Coq |
| Biernacki 2019 | N7 (existential effects), local effects, coercions | type soundness only | syntactic | not found |
| Biernacki 2020 | N5 + N8-like lexical instances | AS1, AS3-style parametricity under the generative semantics | Kripke step-indexed binary | Coq |
| Convent et al. 2020 | N3 (adaptors) | type soundness | syntactic | not found |
| System Ξ / C | N6 | AS1 (labels delimited) | progress and preservation | Coq (System C) [relayed] |
| Cambria 2026 | N7 | AS5 (Cor. 4.10) | binary step-indexed | not found in the text I read |
| EffModel(Rel) (ours, SIB) | N5 + instances in types | AS4, `ν` laws | binary, no step index, partial-bijection worlds | Lean |
| HandlersAsBorrows (ours, PAPER) | N6 for answering handlers | AS1 as `escape_refused` | the BoLo FP | Lean |
| Core today | N1, static names | `[handle]`'s `n ∉ Σ`; AS0 stated | unary FP | Lean (Core σ=[]) |

**Three patterns** [synthesis]:
1. **Every binary result rests on a binary logical relation built for that calculus.** None is relation-free. AS3–AS5 cost a binary relation, and nothing is cheaper.
2. **By-construction systems (N6) prove the unary half and stop.** System C proves soundness, not parametricity. "By construction" is an argument, not a theorem, until someone proves AS2 or AS3.
3. **Generativity costs a freshness argument, used only at `handle`'s compatibility** (Biernacki 2020 §6.1; our `handleAt_compatC`). The cost elsewhere is the machine step and confinement.

---

## 3. Pitfalls

1. **Static unique labels do not survive recursion through a site.**
   - Zhang–Myers *assume* label uniqueness. Biernacki 2020 notes their Coq semantics is generative instead.
   - Decision 57 rejects recursion through a site for the same reason (`rec-through-site.bc`). Generative names (#173) are the general fix.
2. **Generative names under memory reuse.** SPEC §19: a freed label reused by a new handler lets an escaped continuation reach the wrong handler.
   - In a leak-free heap (B4, B5), this is the label analogue of B5's location reuse and `BumpSim`. [synthesis]
3. **Mask is a burden on the programmer.**
   - Biernacki 2018's `f_cnt` is parametric but un-polymorphic until the author adds `[−]T`. The type rejects `∀α`; it does not warn.
   - Mask also needs Yoshioka's condition (3), which R1 fails.
4. **"Parametric" is not "abstraction-safe".** Row systems with dynamic handlers are parametric (Biernacki 2018). The property that fails is the *expressiveness* of polymorphic HOFs that handle internally, which is AS0's reading.
5. **Opening an effect** (Ante): "Rows merge equal effects … Accidental handling comes from merging equal effects" (`ante-deep-dive.md`). [relayed]
6. **Parametricity forbids liveness analysis** (Cambria Cor. 4.13). Handler-state cleanup must come from substructural typing, not reachability. Ours does: linearity (P8/P5).
7. **The safety half and the abstraction half are different properties.**
   - Zhang–Myers' `[t-down]` is safety (escape).
   - Their Thm 1 + Thm 3 is abstraction.
   - Conflating them makes P12 look either free (by construction) or expensive (binary). It is neither.

---

## 4. With borrows or lifetimes

- **What the literature has.**
  - The survey's analogy (B1) is "A fresh handler instance behaves like a fresh lifetime, and masking an effect behaves like a lifetime ending" (Lucassen–Gifford masking; Timany et al.'s `runST`). [relayed]
  - Müller et al. 2023 make a handler's scope a region (rows-vs-caps §1.2).
  - Xie et al. 2022 index an effect by a rank-2 scope variable.
  - None of these states a parametricity or representation-independence theorem in a calculus with lifetime-indexed exclusive borrows. My searches found none. [unverified as exhaustive]
- **Where we would be new.**
  1. **A binary logical relation for a borrow calculus** (PR-b). BoLo's relation is unary. Any AS3–AS5 over Core or W needs two runs related through lends, lifetimes and `↭`. I found no precedent. RustBelt is unary [relayed: P10/P9 note §1.14].
  2. **Instance generativity under a leak-free, reusing heap** (N5 with B5): the stale-label question of SPEC §19, stated as a theorem.
  3. **Representation independence of lent handler state** (AS5 under N6). The state is `Mut 'h S` (P10 X.1). Abstracting `S` is SDRI (§1.7) at a borrow world.
  4. **The instance half of freeze-as-binder** (I2's T3). Equivariance under instance bijections is EffModelRel's world shape. Combined with the ordered lifetime half, it has no precedent ([I2 note](i2-capture-resume.md) §1.4: Pitts 2016 leaves ordered names open).
- **What BoLo gives for free under N6.** AS1 is B7: `escape_refused`, "`[]I`'s premise … fails for any context that still holds the capability live" [local].

---

## 5. The menu, with trade-offs

### Statements

**AS0. E6, unary expressiveness (in done).**
- *Shape:* `Tunnel` over A, with `PolyUseLacks` and `CallsThrough`, at two distinct labels of one signature.
- *Cost:* E1's effect polymorphism; nothing else.
- *Buys:*
  - the program `fwrap` written once, serving a pure and a failing callback;
  - it has teeth against a monomorphic instance (`not_tunnel_of_monoCallback`);
  - by reading, it also has teeth against an instance whose labels are one per signature, as Koka's dynamic names are, since `ForLabels [sigExn, sigExn]` needs two distinct labels of one signature [synthesis].
- *Interactions:* any of N1–N8 meets it; N2 makes its quantifier a kinding rule. It needs no option from the other menus beyond E1's polymorphism (rows-vs-caps O1–O4 all supply it).
- *Evidence:* proved non-vacuous at every instance; open at ours (no `fwrap` typing at `J₁`, AGREE §1).

**AS1. Scope (escape), unary safety.**
- *Shape:*
  - under N1: SF, `n` free in no type outside its site, as a typing lemma;
  - under N5: "no reachable configuration performs on an instance whose handler has ended, or on a reused one";
  - under N6: B7 at capabilities.
- *Cost:*
  - N1: one lemma, already implied in the kernel by `[handle]`'s `n ∉ Σ` (for the row; SF adds `Γ₂` and the operation types);
  - N5: the confinement former (T2, #173);
  - N6: none beyond B7, plus a `U C` outlives rule for stored code (P10 L.3).
- *Buys:* the part of P12 that safety uses. Under N5 it is the guard on SPEC §19's stale-label scenario.
- *Interactions:* under N6 it is the same theorem as P9 (P10 L.1). Under N5 it rides on I2's T3 instance half and on B5.

**AS2. Resolution, unary on runs.**
- *Shape:* with site tags, every `perform` from code written under site `s` is caught by a frame of `s`, or the run is in `StopsIn`.
- *Cost:* an instrumented semantics and an erasure lemma (like P8's 8.2).
- *Buys:*
  - "no accidental handling" without a binary relation;
  - the lemma P13's static dispatch needs (SPEC §19 *Lowering*: "the handler is known statically");
  - it states "by construction" as a theorem for N1, N5, N6 and N8.
- *Interactions:* favours P13; independent of the P2 and rows choices. Under N1 with re-entry (`memo`), resolution is "nearest instance of the site", which SPEC §19 argues sound by "one protocol per name". AS2 makes that argument a statement.

**AS3. Tunnelling, binary.**
- *Shape:* A₂'s `TunnelBin`; `Instance/Binary.lean`'s `Tunnel` (`f` free of `hnd n`, `f c ≡ handle_n[c] (f (perform n))`).
- *Cost:* PR-b or PR-c.
- *Buys:* Zhang–Myers' guarantee itself; licence to erase a handler that never catches (a P13 optimisation); a client cannot observe a library's internal handlers.
- *Interactions:* it shares its relation with P11's binary laws (A₂ `HandlerLaws`), so the cost is shared if those are taken.

**AS4. Instance parametricity.**
- *Shape:* `ν x. handleAt x H M ≡ M` (T7.16).
- *Cost:* N5 in the kernel, and a binary relation with name bijections.
- *Buys:* AS3 for free at generative instances (the proof is `hnd_transparent`: a garbage name is never matched); Staton's laws.
- *Interactions:* **requires** N5. It shares world structure with I2's T3 instance half.

**AS5. Representation independence and encapsulation.**
- *Shape:* `RepInd := Hiding` at answering handlers; `Encap` (closed, fully handled, runner-equal computations are contextually equivalent); Cambria Cor. 4.10.
- *Cost:* PR-b; under N6, abstraction over the lent state's type.
- *Buys:* library evolution, which matters for the north-star operator's handler-provided platform bundles. That is a reading of the goals; no program in E1–E10 needs it.
- *Interactions:* under N6 it is about `Mut 'h S` (P10 X.1). Under O1 the handler has no lifetime (rows-vs-caps §3.3), so the state's relation lives outside the type.

### Mechanisms

N1–N8 are as in §0.2. Their links to the other menus, in one place:

| | P2 | rows vs caps | I2 | P10/P9 | P8/P5 |
|---|---|---|---|---|---|
| N1 | requires R1 (or R3) | O1-a | T3 without an instance half; M0–M3 unaffected | L.4 optional | none |
| N2 | requires R3 | O1-b | as N1 | as N1 | none |
| N3 | requires R4; conflicts with R1's `∼` | O1-c | none | L.6 (b)'s masking needs the same condition (3) | none |
| N4 | R5-like (sets of labels) | near O3 | none | L.4 | none |
| N5 | favours R4 or R6 (local labels) | O3 or O4 | requires T3 **with** an instance half; M1's fresh re-lend is its lifetime analogue | L.5 (resume under the capture's instances) | a machine step for `ν` changes S0/S4, as 8.3 would; reuse safety meets B5 |
| N6 | is R5 | is O2 | T2 (second-class resume) | requires L.1, L.4; gives X.1 | none |
| N7 | orthogonal | orthogonal; under O2 it abstracts `S` in `Mut 'h S` | none | X.1 | Cambria's leak is answered by linearity |
| N8 | R6-like | O3 | T3 with an instance half | L.4 (a), L.6 (b) | none |

### Proof routes

- **PR-a** pairs with AS0–AS2. It costs nothing binary.
- **PR-b** is the only route to AS3/AS5 over Core. Its cost is the largest item on any menu: a binary BoLo relation, where we would be new.
- **PR-c** gives AS4 now (SIB). The bridge to Core is unbuilt, and EffModel is a different calculus (no lifetimes beyond scope, rows of instances).
- **PR-d** is today's position. It asserts nothing in Lean.

---

## 6. Where our current target sits

### 6.1 Position

- **Statement:**
  - AS0 is in done: E6 `Tunnel`, stated, proved non-vacuous at every instance, and open at our instance.
  - AS3 and AS5 are stated as A₂ `Abstraction` and over Core (`Instance/Binary.lean`), out of the first pass.
  - AS1 holds in the kernel as `[handle]`'s `n ∉ Σ`.
  - AS2 and AS4 are not stated over Core. AS4 is proved in SIB.
- **Mechanism:** N1 by decision 57, rows R1 (`orowRF`). Recursion through a site is rejected.
- **Proof route:** PR-d for SF, decided. Binary T3 "from a binary fundamental lemma" is named-only (P12 chapter).

### 6.2 Observations from reading, with no Lean checks run

1. **SF is decided, not built.**
   - The P12 chapter says "Decision 57 site freshness is checked by the elaborator", and this brief says "elaborator-checked".
   - Decision 57 says SF "is checked by the elaborator only", meaning only there and not in the kernel.
   - `docs/Home.md` lists `effect-polymorphism.md` as "A design; nothing is built", and that file's header says "Nothing here is built".
   - A grep of `Frontend/` for an SF check found none. The elaborator does give each site a fresh static name (`freshSite`, `Frontend/Elab/Effects.lean`), and effectful callbacks (#161) are not built (`corpus/pending/yield-callback.bc`).
   - The chapter's wording should read "decided; to be checked by the elaborator".
2. **`Instance/Binary.lean`'s `Tunnel` takes `HndFree n` (syntactic) as its freshness.** That is SF read on `f`'s code, not on types. By reading it is adequate: `f` is closed and typed uniformly in `ρ`, so it cannot perform `n` itself. I have not checked whether `HndFree` misses a `hnd` reached through a value `f` returns.
3. **`Encap`'s premise already quantifies over every respecting runner.** Its content is that contexts cannot distinguish closed, fully handled computations beyond what runners see. It may be close to a context lemma rather than encapsulation in Timany et al.'s sense. I have not compared the two, and I have not verified that any gap is real.
4. **`FreezeBinder` has no instance half** (AGREE §5). Under N1 it needs none, since names are static. Under N5 or N8 it would.

### 6.3 Inventory

- **Untranscribed results in the run-up:**
  - Zhang–Myers Thm 1 and Lemma 5 (Congruency) have no counterpart over Core (PR-b).
  - Biernacki 2020's handle compatibility under freshness has a unary counterpart (`handleAt_compatC`), not a binary one.
  - Cambria Cor. 4.10 has no counterpart. `RepInd` is defined as `Hiding`, a T2 law, not as a relational premise on handler states.
  - `docs/effect-polymorphism.md` §9.2's renaming lemma and uniqueness of resolution (AS2) are unbuilt.
- **Proved evidence:**
  - `not_tunnel_of_monoCallback` (every instance);
  - `no_accidental_handling`, `hnd_transparent`, `idem_nu`, `nu_nu`, `new_nu` (SIB, `EffModelRel/Laws.lean`);
  - `escape_refused`, `capability_not_outlives` (PAPER, `HandlersAsBorrows/Safety.lean`);
  - `handleAt_compatC`, `fresh_exists` (Core σ=[], `SecondClass/Prompts.lean`).
- **Unused uniqueness results:** determinism of the machine (Core) and Pitts–Stark Lemma 1's renaming (TwoRun's `head_rename`, which does not build on main per the I2 note). AS2 under N1 would use the first.

---

## Sources

- Zhang, Myers. *Abstraction-Safe Effect Handlers via Tunneling.* PACMPL 3 (POPL 2019), Article 5. §1, §4.1–4.3, Thms 1–3, Lemmas 5–6, Examples 1–2, §5.5, §8. https://cs.uwaterloo.ca/~yizhou/papers/abseff-popl2019.pdf [read]
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Handle with Care: Relational Interpretation of Algebraic Effects and Handlers.* PACMPL 2 (POPL 2018), Article 8. §1, Example 2.4, Thms 8–10, §5. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl18.pdf [read]
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Abstracting Algebraic Effects.* PACMPL 3 (POPL 2019). Author preprint: abstract, §1.2, Lemmas 2.2–2.6, Thm 2.7. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl19.pdf [read]
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Binders by Day, Labels by Night.* PACMPL 4 (POPL 2020), Article 48. §1, §4, §5 (Fig. 5), §6.1 (Thms 1–3), §6.2 (Thms 4–5), §9. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl20.pdf [read]
- Convent, Lindley, McBride, McLaughlin. *Doo Bee Doo Bee Doo.* JFP 30, 2020. Preprint of 16 January 2020: §3 (mask, adaptors), Thms 5, 7, §9. https://homepages.inf.ed.ac.uk/slindley/papers/frankly-jfp.pdf [read]
- Liell-Cock, Staton. *Cambria: Resource Abstraction for Parametrized Algebraic Effects and Handlers.* arXiv 2608.27798v1, 2026. Abstract, §2.1, Thms 4.2, 4.9, Cor. 4.10, Thm 4.12, Cor. 4.13, §7. https://arxiv.org/pdf/2608.27798 [read]
- Ahmed, Dreyer, Rossberg. *State-Dependent Representation Independence.* POPL 2009. Abstract. https://www.khoury.northeastern.edu/home/amal/papers/sdri.pdf [read: abstract only]
- Ma, Ge, Lee, Zhang. *Lexical Effect Handlers, Directly.* PACMPL 8 (OOPSLA2 2024), Article 330. §1, §9. https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf [read]
- Brachthäuser et al. System Ξ (OOPSLA 2020), System C (OOPSLA 2022). [relayed: rows-vs-capabilities note §1.2]
- Xie, Cong, Ikemori, Leijen. *First-Class Names for Effect Handlers.* OOPSLA 2022 (MSR-TR-2021-10). [relayed: P10/P9 note §1.11]
- Yoshioka, Sekiyama, Igarashi. *Abstracting Effect Systems for Algebraic Effect Handlers.* arXiv 2404.16381. Def 5.1 (3), Thm 7.2. [relayed: P2 note]
- Staton. *Instances of Computational Effects.* LICS 2013, §IV–V. [relayed: `docs/effect-model.md`]
- Pitts, Stark. *Operational Reasoning for Functions with Local State.* HOOTS 1998, Lemma 1. [relayed: I2 note]
- Zhang, Salvaneschi, Myers. *Handling Bidirectional Control Flow.* OOPSLA 2020. [relayed: survey]
- Leijen. Koka `inject` (MSFP 2014) and `mask` (2018). [relayed: Biernacki 2018 §5; Convent et al. §3]
- Local:
  - `experiments/Targets/Targets/A/{Expressiveness,Binary,NonVacuity,System}.lean`, `Targets/Instance/Binary.lean`, `RESTRUCTURE.md` §1.6–1.7, `AGREE.md`;
  - borrow-core: `docs/decisions.md` (57, 62), `docs/effect-polymorphism.md` §0, §5.3, `SPEC.md` §19, `docs/second-class-and-system-c.md` §2.3–2.4, `docs/effects-tr/07-laws.md` (T7.16), `docs/Home.md`;
  - experiments: `EffModelRel/{Laws,World}.lean`, `HandlersAsBorrows/Safety.lean`, `SecondClass/Prompts.lean`;
  - corpus: `corpus/reject/rec-through-site.bc`;
  - research: `survey.md` B1, `research/effects/ante-deep-dive.md`.
