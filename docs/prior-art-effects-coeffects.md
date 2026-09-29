# Prior art: effects, coeffects, and borrowing

This is a literature survey. It maps what exists; it proposes no design and unifies nothing.

**Occasion.** Andrew Wagner, the first author of BoLo, replied to the remark that "borrowing and
effect handling are related quite deeply" with "I think so too! And you should check out
coeffects as well." Two spikes have already tried to build on that:

- `experiments/Coeffects/README.md` (branch `coeffects-spike`, PR #100);
- `experiments/CoeffectsStrict/README.md` (branch `coeffects-strict`, PR #101).

Those spikes read the core coeffect papers and the effect-handler foundations, and they drew
conclusions about the kernel. This survey does not repeat those analyses. It adds what they did not
cover: ownership and borrowing expressed with grades or coeffects (§3, the priority), capabilities
treated as coeffects (§5), and the BoLo authors' own line of work (§6). §§7–10 draw the
conclusions: what Wagner probably meant, the closest existing system, a reading list, and the
survey's limits.

**Reading tags.** These follow `docs/prior-art-sessions.md`.

- *(full)*: the whole text was read.
- *(sections)*: the named sections were read, and the rest skimmed.
- *(abstract)*: only the abstract or the first page was read.
- *(secondhand)*: the source is known only through another source, which is named.
- *(spike)*: the reading is the Coeffects or CoeffectsStrict spike's. This survey re-opened the PDF
  only to spot-check the quoted passage, if one is given.

Every PDF was fetched from the URL under **Sources** and converted with `pdftotext`. Titles,
authors and venues were checked against the paper's first page, the publisher's or conference's
page, or an author's publication list.

**Two Marshalls.** Brianna Marshall (Northeastern) is a BoLo author. D. Marshall of the Granule
project (Kent, now Royal Holloway) is a different person. Her current papers are published as
*Danielle* Marshall. ESOP 2022 and BoLo's bibliography print *Daniel* Marshall. This document uses
"Marshall–Orchard" for the Granule author.

---

## 1. Coeffects: the core

What each founding paper solves. The spikes read these; they are summarised here only so the later
sections can refer to them.

- **Petricek, Orchard, Mycroft**, *Coeffects: a calculus of context-dependent computation*, ICFP
  2014 *(spike; abstract and §1 re-read)*.
  - **Problem.** Static analysis of what a term needs from its context.
  - **The distinction.** It generalises the earlier ICALP 2013 system, which tracked only
    "whole-context properties where terms have just one coeffect". The abstract calls these
    **flat** coeffects, one annotation on the whole context. The new system adds **structural**
    coeffects, one annotation per variable.
    - Flat instances: implicit parameters, rebindable resources, platform versions.
    - Structural instances: bounded reuse, liveness, dataflow.
  - The semantics is by indexed comonads. The theorems are syntactic and equational.
- **Petricek**, *Context-aware programming languages*, PhD thesis, UCAM-CL-TR-906, 2017 *(spike;
  the `letdyn` passage re-read)*.
  - This is the long form of the flat and structural systems.
  - For implicit parameters, the binder `letdyn ?p = e₁ in e₂` "removes the bound parameter from
    the set of requirements".
- **Brunel, Gaboardi, Mazza, Zdancewic**, *A core quantitative coeffect calculus*, ESOP 2014
  *(spike; the co-handler passage re-read)*.
  - **Problem.** One calculus that is generic over a semiring of usage annotations: `!ᵣA` with
    promotion scaling the context by `r`.
  - Its "co-handlers" are context operations (e.g. `next` for dataflow). They are not scoped
    providers.
  - Soundness is by a realizability model with no heap.
- **Ghica, Smith**, *Bounded linear types in a resource semiring*, ESOP 2014 *(spike; §1
  spot-checked)*.
  - **Problem.** The same generalisation of bounded linear logic, reached from resource semirings.
  - It describes reusable resources "the typical example of which is memory, especially local
    (stack-allocated) memory".
- **Wood, Atkey**, *A Framework for Substructural Type Systems*, ESOP 2022 *(abstract)*.
  - A generic, mechanised metatheory (renaming, substitution) for simply typed syntaxes with
    semiring usage annotations.
  - Bianchini et al. (§3.4) credit this paper and McBride 2016 with observing that coeffect
    contexts form a *module* over the semiring.
- **Liepelt, Marshall, Orchard**, *Same Coeffect, Different Base: Connecting Two Dominant
  Approaches to Graded Types*, ICFP 2026, arXiv 2606.28042 *(abstract, §1)*.
  - It names the two lineages:
    - **linear-base**: a graded modality `□ᵣ` on top of linear types, as in Granule, Brunel et al.
      and Gaboardi et al.;
    - **graded-base**: pervasive annotations on every assumption and arrow, as in Petricek's
      structural system, QTT and Linear Haskell.
  - It gives translations between the two that preserve types, grades and operational semantics.
  - This is the current map of "which coeffect system is which".

## 2. Graded modal types, Granule, and effects with coeffects

- **Orchard, Liepelt, Eades**, *Quantitative program reasoning with graded modal types*
  (Granule), ICFP 2019 *(spike; Thm 7.1 re-read)*.
  - It has a linear base with semiring-graded `□ᵣ` (coeffects) and graded `◇` (effects for I/O).
  - It has no handlers.
  - Theorem 7.1 is type safety by progress and preservation.
- **Gaboardi, Katsumata, Orchard, Breuvart, Uustalu**, *Combining effects and coeffects via
  grading*, ICFP 2016 *(spike; §1 re-read)*.
  - Coeffects are graded comonads and effects are graded monads.
  - Their interaction is a graded distributive law, which exists only for "matched" pairs of
    grade maps.
  - It is the canonical "effects and coeffects together" paper. It has no handlers and no heap.
- **Abel, Bernardy**, *A Unified View of Modalities in Type Systems*, ICFP 2020 *(spike; abstract
  re-read)*.
  - A generic "modality" structure (an ordered semiring-like ringoid) covers linearity,
    irrelevance, security and more in one system.
  - The metatheory is the fundamental lemma of a relational model. Noninterference is a corollary.
- **Choudhury, Eades, Eisenberg, Weirich**, *A Graded Dependent Type System with a Usage-Aware
  Semantics*, POPL 2021 *(abstract)*.
  - It proves resource accounting against a *heap-based* operational semantics, and the
    single-pointer property for linear resources follows.
  - This "usage-aware store" technique is reused by Lorenzen et al. (§3.3).
- **Torczon, Suárez Acevedo, Agrawal, Velez-Ginorio, Weirich**, *Effects and Coeffects in
  Call-By-Push-Value*, PACMPL 8 OOPSLA2, 2024 *(spike)*.
  - It grades `U` for effects and `F` for coeffects.
  - Effect soundness and coeffect soundness are proved by mirrored logical relations, with no heap
    and no handlers.
  - Of the published systems, its shape (CBPV) is the closest to this core's.

## 3. Ownership, uniqueness and borrowing with grades or coeffects (priority)

### 3.1 Marshall, Vollmer, Orchard, *Linearity and Uniqueness: An Entente Cordiale*, ESOP 2022 *(sections: abstract, §1, §2, Thms 4–7)*

- **How borrowing is represented.**
  - Uniqueness is a modality `*A` (a value that has *never* been shared), set against linearity
    (a value that *will not* be shared).
  - `borrow : *A → !A` forgets uniqueness, and `copy` makes a fresh unique copy.
  - The paper puts it this way: `!` is a relative monad over `*`, and uniqueness is "a third kind of
    modality alongside coeffect and effect modalities".
- **Soundness.** It uses a call-by-name heap model, with conservation (Thm 4), uniqueness (Thm 5),
  progress (Thm 6) and equational soundness (Thm 7). These are syntactic, per-configuration
  invariants.
- **Against BoLo.** "Borrow" here is one-way: it forgets uniqueness permanently. There is no
  scope, no lifetime and no `Mut`.
- **For this survey.** The Granule authors do *not* classify uniqueness as a coeffect. It sits
  beside the coeffect `□ᵣ`.

### 3.2 Marshall, Orchard, *Functional Ownership through Fractional Uniqueness*, PACMPL 8 OOPSLA1, 2024, pp. 1040–1070 *(sections: abstract, §1, §4, §5, §6.1, §6.3, §7, §8)*

The OOPSLA-era paper exists. Its title, venue and pages were verified against BoLo's bibliography
entry [18] and the Granule project's publication list.

- **How borrowing is represented.** It uses *grades on a type former*, in the form of permissions.
  - `&ₚ A` with `p ∈ {∗} ∪ (0,1] ∩ ℚ` is "a graded form of non-uniqueness".
  - Unique ownership is `∗A ≡ &∗ A`, and a mutable borrow is `&₁ A`.
  - `withBorrow : ∗A → (&₁A ⊸ &₁B) → ∗B` (rule `with&`) creates a borrow. The borrow must be
    returned from the continuation.
  - `split : &ₚA → &ₚ/₂A ⊗ &ₚ/₂A` and `join` (when `p+q ≤ 1`) create and recombine immutable
    borrows.
  - "Reborrowing … simply involves continuing to split immutable borrows further."
  - `push : &ₚ(A⊗B) → &ₚA ⊗ &ₚB` and `pull` (§5) handle products at the *same* permission.
  - Functions can be polymorphic in `p`, ranging over owned and borrowed alike.
- **Relation to coeffects.** It is placed inside Granule's coeffect-graded calculus, and §8 says
  "Linearity is only one property that can be tracked via coeffects, the flavour of grading we
  consider".
  - The permission `p`, however, grades a *type* (`&ₚ`). Its introduction rules are not
    promotion scaling the context.
  - It is closer to fractional permissions carried by a modality than to a context coeffect.
- **What it proves, and how.** Syntactic type safety against a heap with permission-annotated
  references `ref ↦ₚ id`:
  - progress (Thm 6.6);
  - preservation (Thm 6.7), restricted to references that do not hold functions;
  - borrow safety (Lemma 6.8, Thm 6.9): the permissions pointing to a resource keep summing to 1,
    or drop to 0 once it is shared;
  - uniqueness (Cor. 6.10);
  - equational soundness (Thm 6.11).
  - The invariant is heap compatibility `H ⋈ Γ`, a *local, per-configuration* relation (Def. 6.4).
    Its `GCArr` rule lets leftover resources be "garbage collected". There is no leak-freedom
    theorem, and §4 says non-owned values are managed "implicitly by a garbage collector".
- **Lifetimes.** "We only support lexical lifetimes." No lifetime variables or outlives relation
  appear in §§3–5. Non-lexical lifetimes are future work (§8).
- **Mutable heap.** Yes: arrays and references with permission-indexed read, write and delete
  operations.
- **BoLo's own verdict** (BoLo §5): its borrowing construct "requires that borrows be explicitly
  returned at the end of their scope, which does not alleviate capability-passing style, and their
  mutable borrows are not type-preserving in general". The second clause refers to
  `&₁A ⊸ &₁B`, which changes the type.

### 3.3 Lorenzen, White, Dolan, Eisenberg, Lindley, *Oxidizing OCaml with Modal Memory Management*, PACMPL 8 ICFP, 2024 *(sections: abstract, §2.6, §3.2, §3.5, §4 overview, §5–5.5, §8.4)*

- **How borrowing is represented.** It uses *modes on context bindings* (`x : τ @ μ`) along three
  axes: affinity, uniqueness and locality.
  - `borrow x = e₁ for y = e₂ in e₃` (§3.5) lends `x` to `e₂` at `aliased` and `local`. `e₂`
    must return at `global`, so the borrow cannot escape, and `x` is available again in `e₃`.
  - The surface version is `let y = &x in e` (Fig. 5).
  - Only immutable borrows are provided. Locality is a stack-region level, not a named lifetime.
- **Relation to coeffects.** §5 gives a translation "into a graded modal calculus"
  (fine-grain call-by-value) by constructing an ordered semiring. The grades are
  `{0, A, AM, 1, M, ⊥}`, with `+` as the mode join, and it is extended with a residual `A ⊸ 1` so
  that aliased closures can be applied.
  - §5.3 restricts the construction to uniqueness and affinity, saying "the same techniques also
    apply to locality and borrowing". The borrowing part of the translation is claimed and not
    shown.
- **Soundness.** Progress and preservation (Lemmas 4.1, 4.2) over a usage-aware store semantics
  (after Choudhury et al.). A borrow copies the borrowed value into a new stack frame, and the frame
  is deleted when the region ends.
- **Against BoLo.** It has no `Mut` borrow and no lifetime variables, and it relies on the GC for
  the heap. Its advantage is full inference with no annotations.
- Its concurrent follow-up, Georges et al., *Data Race Freedom à la Mode* (POPL 2025), is
  summarised in `docs/prior-art-borrow-splitting.md` §2.6. It proves semantic soundness in Iris.

### 3.4 Bianchini, Dagnino, Giannini, Zucca, Servetto, *Coeffects for sharing and mutation*, PACMPL 6 OOPSLA2, 2022 *(sections: abstract, §1, Defs 2.3–2.4, §3.1–3.2, Thms 4.3, 4.5, 5.2, 5.7, 5.11, §7, §8)*

- **How it is represented.** The coeffects are *sharing* links among variables, in an imperative
  Featherweight Java.
  - Sharing is **non-structural**: "the way a given variable is used can affect the coeffects of
    other variables".
  - Coeffect contexts form a module over a semiring, and the operators are not pointwise.
  - Modifiers `read`, `caps` and `imm` (read-only, capsule/unique, immutable) sit on top. They are
    *detected* (inferred by a promotion rule), not imposed.
  - A variable is **lent** in `e` if it is not connected to the result (Def. 2.3). This is the
    closest thing in the paper to a borrow that does not escape.
- **Soundness.** Subject reduction preserves types and sharing (Thms 4.3, 5.2). The lent,
  capsule and immutability properties follow as corollaries (Thms 4.5, 5.7, 5.11). All of this is
  syntactic over a mutable store.
- **Against BoLo.**
  - There are no lifetimes and no scoped borrow that gives ownership back. It is a GC'd object
    language, so there is no deallocation.
  - Ownership is *transfer* rather than *invariant* (§7).
  - "All properties are deep". It contrasts this with Rust, which "uses ownership to control
    deallocation without a garbage collector".
- **For this survey.** It is the only paper found whose *coeffects* are themselves about aliasing
  and mutation in a heap. §8 proposes, as future work, formalising read-only and other
  "capabilities … as graded modal types".
- Follow-ups exist but were not read: *Multi-Graded Featherweight Java* (ECOOP 2023) and a
  heterogeneous-coeffects Java-like calculus (TCS 971, 2023).

### 3.5 Second-class values: Osvald, Essertel, Wu, González Alayón, Rompf, *Gentrification Gone too Far? Affordable 2nd-Class Values for Fun and (Co-)Effect*, OOPSLA 2016 *(sections: §1–2, related work)*; Osvald, Rompf, *Rust-like Borrowing with 2nd-Class Values*, SCALA 2017 *(sections: abstract, §1, §2)*

- **2016.** `@local` (second-class) values may not escape their defining scope.
  - The paper frames them explicitly as coeffects: "our @local annotations are co-effects,
    encoded on the left of the turnstile: `G, (@local c : CanIO), G′ ⊢ e : T`". They are set
    against a monad (`CanIO[T]`) or an effect type (`T @canIO`).
  - It notes that the restrictions "are similar to those on borrowed references in ownership type
    systems".
  - It proves type soundness and a "never leaks stack references" theorem (Thm 3.2) for a
    big-step, environment-based semantics, in Coq.
- **2017.** Rust-like `Imm`/`Mut` bindings in Scala. Flow sensitivity is removed by writing each
  borrow in continuation-passing style, `bindMut(x) { y => … }`, with the continuation's parameter
  second-class. "introducing variables as second-class values restricts their lifetime to the
  enclosing scope defined by the passed closure".
  - `bindImm` copies the value (`new Var(r.value)`), so its immutable "borrow" is a copy.
  - It enforces nothing about deallocation.
  - It is a short paper with no soundness proof for the borrowing layer.
- **Against BoLo.** The *shape* is BoLo's `withbor`: a continuation whose borrowed parameter
  cannot escape. The *framing* is a coeffect.
  - Lifetimes are only "the enclosing scope". There is no `['a] T`, so a borrow cannot be returned
    at a lifetime.
  - There is no memory model.
- **Descendants.**
  - System Ξ and System C (§4) build on `λ1/2`: "tracked blocks in System C correspond to
    second-class values".
  - System C §6.1 cites the 2017 paper as showing that second-class values "can even express
    borrowing".
  - Reachability types (Bao et al., OOPSLA 2021, and successors) come from the same group *(not
    read)*.

### 3.6 Borrowing inside a graded-base system: Matsushita, Ishii, *Pure Borrow: Linear Haskell Meets Rust-Style Borrowing*, arXiv 2604.15290 (PLDI 2026) *(abstract; summarised in `docs/prior-art-borrow-splitting.md` §2.5)*

- Linear Haskell's multiplicities `1`/`ω` are a graded-base coeffect system (Liepelt et al.'s
  classification).
- Pure Borrow implements Rust-style borrowing as a *library* on top, with lifetime tokens and a
  history-based model, and it claims leak freedom.
- The borrow is not a grade. The grades only enforce linearity of the tokens.

### 3.7 Mentioned only

- **Makwana, Krishnaswami**, *NumLin* (ECOOP 2019): fractional permissions in a linear type system
  *(secondhand, via Marshall–Orchard §5)*.
- **Spiwack, Kiss, Bernardy, Wu, Eisenberg**, *Linear Constraints*, arXiv 2604.21467, 2026: a
  revised and extended version of *Linearly Qualified Types*, ICFP 2022 *(abstract, §4.1
  opening)*.
  - Capabilities (`RW n`, `R n`) are *implicit linear arguments* solved by the constraint solver.
  - Borrowing slices, freezing and non-lexical lifetimes are encoded as library functions (§4).
  - It is context-side, like an implicit parameter, but its soundness is by desugaring into Linear
    Haskell, not by a coeffect semantics.

### 3.8 Comparison with BoLo

`—` means the feature was not found in the sections read.

| | BoLo | Marshall–Orchard 2024 | Lorenzen et al. 2024 | Bianchini et al. 2022 | Osvald–Rompf 2017 |
|---|---|---|---|---|---|
| where the borrow lives | `Imm`/`Mut` type formers at a lifetime; `[a]`/`[]I` filters the context | permission grade on a type (`&ₚ`) | mode on a context binding | coeffect (sharing) on a context binding | second-class annotation on a binding (a coeffect, by the 2016 paper) |
| named lifetimes, outlives, lifetime polymorphism | yes | — (lexical only) | — (stack-region levels) | — | — (enclosing scope) |
| `Mut` borrow | yes, type-preserving | `&₁`, type-changing (`&₁A ⊸ &₁B`) | — | `mut` default plus `read`; no scoped exclusive borrow | `bindMut`, no proof |
| reborrowing | at a shorter lifetime (`withbor` forms) | by `split`, then `join` | — | n/a | not formalised |
| borrow returned implicitly (no capability passing) | yes | no: the continuation returns `&₁B` | yes | n/a | yes |
| frozen lender | yes (borrow frame rule) | yes (the continuation consumes `∗A`) | in effect (during `e₂`, `x` exists only at `aliased`, `local`) | n/a | not stated |
| same-lifetime or same-permission views of components | refuted in our model at the same lifetime (`docs/prior-art-borrow-splitting.md` §0) | `push`/`pull` at the same `p` | modes are deep | deep modifiers | — |
| heap | linear, manual `alloc`/`free` | permission-annotated heap plus GC | stack regions plus GC heap | GC'd store | GC'd (Scala) |
| leak freedom | yes | no | no | no | no |
| soundness technique | semantic: a logical relation into a linear separation logic with borrow (anti-)frame rules; termination via lifetime stratification | syntactic progress and preservation; per-configuration heap compatibility; permission-sum lemma | syntactic progress and preservation over a usage-aware store | syntactic subject reduction preserving sharing | none (the 2016 base calculus: syntactic, Coq) |
| coeffect or grade connection | none printed (0 occurrences of "coeffect") | inside Granule's coeffect grading; §8 says so | §5 translation to a graded calculus (borrowing part claimed) | *is* a coeffect system | "@local … are co-effects" (2016) |

## 4. Effects in capability-passing style (only what bears on coeffects and capabilities)

- **Brachthäuser, Schuster, Ostermann**, *Effects as Capabilities* (Effekt, System Ξ), PACMPL 4
  OOPSLA 2020 *(spike; §7.3 re-read)*.
  - A handler "creates a capability and binds it". Effects are "a requirement on the calling
    context".
  - §7.3, *Coeffects*: "effects in Def … can also be handled either at the call-site or the
    definition-site. Petricek et al. refer to those requirements as latent or immediate … Effekt
    can thus be seen as a combination of a coeffects, second-class values, and delimited control
    … In the future, we hope to formally establish the relation to coeffects."
- **Brachthäuser, Schuster, Lee, Boruch-Gruszecki**, *Effects, Capabilities, and Boxes* (System
  C), PACMPL 6 OOPSLA 2022 *(spike; §6.1 and §6.5 re-read)*.
  - §6.5: "Our annotations on block variable bindings roughly correspond to structural coeffects,
    whereas the context restriction C roughly corresponds to a flat coeffect … the precise
    connection is unclear."
  - Boxed blocks are "reminiscent of the graded box modality of Gaboardi et al.".
- **Leijen**, *Koka: Programming with Row-polymorphic Effect Types*, MSFP 2014 *(abstract)*.
  - Row-polymorphic effect types sit on the *output* side of the judgment, with no capabilities.
  - This is the contrast case: Koka tracks effects the effect-system way, Effekt the coeffect way.
- **Plotkin, Power**, *Algebraic operations and generic effects* (ACS 2003) *(secondhand, via the
  CoeffectsStrict spike)*. **Plotkin, Pretnar**, *Handling algebraic effects*, LMCS 2013
  *(spike)*. A handler is the unique homomorphism out of the free model.
- **Wu, Schrijvers, Hinze**, *Effect Handlers in Scope*, Haskell 2014 *(abstract)*. **Piróg,
  Schrijvers, Wu, Jaskelioff**, *Syntax and Semantics for Operations with Scopes*, LICS 2018
  *(abstract)*.
  - Scoped operations delimit a region of the computation, much as a borrow block does.
  - Their subject is syntax and semantics for handlers of scoping constructs. They have no
    coeffect or capability reading.
- **Recent, abstracts only.**
  - *Yarrow* (Mathiasen, Timany, Birkedal, arXiv 2607.15876, 2026): algebraic effects with
    region-based memory, and an Iris program logic in which multi-shot handlers break the
    exit-a-region-at-most-once invariant.
  - *Cambria* (Liell-Cock, Staton, arXiv 2608.27798, 2026): parametrised handlers whose effect
    signatures abstract over resources such as locations.
  - *Affect* (van Rooij, Krebbers, POPL 2025): affine types with one-shot versus multi-shot
    effects.
  - *Modal Effect Types* (Tang et al., OOPSLA 2025).
  - These bear on "effects × linear resources", not on coeffects.

## 5. Capabilities, implicit parameters, and effects read as coeffects

- **Implicit parameters.**
  - Lewis, Launchbury, Meijer, Shields, *Implicit parameters: dynamic scoping with static types*
    (POPL 2000) *(secondhand: the PDF did not download)*.
  - Petricek's flat coeffect instance and `letdyn` provider (§1).
- **Boruch-Gruszecki, Odersky, Lee, Lhoták, Brachthäuser**, *Capturing Types*, TOPLAS 45(4), 2023
  *(sections: related work, "Coeffect systems")*.
  - Capture sets on types record which capabilities a value closes over.
  - The authors: coeffect systems "attach additional information to bindings in the environment
    … Such systems can be seen as similar in spirit to CC<:□". The difference is that Petricek's
    framework is simply typed and "coeffect-monomorphic".
  - The companion *Scoped Capabilities for Polymorphic Effects* (arXiv 2207.03402) is read in the
    spike.
- **Xu, Bračevac, Pham, Zhao, Odersky**, *System Capybara: Tracking Capabilities for Separation and
  Freshness*, arXiv 2607.09383, 2026 *(sections: abstract, §1, §2.4, Thms 5.1–5.4)*.
  - This is Scala's separation checker, built on capture checking. It compares itself directly
    with Rust (§2.4):
    - an owned value is a fresh capability;
    - `&mut` is a tracked read-write alias;
    - `&` is a read-only view `ro …^{f.rd}`.
  - The difference is when exclusivity is enforced: "Rust enforces shared-xor-mutable throughout
    each borrow's lifetime; Capybara tracks aliases and demands exclusivity only at a consume or a
    separation check."
  - **Soundness is semantic and mechanised in Lean 4:**
    - the fundamental theorem (5.1);
    - type soundness (5.2);
    - memory safety, meaning no use-after-free and each allocation freed at most once (Cor. 5.3);
    - read-only immutability (5.4);
    - separation.
  - There is no leak freedom and there are no lifetimes. It does not use the word "coeffect", but
    its lineage (capture sets) is the one *Capturing Types* compares to coeffects.
  - Among the systems found, it is the nearest in proof style to this repository: semantic, in
    Lean, with a fundamental theorem.
- **Choudhury, Krishnaswami**, *Recovering Purity with Comonads and Capabilities*, PACMPL 4 ICFP
  2020 *(sections: abstract, conclusion)*.
  - An impure calculus gains a comonad `□` for purity. It is modelled by "capability spaces": a
    program is capability-safe if it performs no effect without a runtime capability.
  - `□` removes *all* capabilities from the context. As future work the paper proposes an indexed
    `□_C` that removes a set `C`, and hopes it "could form a model of … other systems of
    coeffects".
  - That context-filtering comonad has the shape of BoLo's `[]I` (`CtxOutlives` filters the
    context by lifetime). This is our observation, not the paper's.
- **Jia, Liu, He, Deng, Bao, Rompf**, *Typestate via Revocable Capabilities*, arXiv 2510.08889
  *(abstract)*. It moves scoped capabilities to flow-sensitive ones in Scala, decoupling
  "capability lifetimes from lexical scopes".

## 6. The BoLo authors' own line

Wagner, Gierczak, Brianna Marshall, Li and Ahmed.

- **BoLo** (PACMPL 9 OOPSLA2, 2025) *(sections: §1, §5)*.
  - The word "coeffect" does not occur in the paper.
  - Graded systems enter only in §5, through Marshall–Orchard (quoted in §3.2) and Lorenzen et al.
  - The paper's motivation is avoiding "capability-passing style".
- **Marshall, Wagner, Li, Gierczak, Ahmed**, *An Incremental Approach to the Semantics of
  Borrowing*, HOPE 2024 (extended abstract, 3 pp.) *(full)*.
  - This is the pre-BoLo presentation. Its type system is written as **context structure**:
    - an "unrestricted borrowable context Δ", with judgments `Δ; Γ ⊢ e : C`;
    - borrowable variables annotated with a lifetime bound, `Γ₂[l]`;
    - `brw x : Brw_l′ V` for `l′ < l`;
    - thunks carrying "a lower bound on the lifetimes it closes over" (`Δ, Γ ≥ l`);
    - for mutable borrows, a separate context `Δ_m` that "is split between sub-terms, as usual".
  - It credits Perceus (Reinking et al.) for the borrowable-context idea.
  - It does not use the word "coeffect".
  - Its logic has the borrow frame and mutable anti-frame rules, and a Kripke resource model with
    owned, immutable and mutable fragments.
- **Wagner's publication list** (andrewwagner.io) *(full page)* has no paper on coeffects, grades
  or handlers. Its themes are borrowing, ABIs, realizability, linking types and interoperability.
  A June 2025 talk is listed as "An Adjoint Separation Logic for the Wasm Call Stack" *(title
  only)*.
- **Nothing found** that relates this group's work to coeffects or grades, beyond BoLo §5's
  comparison with Marshall–Orchard.

## 7. What Wagner most plausibly meant

This section is an inference, and it is labelled as one. It ranks readings by the evidence in
§§1–6. Wagner's full message and its context were not available to this survey.

1. **The context side of borrowing: a borrow is a requirement on the context, discharged by a
   scope. Strongest.**
   - His own HOPE 2024 system *is* written as context structure. It has a borrowable zone `Δ`,
     lifetime-annotated bindings `Γ[l]`, and a lifetime lower bound on the context of a thunk.
     That is the shape of a structural coeffect (per-binding annotations) plus a flat restriction
     (`Δ, Γ ≥ l`), in System C §6.5's vocabulary.
   - BoLo keeps this in `[]I`, which filters the context.
   - The published bridge to *effect handling* is on exactly this side. Effekt §7.3 reads
     handler-bound capabilities as coeffects ("latent or immediate"). Osvald et al. 2016 call
     scope-bound values "co-effects … on the left of the turnstile". Osvald–Rompf 2017 use them for
     Rust-like borrowing in CPS.
   - So the literature already connects three things, borrowing, effect handlers and coeffects,
     each through "a capability bound by a scope and demanded by the body".
   - The Coeffects spike built this reading (`KDem`, `provide_wf`).
2. **Granule's ownership and borrowing as grades (Marshall–Orchard 2024). Plausible; second.**
   - It is the one published borrowing system inside a coeffect-graded calculus, and BoLo cites
     and critiques it, so Wagner knows it.
   - Against: BoLo §5 rejects its design, which makes it unlikely to be what he recommends as a
     model. And its grade is on a type former (`&ₚ`), not on the context.
3. **Capture checking and separation checking (Scala: CC<:□, Capybara). Plausible; third.**
   - Capabilities are tracked in types, *Capturing Types* compares them to coeffects, and Capybara
     now models `&`/`&mut` analogues.
   - It overlaps with reading 1 through the Effekt and System C lineage. The difference is that
     the tracking sits on values' types rather than on bindings.
4. **Combining effects and coeffects via grading (Gaboardi et al. 2016; Torczon et al. 2024).
   Weakest.**
   - "As well" could mean "effects *and* coeffects together", and Torczon et al. is even in CBPV.
   - But neither paper has handlers, borrows or a heap.
   - The CoeffectsStrict spike found that the combining laws do not reach the scope axis.

The best-supported reading, then, is (1). "Check out coeffects" most likely means: treat what a
borrow needs as a context-side demand, the dual of an effect on the result. That is how his own
HOPE 2024 calculus is already laid out, and how Effekt relates capability-passing handlers to
coeffects.

## 8. The closest existing system to "borrowing as coeffects"

There is no system that is both a coeffect system in the strict (Petricek or Brunel) sense *and* a
borrowing system with lifetimes. Three come closest, each on a different axis:

- **Most complete borrowing inside a coeffect-graded calculus: Marshall–Orchard 2024.**
  - **It expresses what BoLo does not:**
    - fractional `split`/`join` that *recovers* a mutable or unique value by rejoining;
    - permission polymorphism, one function over owned and borrowed;
    - same-permission `push`/`pull` through products (BoLo's same-lifetime analogue is refuted in
      our model);
    - type-changing mutable borrows;
    - coexistence with arbitrary semiring grades and GC'd sharing (`share`/`clone`).
  - **BoLo expresses what it does not:**
    - named lifetimes, outlives and lifetime polymorphism;
    - borrows that escape into results at a lifetime (`['a] T`) and into thunks;
    - borrows that need not be returned, so there is no capability passing;
    - type-preserving `Mut` with an anti-frame;
    - deep immutability under `Imm`;
    - leak freedom and termination.
  - **Proof technique:**
    - Marshall–Orchard: syntactic progress and preservation against a per-configuration heap
      compatibility, plus a permission-sum lemma, with a GC escape (`GCArr`).
    - BoLo: semantic, a logical relation into a linear separation logic whose borrow frame rule
      carries the global invariant.
- **Closest in coeffect framing: second-class values (Osvald et al. 2016; Osvald–Rompf 2017).**
  - The borrow is a scope-bound context annotation, and it is called a co-effect.
  - It has BoLo's `withbor` continuation shape.
  - It has no lifetimes beyond the enclosing scope, no memory model, and no proof for the
    borrowing layer.
- **Closest in "coeffects about aliasing in a mutable heap": Bianchini et al. 2022.**
  - It has genuine non-structural coeffects for sharing, with read-only and immutable modifiers,
    and syntactic subject reduction.
  - It has no scoped borrow and no deallocation.

If one system has to be named, it is **Marshall–Orchard 2024**. Note that its grade is a
permission on a type, not a context coeffect, and that Granule's own authors classify uniqueness as
a third kind of modality, not a coeffect (§3.1).

## 9. Reading list, in order

1. **Marshall, Wagner, Li, Gierczak, Ahmed, HOPE 2024 abstract** (3 pages). Wagner's own
   borrowing calculus, written as context structure. It is the most direct evidence of what
   "coeffects" would mean to him.
2. **Marshall, Orchard, *Functional Ownership through Fractional Uniqueness*, OOPSLA 2024,
   §§4–6.** The one full borrowing system inside a coeffect-graded language. Read it beside BoLo
   §5's critique.
3. **Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*, OOPSLA 2020, §7.3, with System
   C (OOPSLA 2022) §§6.1 and 6.5.** The explicit, and self-described unfinished, bridge from effect
   handlers to coeffects via capabilities and second-class values.
4. **Osvald et al., OOPSLA 2016, §1–2, then Osvald–Rompf, SCALA 2017.** Scope-bound values named
   as coeffects, then used for Rust-like `Imm`/`Mut` borrowing in CPS, which is `withbor`'s shape.
5. **Bianchini et al., *Coeffects for sharing and mutation*, OOPSLA 2022, §§1–4.** What a coeffect
   system about a mutable heap looks like when the coeffects are non-structural.

Runner-up: Lorenzen et al. 2024 §5, the only printed translation of a borrowing-capable mode
system into a semiring-graded calculus (the borrowing part is claimed there, not shown).

## 10. Honest limits

- **Not retrieved:**
  - Lewis et al. POPL 2000 (the download failed);
  - D. Marshall's PhD thesis, *Graded Modal Types for Memory and Communication Safety* (Kent,
    2025), which is listed on Orchard's page but has no PDF located;
  - Osvald et al. 2016's appendix and Coq development;
  - the Marshall–Orchard appendices with full proofs.
- **Not re-read here, relied on the spikes:** Gaboardi et al. 2016, Torczon et al. 2024,
  Abel–Bernardy 2020, Brunel et al. 2014, Ghica–Smith 2014, Plotkin–Pretnar, CC<:. Their quoted
  passages were spot-checked.
- **Abstract only:**
  - Koka (MSFP 2014; the POPL 2017 paper was not read);
  - scoped effects;
  - Wood–Atkey;
  - Choudhury et al. 2021;
  - Yarrow, Cambria, Affect, *Modal Effect Types*;
  - *Typestate via Revocable Capabilities*;
  - Pure Borrow in this survey (the repository has a fuller reading).
- **Not read:** reachability types (Bao et al. 2021, Wei et al. 2024, and the OOPSLA 2025 logical
  relations model), *Degrees of Separation* (OOPSLA 2024), *Multi-Graded Featherweight Java*, and
  *On Graded Coeffect Types for Information-Flow Control* (2025).
- **2026 preprints** (Capybara, Yarrow, Cambria, Linear Constraints, Same Coeffect's arXiv version)
  were read as posted. Their venues other than Same Coeffect (ICFP 2026) were not confirmed.
- **Nothing found** in which a BoLo author discusses coeffects in print. §7 is inference from
  indirect evidence. dblp was not reachable, so author lists were checked against first pages,
  conference pages and author home pages instead.

## Sources

- https://www.andrewwagner.io/assets/papers/incr-brw-hope.pdf (HOPE 2024)
- http://www.ccs.neu.edu/home/amal/papers/borrowing.pdf (BoLo)
- https://www.andrewwagner.io/
- https://arxiv.org/pdf/2310.18166 (Marshall, Orchard, OOPSLA 2024)
- https://granule-project.github.io/papers/esop22-paper.pdf (Entente Cordiale)
- https://granule-project.github.io/ and https://dorchard.github.io/ (publication lists)
- https://arxiv.org/pdf/2606.28042 (Liepelt, Marshall, Orchard, ICFP 2026)
- https://homepages.inf.ed.ac.uk/slindley/papers/mode-inference.pdf (Lorenzen et al., ICFP 2024)
- https://arxiv.org/pdf/2209.07439 (Bianchini et al., OOPSLA 2022)
- https://www.cs.purdue.edu/homes/rompf/papers/osvald-oopsla16.pdf
- https://www.cs.purdue.edu/homes/rompf/papers/osvald-scala17.pdf
- https://arxiv.org/pdf/2604.15290 (Pure Borrow)
- https://arxiv.org/pdf/2604.21467 (Linear Constraints) and https://arxiv.org/pdf/2103.06127
  (Linearly Qualified Types)
- https://tomasp.net/academic/papers/structural/coeffects-icfp.pdf
- https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-906.pdf
- https://www.cis.upenn.edu/~stevez/papers/BGMZ14.pdf
- https://pure-oai.bham.ac.uk/ws/portalfiles/portal/23697858/esop14.pdf
- https://strathprints.strath.ac.uk/79767/1/Wood_Atkey_ESOP_2022_A_framework_for_substructural_type_systems.pdf
- https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
- https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf
- https://www.cse.chalmers.se/~abela/icfp20.pdf
- https://arxiv.org/pdf/2011.04070 (Choudhury, Eades, Eisenberg, Weirich)
- https://arxiv.org/pdf/2311.11795 (Torczon et al.)
- https://ps.informatik.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf
- https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects.pdf
- https://arxiv.org/pdf/1406.2061 (Koka, MSFP 2014)
- https://arxiv.org/pdf/1312.1399 (Plotkin, Pretnar)
- https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf
- https://maciejpirog.github.io/papers/scopes.pdf
- https://se.cs.uni-tuebingen.de/publications/boruch2023capturing.pdf (Capturing Types)
- https://arxiv.org/pdf/2207.03402 (CC<:)
- https://arxiv.org/pdf/2607.09383 (Capybara)
- https://arxiv.org/pdf/1907.07283 (Choudhury, Krishnaswami)
- https://arxiv.org/pdf/2510.08889 (Typestate via Revocable Capabilities)
- https://arxiv.org/pdf/2607.15876 (Yarrow)
- https://arxiv.org/pdf/2608.27798 (Cambria)
- https://iris-project.org/pdfs/2025-popl-affect.pdf
- https://arxiv.org/pdf/2407.11816 (Modal Effect Types)
