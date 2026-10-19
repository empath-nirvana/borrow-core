## Report: graded, modal and adjoint type systems as prior art for "borrow-core as an adjoint system"

I did not edit the repo. Downloaded PDFs were converted to text in `/private/tmp/claude-501/-Users-johnthompson-repos-borrow-lang/8e4045bd-7129-41e8-acf7-6b8f9fa81f6a/scratchpad/papers/`. Citations marked **(unverified)** are ones I did not confirm this session. Everything else I read either in full text (FT) or in an abstract or metadata page (AB).

### Bottom line
- **Closest system:** no single prior system is "our calculus as an adjoint system". The nearest construction is three pieces combined:
  1. Pruiksma–Chargin–Pfenning–Reed adjoint logic, for the `lin`/`aff`/`unr` modes and the concurrency reading.
  2. Curien–Fiore–Munch-Maccagnoni, for keeping the CBPV `U`/`F` effect adjunction separate from the resource adjunction.
  3. Marshall–Orchard fractional uniqueness, or the OxCaml contention axis, for `imm`/`mut`.
- **Have `imm`/`mut` been modes or grades before?** Yes, in two places, but never with lifetimes ordered as a chain, never with lexical lend blocks inside a mode theory, and never with effect handlers.
- **Genuinely new:** lifetimes as part of the mode or grade structure, the T1 interaction between resuming operations and borrows, and a mechanised adjoint presentation of borrowing.

### 1. Granule

**1a. Graded modal core.** Granule is linear by default, with a semiring-graded comonad `□_r A` (written `A [r]`), dereliction (`der`) and approximation (`approx` along the semiring preorder). The paper recaps the semirings ℕ, intervals (`0..1` is affine), and security lattices. Granule calls this design "linear base"; Linear Haskell is "graded base". (FT, recap in Marshall–Orchard §3.)

**1b. Marshall, Vollmer, Orchard, *Linearity and Uniqueness: An Entente Cordiale*, ESOP 2022, LNCS 13240, pp. 346–375** (AB, plus a secondary reading-group note; I did not get the full text).
- Calculus LCU: linearity is the base and uniqueness is a modality `*`.
- `!` is a comonad. `*` is a monad: "borrow" (forget uniqueness) is its return and "copy" is its bind. Together `*` and `!` form a relative monad.
- Slogan: linearity restricts future use; uniqueness guarantees past use.
- Mutable arrays rely on uniqueness. There is a heap model with reference counts.
- Theorem names and proof status: (unverified). The 2024 paper cites a uniqueness theorem and a conservation property from it.

**1c. Marshall, Orchard, *Functional Ownership through Fractional Uniqueness*, OOPSLA 2024, PACMPL 8(OOPSLA1), DOI 10.1145/3649848, arXiv 2310.18166** (FT).
1. **Grades:** a borrow modality `&_p A` with permissions `p ::= * | f`, where `f ∈ ℚ` and `0 < f ≤ 1`.
   - `&_1` is a mutable borrow and `&_f` with `f < 1` is immutable.
   - `*A ≡ &_* A` is unique ownership.
   - The rules are `withBorrow : *A, (&_1 A ⊸ &_1 B) ⊢ *B`, `split : &_p A → &_{p/2} A ⊗ &_{p/2} A`, and `join : &_p, &_q → &_{p+q}` with `p+q ≤ 1`.
   - `share : *A → □_r A` and `clone` (deep copy back to `*`, using existential "identifiers").
   - Reborrowing is repeated split. Partial borrows of a product use distributive laws.
   - `*` "induces a relative functor over" the `&` modality (§5.1).
2. **Shifts:** `share` and `clone` between `*` and `□_r`; `withBorrow` from `*` into `&_1`.
3. **Lifetimes:** lexical only, enforced by the `withBorrow` continuation. There is no lifetime index and no outlives relation. Non-lexical lifetimes are future work.
4. **Concurrency:** disjoint partial borrows are used with Granule's `par`. No data-race theorem.
5. **Interior mutability:** none.
6. **Proofs, on paper (appendices):**
   - progress (Thm 6.6);
   - preservation (Thm 6.7), with references restricted to non-function types;
   - borrow safety (Lemma 6.8: fractions summing to 1 are preserved, or drop to 0);
   - multi-step borrow safety (Thm 6.9);
   - uniqueness as a corollary (6.10);
   - soundness of the equational theory (6.11).

   Conservation in their CBV setting is explicitly left as future work. The categorical model "based on adjunctions" (LNL-style) is listed as future work, so no adjoint model of borrowing exists there.
7. **Map to ours:**
   - `&_1` corresponds to our `mut` and `&_{f<1}` to our `imm`. Their `*` is our owned value.
   - `withBorrow` is a lexical lend block in continuation form.
   - They have no lifetimes, so no chain and no reborrow-at-a-shorter-lifetime. Their reborrow is fraction splitting, not BoCa's reborrow.
   - No effects or handlers, no CBPV, and no fundamental property or adequacy.

**1d. Granule concurrency.** Marshall, Orchard, *Replicate, Reuse, Repeat: Capturing Non-Linear Communication via Session Types and Graded Modal Types*, PLACES 2022, EPTCS 356, arXiv 2203.12875 (AB).
- Session types are linear; grading recovers reusable channels, replicated servers and multicast as variants of a fork primitive.
- Shared channels use a graded monadic modality, dual to `[r]`.
- No borrowing.

**1e. Graded and adjoint bridges.**
- Eades, Orchard, *Grading Adjoint Logic*, arXiv 2006.08854 (AB): "adjoint logic uses modes to control which structural rules are allowed; graded logic controls how they are used."
- Vollmer, Marshall, Eades, Orchard, *A Mixed Linear and Graded Logic: Proofs, Terms, and Models*, CSL 2025, LIPIcs 326, arXiv 2401.17199 (AB): LNL composed with a grading action, with sequent calculus, natural deduction (shown isomorphic) and a categorical model. It lists "an adjoint model for uniqueness" as further work.

### 2. Benton's LNL and descendants

**Source:** Benton, *A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models*, CSL '94, LNCS 933, pp. 121–135, DOI 10.1007/BFb0022251; extended version Cambridge TR UCAM-CL-TR-352 (AB).
1. **Modes:** two, a linear SMCC and a non-linear CCC.
2. **Shifts:** a symmetric monoidal adjunction F ⊣ G, with `! = F G`. Benton shows this is equivalent to linear categories.
3–5. Borrowing, concurrency, interior mutability: none.
6. **Proofs:** on paper; term calculus and models.
7. **Map to ours:** our `!` persistent values are the LNL `F G` comonad. Important: LNL's adjunction is a resource adjunction. Our CBPV `U ⊣ F` is an effect adjunction, and the two must not be identified (see §5).

**Descendants seen this session:**
- PCPR adjoint logic (below) embeds LNL (FT).
- Vollmer et al. 2025, the graded LNL above.
- Krishnaswami–Pradic–Benton, *Integrating Linear and Dependent Types*, POPL 2015 (unverified).
- Benton–Wadler, LICS 1996 (unverified).

### 3. Adjoint logic

**3a. Reed, *A Judgmental Deconstruction of Modal Logic*, unpublished manuscript, May 2009.** Confirmed only through PCPR's bibliography. It introduced arbitrary mode preorders.

**3b. Pruiksma, Chargin, Pfenning, Reed, *Adjoint Logic and Its Concurrent Operational Interpretation*, manuscript under submission January 2018, cs.cmu.edu/~fp/papers/adjoint18.pdf** (FT).
1. **Modes:**
   - Each mode m has σ(m) ⊆ {W, C}: {} is linear, {W} affine, {C} strict, {W, C} structural. Exchange is always allowed.
   - There is a preorder on modes, monotone in σ.
   - "Declaration of independence": a proof at mode k may use only hypotheses at modes at least as strong as k.
   - Every mode has the same connective rules; only the structural rules differ.
2. **Shifts:** up and down shifts between comparable modes. Benton's F and G, and Girard's `!`, are special cases. LNL, judgmental S4, lax logic and subexponential linear logic embed (Thms 2.3, 2.6, 2.8).
3. **Borrowing:** none.
4. **Concurrency:** it is read straight off the modes.
   - Proofs are session-typed processes.
   - Contraction at a mode gives multicast; weakening gives cancellation and logically justified distributed garbage collection.
   - Preservation is session fidelity (Thm 5.1). Progress is deadlock freedom (Thm 5.3).
   - A "no garbage" result is proved.
5. **Interior mutability:** none. "Shared memory implementation" is listed as future work.
6. **Proofs, on paper:** cut elimination via multicut (Thm 2.10), identity expansion (2.9), conservativity, preservation and progress. No mechanisation mentioned.
7. **Map to ours:**
   - `lin`/`aff`/`unr` correspond exactly to modes with σ = {}, {W}, {W, C}, and `!` is a shift.
   - The independence principle is the shape our "unr may not depend on lin" rules must take.
   - Missing from their system: borrow modes, lifetimes, effects and handlers, and CBPV.

**3c. Follow-ups on process interpretations.**
- Pruiksma, Pfenning, *A Message-Passing Interpretation of Adjoint Logic*, PLACES 2019, EPTCS 291, arXiv 1904.01290 (AB): session fidelity and deadlock freedom proved.
- Pruiksma, Pfenning, *Back to Futures*, arXiv 2002.04607 (AB): a shared-memory semantics of the semi-axiomatic sequent calculus, weakly bisimilar to message passing, with typed linear futures.
- Jang, Roshal, Pfenning, Pientka, *Adjoint Natural Deduction*, arXiv 2402.01428 (AB; the FSCD 2024 venue is unverified): natural deduction, a functional language, "freedom from garbage" for some modes, and type checking. No mechanisation mentioned.

**3d. Shared mode as interior mutability.** Balzer, Pfenning, *Manifest Sharing with Session Types*, ICFP 2017, PACMPL 1, Article 37, DOI 10.1145/3110281 (AB).
- Types are stratified into a linear layer and a shared layer, linked by modal shifts (acquire and release). This is the closest adjoint account of interior mutability: a shared mutable process with mutual exclusion.
- Session fidelity holds; deadlock freedom is lost.
- The exact shift notation and the deadlock-freedom follow-up (Balzer, Toninho, Pfenning, ESOP 2019) are (unverified).

**3e. Licata, Shulman, Riley, *A Fibrational Framework for Substructural and Modal Logics*, FSCD 2017, LIPIcs 84, 25:1–25:22, DOI 10.4230/LIPIcs.FSCD.2017.25** (AB).
- A mode theory (a 2-dimensional cartesian multicategory) describes the structure of contexts. Every connective is one of two general connectives (F-like and U-like), which form a bifibration.
- Cut and identity admissibility are proved once for every mode theory. An equational theory identifies derivations that differ only in where structural rules sit.
- Examples cover linear, affine, relevant, bunched, monoidal functors and adjunctions.
- Proofs on paper. Per PCPR, it gives no operational semantics.
- Licata–Shulman LFCS 2016 (2-category of modes) is (unverified).
- **Map to ours:** this is the only framework general enough to state "context = owned resources plus lifetime-indexed borrows" as a mode theory, and nobody has done it.

**3f. Multimodal type theory.** Gratzer, Kavvos, Nuyts, Birkedal, *Multimodal Dependent Type Theory*, LICS 2020; LMCS 17(3), 2021 (AB).
- The mode theory is a 2-category of modes, modalities and 2-cells.
- Consistency and canonicity are proved by gluing, for any mode theory.
- Structural, not substructural: no linearity. Normalisation (Gratzer, LICS 2022) is (unverified).
- **Effects descendant:** Tang, White, Dolan, Hillerström, Lindley, Lorenzen, *Modal Effect Types*, OOPSLA 2025, PACMPL 9(OOPSLA1), pp. 1130–1157, arXiv 2407.11816 (AB). Its calculus Met is a multimodal System F with effects and handlers, where effects are relative and absolute modalities. This is prior art for effects as modes. It has no borrows. Proof status: (unverified).

### 4. QTT, Idris 2, Linear Haskell, graded CBPV

**QTT and Idris 2.**
- McBride, *I Got Plenty o' Nuttin'*, WadlerFest 2016. Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018, pp. 56–65 (AB).
  - Semiring usage annotations on binders; quantity 0 is erased.
  - Semantics: realizability (a variant of linear combinatory algebras) and quantitative CwFs. Proofs on paper; mechanisation is (unverified).
- Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021, arXiv 2104.00480 (AB). The semiring is {0, 1, ω}. Session types are a library example.
- No borrowing in either.
- **Map:** QTT multiplicities 1 and ω correspond to our `lin` and `unr`. Affine needs a semiring with an ordered 0..1.

**Linear Haskell.**
- Bernardy, Boespflug, Newton, Peyton Jones, Spiwack, arXiv 1710.09756, DOI 10.1145/3158093 (AB; the POPL 2018 venue and the on-paper metatheory are unverified). Multiplicities sit on arrows ("graded base"). Used for mutable data behind pure interfaces.
- Spiwack, Kiss, Bernardy, Wu, Eisenberg, *Linearly Qualified Types*, ICFP 2022, PACMPL 6, pp. 137–164 (AB). Linear constraints infer capabilities and uniqueness; soundness is by desugaring into Linear Haskell.
- **Borrowing on top of Linear Haskell:** Matsushita, Ishii, *Pure Borrow: Linear Haskell Meets Rust-Style Borrowing*, PLDI 2026; arXiv 2604.15290 v4 (FT).
  - `Mut_α`, `Share_α` and `Lend_α` are library types, not modes, over a `BO_α` monad.
  - Lifetimes are atoms with `∧` intersection and `Static`: a meet-semilattice, not a chain.
  - `parBO` gives parallel mutation.
  - Strong confluence (Thm 5.1), "association" (Thm 5.2) and leak freedom (Thm 5.3) are proved.
  - **Conjectured, not proved:** progress (Conj 5.4) and that association is a bisimulation (Conj 5.5). Preservation of safety depends on Conj 5.5.

**Graded CBPV: it exists.**
- Torczon, Suárez Acevedo, Agrawal, Velez-Ginorio, Weirich, *Effects and Coeffects in Call-By-Push-Value*, OOPSLA 2024, PACMPL 8, DOI 10.1145/3689750, arXiv 2311.11795 (FT).
  - Effects grade the thunk type `U_φ B`; coeffects grade the returner `F_q A`. `U_φ(F A)` gives the graded monad and `F_q(U B)` the graded comonad.
  - A resource semiring {0, 1, ω} recovers linear and affine tracking.
  - Effect soundness and coeffect soundness are proved via fundamental lemmas of logical relations, mechanised in Coq.
  - No borrows, no handlers, no concurrency.
  - **This is the closest mechanised precedent for our kernel's U/F plus grades plus logical-relation proof.**
- McDermott, *Grading Call-by-Push-Value, Explicitly and Implicitly*, FSCD 2025, LIPIcs 337 (AB): effect-graded CBPV with a coherence result.

**OxCaml modes** (graded and modal, and the most relevant industrial line).
- Lorenzen, White, Dolan, Eisenberg, Lindley, *Oxidizing OCaml with Modal Memory Management*, ICFP 2024, PACMPL 8, Art. 253 (FT).
  - Mode axes: affinity (many/once), uniqueness (unique/aliased) and locality (global/local), plus modalities.
  - Borrowing is immutable only: `borrow x = e for y = e in e`, where a borrowed value is local and aliased inside a lexical region.
  - Soundness is proved on paper against a usage-aware store semantics.
  - They translate the mode calculus into a graded fine-grain-CBV calculus with a hand-built semiring. They need an adjoint residual "A⊸1" so that `A ∘ A⊸1` is a comonad.
- Georges, Peters, Elbeheiry, White, Dolan, Eisenberg, Casinghino, Pottier, Dreyer, *Data Race Freedom à la Mode*, POPL 2025, PACMPL 9, pp. 656–686 (FT).
  - Contention axis: uncontended ≤ shared ≤ contended, which is read-write, read-only and no access. Portability axis: portable ≤ nonportable.
  - Interior mutability through Capsule and reader-writer-lock APIs keyed by unique or aliased ghost keys.
  - Proved and mechanised in Rocq/Iris: a fundamental theorem, "no crash implies no race" (Thm 3.1), semantically typed expressions are data-race free (Thm 5.3), and semantic soundness of the Capsule and RwLock APIs (Thms 6.1, 6.2).
- Peters, Jacobs, Kalinichenko, Stevenson, Smith, Dreyer, Eisenberg, *Mode Crossing*, ICFP 2026, PACMPL 10, Art. 283 (FT). Modal kinds; soundness in Rocq/Iris.
- **Map:** shared/uncontended is a mode-level imm/mut, but per thread, not per lifetime. Locality is a two-point lifetime. There is no mutable borrow with lifetimes.

**Adjacent effects work.** van Rooij, Krebbers, *Affect: An Affine Type and Effect System*, POPL 2025, PACMPL 9, pp. 126–154 (AB). Affine types track one-shot versus multi-shot continuations; logical relation in Iris/Coq. Relevant to our `lin`/`aff`/`unr` continuations. No borrows.

### 5. CBPV as an adjunction
- Levy: `U ⊣ F`, with `UF` a monad and `FU` a comonad. Confirmed only as cited in Torczon et al. ("Levy 2003a"); the book and adjunction-model papers are (unverified) this session.
- Curien, Fiore, Munch-Maccagnoni, *A Theory of Effects and Resources: Adjunction Models and Polarised Calculi*, POPL 2016, DOI 10.1145/2837614.2837652, HAL hal-01256092 (AB).
  - Effects and resources are orthogonal. The models linearise CBPV adjunction models, or equivalently extend LNL with an adjoint resolution of effects.
  - Recovers Levy (cartesian linear structure, trivial resources) and Benton (trivial effects).
  - The adjoint resolution of effects corresponds to polarisation.
  - **Lesson for us:** our CBPV `U`/`F` and our `lin`/`aff`/`unr`/`!` shifts are two different adjunctions, and an adjoint presentation must keep both.
- Munch-Maccagnoni, *Resource Polymorphism*, arXiv 1803.02796 (AB): ownership, move and RAII for OCaml from polarisation. Combette, Munch-Maccagnoni, *A resource modality for RAII*, LOLA 2018 (unverified content). Neither has a borrow mode with lifetimes.

### 6. Have imm/mut been modes or grades?
- **Yes, as grades:** Marshall–Orchard, OOPSLA 2024, §5. `&_1 A` is mutable and `&_f A` with `f < 1` is immutable, a graded generalisation of the uniqueness modality, with split and join. Lexical only, no lifetimes.
- **Yes, as modes, for threads:** Georges et al., POPL 2025, §2.4. The contention axis uncontended ≤ shared ≤ contended. These are modes of access, not borrows with lifetimes.
- **Immutable borrow as a mode combination:** Lorenzen et al., ICFP 2024, §2.6. Local plus aliased in a lexical region.
- **Not as modes:** Pure Borrow (PLDI 2026) has `Mut_α`/`Share_α` as library types over a monad.

### 7. What prior art does not cover
1. Lifetimes inside the mode or grade structure. No surveyed system has lifetimes in the mode theory: Marshall–Orchard and OxCaml are lexical and unindexed, and Pure Borrow's lifetimes are type-level atoms forming a meet-semilattice. BoCa's lifetimes are ordered as a chain, together with reborrowing at a shorter lifetime.
2. Any adjoint or categorical model of borrowing. It is explicitly future work in Marshall–Orchard 2024 and in Vollmer et al. 2025.
3. T1 (a resuming operation cannot cross a borrow), or any interaction of borrow modes with deep handlers. Met and Affect cover effects with modes or affinity, but not borrows.
4. A concurrency story derived from borrow modes. The adjoint-logic concurrency results (multicast, cancellation, deadlock freedom) concern `lin`/`aff`/`unr` modes only. DRFCaml's data-race freedom is a separate axis, not derived from borrows.
5. Mechanised adjoint logic. I found none. The adjoint-logic papers (PCPR18, Licata–Shulman–Riley, Jang et al.) are on paper. The only mechanised graded CBPV is Torczon et al. in Coq, and the only mechanised mode-based data-race-freedom work is OxCaml's Rocq/Iris line.

### What our calculus would add or lack relative to each
- **Versus PCPR adjoint logic:** they have the `lin`/`aff`/`unr` modes and shifts. We would add borrow modes, lifetimes, CBPV and handlers. They have a process semantics we lack.
- **Versus Marshall–Orchard:** they use fractions for `imm`; we use lifetimes and lexical lends. They lack effects and the fundamental property and adequacy; we lack fraction-style split and join, unless BoCa's reborrow is read that way, which I have not checked.
- **Versus DRFCaml:** they have proved data-race freedom with interior mutability. We have neither threads nor interior mutability. Their imm/mut is not lifetime-scoped.
