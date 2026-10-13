# Prior art: formal models of resources and lifetimes under control effects (landing survey, part C)

This note asks one question of the verified and formal literature. How do models that handle
ownership, regions or lifetimes treat control effects and suspension? Which of them succeed, what
do they assume about lifetimes and time, and what negative results are on record? It proposes
nothing. Its last section relates the findings to tier 2's adjacency problem
([tier2-status.md](../tier2-status.md); [interaction-algebra.md](../foundations/interaction-algebra.md)
§4.2, premises PL1–PL4).

**Not repeated here; cite these instead.**

- `~/repos/borrow-core/docs/prior-art-suspension-borrows.md`: Rust E0626/`Pin`, OxCaml, Scala
  capture checking, Effekt/System C, Koka, Hylo/Swift; §5.1 region systems; §5.2 handler logics
  table (Hazel, blaze, Affect, Tang et al., RustBelt); §5.3 tokens versus strata.
- [p10-p9-exclusivity-lifetimes.md](p10-p9-exclusivity-lifetimes.md) §1.4 (Hazel protocols and
  Law A1, quoted), §1.6 (Yarrow), §1.14 (RustBelt lifetime-logic rules, quoted).
- [i2-capture-resume.md](i2-capture-resume.md) §1.3 (well-bracketing), §1.4 (binders and
  equivariance), §4 (what the literature has on borrows across suspension).
- `~/repos/borrow-core/survey.md`; `~/repos/borrow-core/docs/prior-art-sessions.md`.

**Marks.** **[read]** means the passage was read in the primary source's full text for this note.
**[abstract]** means only the abstract or the venue page was read. **[repo]** means the claim is
taken from one of the documents above. **unverified** means it was recalled, not checked.

---

## 1. Program logics for effect handlers: Hazel and its descendants

- **Hazel.** de Vilhena & Pottier, *A Separation Logic for Effect Handlers*, PACMPL 5 (POPL)
  2021, <https://doi.org/10.1145/3434314>.
  - **Mechanism.** Protocols transfer separation-logic resources at `perform` (`P`) and at
    `resume` (`Q`). A captured continuation is a non-persistent wand, so "a captured
    continuation can be invoked at most once", and that is what buys the frame rule [repo: p10
    §1.4].
  - **Lifetimes.** There are none. A borrow is modelled as full ownership transfer through the
    protocol and back. Time is the order of reduction steps only (Iris step-indexing).
  - **Suspension.** Arbitrary owned state can sit in a suspended continuation, with no side
    condition.
  - **Negative.** One-shot is load-bearing: with a persistent continuation, the frame rule fails
    (authors' remark, [repo]).
- **Descendants.**
  - **TES.** de Vilhena & Pottier, ESOP 2023 [repo].
  - **Affect.** van Rooij & Krebbers, POPL 2025, <https://doi.org/10.1145/3704841>. Affine
    values may not be captured in multi-shot continuations. Semantic typing in Iris [repo].
  - **blaze.** de Vilhena, van Collem, Wright & Krebbers, POPL 2026,
    <https://doi.org/10.1145/3776676>. Relational, Iris [repo].
  - **Yarrow.** Mathiasen, Timany & Birkedal, <https://arxiv.org/abs/2607.15876>. Regions with
    one-shot and multi-shot handlers. "Non-local control flow of algebraic effects break[s] the
    stack discipline" [repo: p10 §1.6].
  - **Osiris.** An Iris logic for a fragment of OCaml that includes effect handlers, ICFP 2025,
    <https://iris-project.org/pdfs/2025-icfp-osiris.pdf> [abstract]. No lifetimes.
  - **Extensible program logics.** Zhang, Gregersen & Tassarotti,
    <https://arxiv.org/abs/2607.12642> [abstract]. Handlers are used to *build* program logics
    (concurrency, crash recovery), not to reason about borrows.
  - **ESL.** Song, Foo & Chin, *Specification and Verification for Unrestricted Algebraic
    Effects and Handling*, ICFP 2024, <https://www.comp.nus.edu.sg/~yahuis/ICFP2024.pdf>
    [abstract]. Zero-, one- and multi-shot continuations combined with imperative effects. Not
    Iris; no lifetimes.
- **Mechanised?** Hazel, TES, Affect, blaze, Yarrow and Osiris are in Iris/Coq (Rocq). ESL:
  unverified.
- **Common shape.** Ownership in a continuation is solved by *not having lifetimes*. Every model
  that admits heap ownership in a resumable continuation restricts it to one-shot or affine.

## 2. RustBelt, the lifetime logic, and what it does not cover

- **RustBelt.** Jung, Jourdan, Krebbers & Dreyer, POPL 2018,
  <https://people.mpi-sws.org/~dreyer/papers/rustbelt/paper.pdf> [read, §9].
  - **What a lifetime is.** A ghost name with a fractional token `[κ]_q`; `κ ⊑ κ'` is a proved
    persistent fact, not a position in an order; full borrows; inheritances `[†κ] ⇛ ▷P`.
    Function calls thread the tokens they hold back to the caller [repo: p10 §1.14].
  - **What it leaves out.** The paper's own list: relaxed atomics, trait objects, "stack
    unwinding when a panic occurs", and automatic destruction [read]. Generators, `async` and
    `Pin` are not in λRust [read: none are mentioned].
- **RustHornBelt.** Matsushita, Denis, Jourdan & Dreyer, PLDI 2022,
  <https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf> [abstract].
  - It adds *parametric prophecies*: the final value of a `&mut` is prophesied at creation and
    resolved when the borrow ends. Mechanised in Coq.
  - This is a second way to avoid placing lifetimes: a borrow's end is a future *value*, not a
    position.
  - No async or generators: unverified, but none are listed.
- **RefinedRust.** Gäher et al., PLDI 2024,
  <https://iris-project.org/pdfs/2024-pldi-refinedrust.pdf> [read, §5].
  - It uses RustBelt's lifetime logic and adds "pinned borrows that allows temporarily weakening
    the type under a mutable reference". This is unrelated to `std::pin`.
  - Adequacy is Theorem 5.1. No async.
- **`Pin`.** Ralf Jung, *A Formal Look at Pinning*, 2018,
  <https://www.ralfj.de/blog/2018/04/05/a-formal-look-at-pinning.html> [read].
  - It proposes a third typestate `T.pin(ptr)` in RustBelt's model.
  - It is a blog-level proof sketch, not mechanised.
- **GhostCell.** Yanovski, Dang, Jung & Dreyer, ICFP 2021 (unverified details).
  - Uses a branded lifetime `'id` as an existential, *nominal* token separating permission from
    data. Proved in RustBelt.
  - No suspension.
- **Search result.** No Iris-based work verifying async Rust, Rust generators or `Pin` was found.
  This agrees with p10 §1.14. It is a search result, not a proof of absence.
- **Assumption about time.** No global order. Lifetimes are created fresh and related only by
  proved inclusions, and the whole construction is step-indexed (Iris `▷`).

## 3. Kripke logical relations, worlds and naturality

- **Possible-world semantics.** Oles and Reynolds; O'Hearn & Tennent, *Parametricity and Local
  Variables*, JACM 42(3) 1995 (<https://surface.syr.edu/eecs_techreports/158>, [abstract]).
  - Worlds are store shapes, and a morphism is an expansion of the store.
  - O'Hearn–Tennent require relation-preserving functors: "a non-local procedure is independent
    of locally-declared variables in the same way that a parametrically polymorphic function is
    independent of types".
  - **What a "lifetime" is.** The local variable's *world*, related by injections, with no order
    beyond inclusion.
- **Names.** Pitts & Stark's ν-calculus; Stark's parametric functors.
  - Benton, Hofmann & Nigam, *Proof-Relevant Logical Relations for Name Generation*,
    <https://arxiv.org/abs/1708.05193> [abstract; authors unverified].
  - **Negative.** With recursion over domains, "the direct-style construction of the allocation
    monad no longer works". The earlier fix combined allocation with continuations.
- **Full ground references.** Kammar, Levy, Moss & Staton, *A Monad for Full Ground Reference
  Cells*, LICS 2017, <https://arxiv.org/abs/1702.04908> [abstract]. A monad on a functor
  category of worlds, with encapsulation as a separate monad.
- **Kripke logical relations with state transition systems.**
  - Ahmed, Dreyer & Rossberg, *State-Dependent Representation Independence*, POPL 2009,
    <https://home.ttic.edu/~amal/papers/sdri/> [abstract]: step-indexed possible worlds.
  - Dreyer, Neis & Birkedal, *The Impact of Higher-Order State and Control Effects on Local
    Relational Reasoning*, ICFP 2010 / JFP 2012,
    <https://people.mpi-sws.org/~dreyer/papers/stslr/journal.pdf> [read, §1, §4, §5]. The key
    negative result for us:
    - **Reasoning from stack discipline fails under first-class control.** Several of ADR's
      examples "rely on the well-bracketed nature of computation—i.e., the assumption that
      control flow follows a stack-like discipline—an assumption that is only valid in the
      absence of call/cc". Private transitions and inconsistent states "are only sound in the
      absence of call/cc".
    - **Counterexample.** In §5, a context captures `k` during the second callback, resets
      `x := 0`, and throws back to `k`. That distinguishes `x:=0; f; x:=1; f; !x` from
      `f; f; 1`.
    - **One-shot does not restore it under higher-order state.** Friedman–Haynes encode call/cc
      with one-shot continuations by keeping a fresh one-shot continuation in a private ref cell
      (§4).
  - Timany, Guéneau & Birkedal, *The Logical Essence of Well-Bracketed Control Flow*, POPL
    2024, <https://cs.au.dk/~timany/publications/pub_pages/2024-popl-wbcf/> [read, §7].
    - Well-bracketedness becomes a separation-logic resource, mechanised in Iris.
    - Extending it to handlers is a **conjecture**: "We conjecture that it is the case" for
      "innocuous" call/cc or handlers marked by protocols.
- **Naturality under ordered names.** Bojańczyk, Klin & Lasota, *Automata Theory in Nominal
  Sets*, LMCS 10(3) 2014, <https://arxiv.org/abs/1402.0897> [read, Ex. 2.3].
  - Ordered atoms are taken to be `(ℚ, <)` with monotone bijections ("total order symmetry").
  - The integer symmetry `(ℤ, translations)` is kept "as a source of pathological
    counterexamples".
  - Our observation: `(ℕ, <)` has no non-trivial order automorphism, and successor (adjacency)
    is definable from `<`. A nominal (equivariant) reading of ordered names therefore uses a
    dense, homogeneous order, not `ℕ`.
  - Pitts lists equivariance under ordered renamings as open (2016 §9) [repo: i2 §4].

## 4. Region calculi

- **Tofte–Talpin.** Information and Computation 1997, <https://doi.org/10.1006/inco.1996.2613>.
  - `letregion` is lexical and LIFO: regions form a stack, and a region *is* its position.
  - No control operators [repo: suspension-borrows §5.1].
- **Capability calculus.** Crary, Walker & Morrisett, POPL 1999; Walker, Crary & Morrisett,
  TOPLAS 2000, <https://www.cs.princeton.edu/~dpw/papers/capabilities-toplas.pdf> [abstract].
  - CPS throughout. Regions are named by type variables, and a continuation takes the
    capabilities it needs as arguments.
  - "Region lifetimes need not be lexically scoped". Freeing is explicit.
  - Soundness is syntactic. A region is a *name plus a capability*, never a position.
- **Cyclone.** Grossman et al., PLDI 2002 [repo]; Fluet, Morrisett & Ahmed's dynamic regions.
  - Region names with an outlives *partial* order; dynamic regions are first-class.
  - Fluet et al. are quoted [read, in Schuster et al. §7]: "Dynamic regions are not restricted
    to LIFO lifetimes … particularly well suited for … CPS-based computations … where lexical
    regions do not suffice."
- **Linear regions and L3.**
  - Fluet, Morrisett & Ahmed, *Linear Regions Are All You Need*, ESOP 2006.
  - Ahmed, Fluet & Morrisett, *L3: A Linear Language with Locations*, Fundamenta Informaticae
    2007, with a step-indexed model of substructural state (ICFP 2005).
  - Regions and locations are existentially packed names with linear capabilities. All details
    unverified.
- **Regions in CPS with exceptions.** Schuster, Brachthäuser & Ostermann, *Region-based Resource
  Management in Continuation-Passing Style*, ESOP 2022,
  <https://pl.cs.uni-tuebingen.de/publications/schuster22region.pdf> [read, §1, §7].
  - Lexical regions ("a stack of regions which corresponds to nested scopes") and lexically
    scoped exceptions, translated to CPS. Region variables carry subregion evidence `r ⊑ ρ`.
  - Proved: well-typedness and semantics are preserved. The proof is a paper proof
    (unverified whether mechanised).
  - Exceptions are *abortive only*: no resumption.
- **Monadic regions.** Kiselyov & Shan [repo]: rank-2 encapsulation, so a region name is
  existential.
- **Common shape.** Calculi whose region *is* its stack position (Tofte–Talpin, lexical CPS
  regions) admit only abortive control. Calculi that admit CPS and first-class continuations
  name regions abstractly and thread capabilities.

## 5. Loans, provenances and places: Oxide, Polonius, LLBC/Aeneas; Vale as a contrast

- **Oxide.** Weiss, Gierczak, Patterson & Ahmed (arXiv v1 with Matsakis),
  <https://arxiv.org/abs/1903.00982> [abstract].
  - "Lifetimes as an approximation of the provenances of references": a provenance is a set of
    loans, and borrow checking is a substructural judgment over places.
  - Syntactic progress and preservation. Mechanisation: unverified (abstract silent).
  - No closures capturing borrows across suspension, no async: unverified.
- **Polonius.** <https://rust-lang.github.io/polonius/>; current notes at
  <https://doc.rust-lang.org/stable/nightly-rustc/rustc_borrowck/polonius/index.html>.
  - Origins are sets of loans, computed by Datalog, location-sensitive. An origin is *what was
    borrowed*, not *when*.
  - No published soundness proof was found (unverified).
- **LLBC / Aeneas.** Ho, Fromherz & Protzenko, *Sound Borrow-Checking for Rust via Symbolic
  Semantics*, ICFP 2024, <https://arxiv.org/abs/2404.02680> [read, §§1–4].
  - **Mechanism.** Values carry loan and borrow identifiers. At a call, "for each lifetime, a
    fresh region ρ is introduced together with A(ρ) ('the region abstraction of ρ')". A region
    is a *bag* of loans and borrows.
  - **Ending a region.** It can end once it holds no loans, and merging two abstractions is
    "lifetime weakening".
  - **The proofs.** Pen-and-paper, in appendices [read: proofs "in Appendix A/B"].
  - **Scope.** Loops are new in this paper. Closures and async are absent (unverified).
- **What a loan-set model would offer a suspension** (observation, [read]). A region
  abstraction is defined by its contents, so moving a suspended region past another changes
  nothing that LLBC# can read. Its rules check dependencies between abstractions (cycles get
  stuck, §4), not their positions.
- **Vale group borrowing.** <https://verdagon.dev/blog/valen-group-borrowing> [read].
  - Path-based invalidation: mutating `x` invalidates references *into* `x`.
  - A design with no formal model or soundness claim, and nothing on suspension.

## 6. Session types, coroutines and projections with ownership

- **Ferrite.** Chen, Balzer & Toninho, ECOOP 2022, <https://arxiv.org/abs/2205.06921>
  [abstract]. An embedding in Rust of SILL_S (linear and shared sessions; acquire/release
  modalities). Ownership is per channel; no lifetimes in the calculus.
- **BGV.** *Borrowing From Session Types*, OOPSLA 2025,
  <https://2025.splashcon.org/details/OOPSLA/199/Borrowing-From-Session-Types> [abstract].
  - "Founded on ordered linear typing … with an explicit operation for splitting ownership of
    channels". Soundness is by translation to deadlock-free PGV.
  - Only the external-language translation is stated as mechanised.
  - **Note.** Here the *order* is the ordered-logic context order, not a lifetime order.
- **Kokke.** *Rusty Variation*, ICE 2019 (unverified): deadlock-free sessions with failure in
  Rust, built on affine session types. Borrows play no formal role.
- **Hylo projections / Swift `_read` and `modify` coroutines.**
  - No mechanised formal model was found.
  - *Borrow checking Hylo* (IWACO 2023,
    <https://2023.splashcon.org/details/iwaco-2023-papers/5/Borrow-checking-Hylo>) describes an
    abstract interpreter over Hylo IR with ghost lifetime instructions [abstract].
  - The yield-once projection ends its access before the caller resumes [repo: p10 §1.2].

## 7. Graded and uniqueness lineage

- **Linearity and Uniqueness.** Marshall, Vollmer & Orchard, *Linearity and Uniqueness: An
  Entente Cordiale*, ESOP 2022 (venue page not fetched; unverified details). Uniqueness as the
  dual of linearity in Granule.
- **Fractional Uniqueness.** Marshall & Orchard, *Functional Ownership through Fractional
  Uniqueness*, OOPSLA 2024, <https://arxiv.org/abs/2310.18166> [read, §§4–6].
  - **Mechanism.** Borrows are a graded modality `&_p` with fractional `p`. "withBorrow …
    encapsulating the mutable borrow behaviour inside a continuation", so no closed term has a
    borrowed type.
  - **Lifetimes.** Identifiers "packed in an existential"; "we only support lexical lifetimes".
  - **Proofs.** Paper progress, preservation, borrow safety and soundness for the equational
    theory (Thms 6.6–6.11). Mechanisation: unverified (none seen).
  - **Suspension.** None.
- **Granule** (Orchard, Liepelt & Eades, ICFP 2019) has graded effects and coeffects. No work on
  suspension holding a borrow was found.

---

## 8. Table

| model | a lifetime/region IS | handles control/suspension? | assumes | mechanised? | key negative result |
|---|---|---|---|---|---|
| Hazel / TES / Affect / blaze / Osiris | nothing (ownership only; a borrow = transfer and return) | yes: deep handlers, resources inside `k` | one-shot (Hazel); affine-only in multi-shot (Affect); step-indexing | Iris/Coq | persistent `k` breaks the frame rule (Hazel) |
| Yarrow | owned region, fixed locations | yes: one-shot and multi-shot | step-indexing; temporary revocation | Iris/Rocq [repo] | handlers "break the stack discipline" |
| RustBelt lifetime logic | ghost **token** `[κ]_q`; inclusion is a proved fact | no: no unwinding, async, generators or `Pin` | step-indexing; tokens returned at call exit | Iris/Coq | call rule "give tokens back on return" has no delayed return [repo] |
| RustHornBelt | token plus **prophecy** of the final value | no | prophecy resolution at borrow end | Iris/Coq | none on control (unverified) |
| `Pin` typestate (Jung 2018) | token; `pin` is a third typestate | address side only | RustBelt model | no (sketch) | — |
| O'Hearn–Tennent / Oles / ν-calculus | a **world** (store shape), morphisms = injections | no (Algol-like) | naturality over all injections | no | direct-style allocation monad fails with recursion (BHN) |
| ADR / DNB Kripke STS | island or STS state, step-indexed | call/cc: yes, but losing stack-discipline reasoning | biorthogonality | partly (DNB technical appendix) | private transitions unsound with call/cc; one-shot plus higher-order state encodes call/cc |
| TGB 2024 well-bracketing | well-bracketing as a resource | concurrency: yes; handlers: conjectured | Iris | Iris/Coq | extension to handlers only conjectured |
| Nominal sets with ordered atoms | **position** in a dense homogeneous order `(ℚ,<)` | — | homogeneity | — | ℤ-translations "pathological"; ℕ has no non-trivial symmetry |
| Tofte–Talpin; lexical CPS regions (Schuster et al.) | **position** on a region stack (lexical) | abortive only (exceptions) | LIFO | no | — |
| Capability calculus (CWM) | **existential** name plus linear capability | yes: CPS, capabilities passed to `k` | explicit free; no LIFO | no (syntactic) | — |
| Cyclone / dynamic and linear regions / L3 | name with outlives **partial** order; existentially packed | dynamic regions "suited for CPS" | uniqueness or linear capabilities | L3 model on paper (unverified) | — |
| Oxide / Polonius | **set of loans** (provenance or origin) | no | flow-sensitive analysis over places | Oxide: unverified; Polonius: none found | — |
| LLBC / Aeneas | **bag** of loans/borrows (region abstraction) | no (loops only) | no cyclic dependencies between abstractions | paper proofs | symbolic execution can get stuck on cyclic merges |
| Vale group borrowing | **path** | no | — | no (design) | — |
| Ferrite / BGV / Kokke | channel ownership; ordered context (BGV) | sessions are suspension by nature, but no borrows *of data* across them | linear or ordered logic | BGV: translation only | — |
| Fractional Uniqueness (Granule) | **existential identifier**, lexical | no | borrow scoped by a continuation | no (paper) | lexical lifetimes only |

## 9. NEGATIVE RESULTS

1. **Hazel** (POPL 2021): a persistent (multi-shot) continuation invalidates the frame rule, so
   resources in `k` require one-shot [repo, p10 §1.4].
2. **Affect** (POPL 2025) and **Tang et al.** (POPL 2024): affine or linear values captured in
   multi-shot continuations are unsound; Links had such a bug [repo].
3. **Dreyer–Neis–Birkedal** (ICFP 2010 / JFP 2012) [read]:
   - reasoning that depends on stack discipline (private transitions, inconsistent states) is
     unsound with call/cc;
   - the "callback with lock" equivalence "simply does not hold in the presence of call/cc".
4. **Dreyer–Neis–Birkedal §4, Friedman–Haynes** [read]: one-shot continuations plus higher-order
   state encode full call/cc. One-shot alone does not restore well-bracketing.
5. **Timany–Guéneau–Birkedal** (POPL 2024) [read]: a well-bracketing logic for handlers is a
   stated conjecture, not a result.
6. **Yarrow** (2026) [repo]: "non-local control flow of algebraic effects break[s] the stack
   discipline" of regions.
7. **RustBelt** (POPL 2018) [read]: unwinding is not modelled. Async, generators and `Pin` are
   outside λRust. No mechanised successor was found.
8. **Benton–Hofmann–Nigam** [abstract]: the direct-style allocation monad over name-worlds
   breaks once recursion is added; proof-relevance is needed.
9. **Bojańczyk–Klin–Lasota** (LMCS 2014) [read]:
   - well-behaved ordered atoms are `(ℚ,<)`;
   - the integer symmetry is the stock source of pathologies;
   - `(ℕ,<)` admits only the identity automorphism, so "equivariance" over it is vacuous.
10. **Pitts** (2016, §9) [repo]: equivariance under ordered renamings is listed as open.
11. **Fractional Uniqueness** (OOPSLA 2024) [read]: lexical lifetimes only; a borrow cannot
    escape its `withBorrow` continuation.
12. **LLBC#** (ICFP 2024) [read]: merging region abstractions can create cyclic dependencies
    that leave symbolic execution stuck.
13. **Search result, not a theorem**: no mechanised model of lifetime-indexed borrows live
    across a resumable suspension was found. This agrees with i2 §4 and p10 §4.

## 10. What this says about our adjacency problem

Observations only.

- **Models that never read where a lifetime sits:**
  - tokens (RustBelt, GhostCell);
  - prophecies (RustHornBelt);
  - ownership with no lifetimes (Hazel, Affect, Yarrow);
  - existential names with capabilities (CWM, L3, Fractional Uniqueness);
  - loan sets or bags (Oxide, Polonius, LLBC#);
  - worlds under injections (O'Hearn–Tennent).
- **What they pay:**
  - **Step-indexing:** every token or Iris model; ours avoids it through strata (`no_nonstrict_stratum`).
  - **One-shot or affine continuations:** Hazel, Affect.
  - **No semantic model at all:** loan sets, which are syntactic or paper proofs.
  - **Explicit capability threading and no LIFO:** CWM.
  - **Lexical scope only:** Fractional Uniqueness.
- **Models that do read position all assume LIFO.** Tofte–Talpin and lexical CPS regions both
  read stack position, and both admit only abortive control. No positional model handles
  resumption.
- **DNB is the closest negative analogue.** Stack-discipline reasoning breaks under first-class
  control, and one-shot plus higher-order state does not repair it. Our `ℕᵒᵈ` strata are a form
  of well-bracketing. Whether linear continuations without stored `κ` escape the Friedman–Haynes
  encoding was not checked.
- **The nominal literature takes ordered names to be dense.** It uses `(ℚ,<)` with monotone
  bijections. On `ℕ` adjacency is definable from `<`, which matches `coreAllAdjacent`.
  Invariance under all order-embeddings, the reading §4.2 calls for, is what that literature gets
  from density.
- **The cut in the literature.** No surveyed model keeps a *total positional order* of lifetimes
  and also admits resumption. Every model that admits resumption gives up position for names,
  tokens or contents.
