## Linear logic as concurrency: prior-art report for borrow-core

**How to read the citations.** "(verified)" means this session found the bibliographic record and an abstract or summary. Except for one listing page, nothing was read in full text, so technical details beyond the abstracts rest on my background knowledge. "(unverified)" means I did not find the item this session. I made no repo edits and sent no identifiers anywhere.

---

### 1. Caires and Pfenning, intuitionistic linear session types
**Citations.**
- *Session Types as Intuitionistic Linear Propositions*, CONCUR 2010, LNCS 6269, pp. 222–236 (verified).
- Journal version with Toninho: *Linear Logic Propositions as Session Types*, MSCS 26(3), 2016, pp. 367–423 (verified).

**What it gives.** Session fidelity, global progress (deadlock freedom) and termination, for tree-shaped process networks. Races are absent: each linear channel has exactly one provider and one client.

**Logic.** Dual intuitionistic linear logic (DILL), with a two-zone context: an unrestricted zone and a linear zone. A process provides exactly one channel (the right of the sequent) and uses many (the left). The operational correspondence is "cut-reduction is communication".
- ⊗ sends a channel.
- ⊸ receives one.
- & offers a choice (external).
- ⊕ selects (internal).
- 1 closes.
- ! is a replicated server.

The two-zone context is already a two-mode adjoint structure. It is Benton's LNL in sequent form (LNL unverified).

**Functional host.** None in this paper.

**Proof status.** Paper proofs only; nothing mechanised.

**How it maps onto us.** The intuitionistic single-provider discipline fits an intuitionistic CBPV host directly. Our codata `&` product is exactly the session `&`: an offer of methods. We lack:
- channels as a value type;
- duality;
- a fork operation that is the cut, i.e. creates a channel and spawns a process in one step.

### 2. SILL and the monadic integration (Toninho, Caires and Pfenning)
**Citations.**
- *Higher-Order Processes, Functions, and Sessions: A Monadic Integration*, ESOP 2013, LNCS pp. 350–369, DOI 10.1007/978-3-642-37036-6_20 (verified).
- Pfenning and Griffith, *Polarized Substructural Session Types*, FoSSaCS 2015, DOI 10.1007/978-3-662-46678-0_1 (verified). This adds an affine variant and polarised, asynchronous SILL.

**What it gives.** Type preservation, and global progress in the higher-order setting, which the authors say is new.

**Logic.** The functional layer is intuitionistic and unrestricted. A linear contextual monad `{c:A ← P ← d̄:B̄}` embeds open process expressions as first-class functional values. This is an adjoint split, a functional mode over a linear mode, and close to CBPV's F/U adjunction.

**Functional host.** Through that monad, so concurrency stays in its own type.

**Proof status.** Paper proofs only.

**How it maps onto us.** This is the closest template for a CBPV kernel. The contextual monad corresponds to a computation type whose effect row contains the session operations. Our version would be a thunk of a computation that, under the scheduler handler, provides one channel and consumes a context of channels. We lack:
- the contextual typing of channel names;
- a proof that handler-based interpretation of send and receive keeps the progress argument, which is tied to cut.

### 3. Wadler's CP and GV
**Citation.** *Propositions as Sessions*, ICFP 2012; JFP 24(2–3), 2014, pp. 384–418 (verified).

**What it gives.** Deadlock freedom; the JFP abstract adds race freedom. Both follow from cut, which fuses channel creation with parallel composition.

**Logic.** CP is classical linear logic, one-sided, with symmetric duality.
- ⅋ types receiving.
- ⊗ types sending.
- Parallel composition is the cut, not ⅋.

GV is a linear functional language translated into CP.

**Proof status.** Paper proofs.

**On "classical against intuitionistic".** The two have been related formally:
- Lindley and Morris's GV↔CP translations (§4).
- Jaramillo, Frumin and Pérez, *Around Classical and Intuitionistic Linear Processes*, arXiv 2407.06391, 2024 (verified as existing). It relates the two through Laurent's CLL→ILL translation.

So the choice is largely one of presentation. The intuitionistic (provider) view fits a functional host better.

**"This is just adjoint": only partly so.** Adjoint logic, in Pruiksma and Pfenning's formulation (§5), is intuitionistic. It unifies the *structural* modes: linear, affine, strict, unrestricted. It does not by itself dissolve the classical/intuitionistic split, which is about duality and polarity. I did not find a classical adjoint session calculus this session.

### 4. GV: Gay and Vasconcelos; Lindley and Morris; Links
**Citations.**
- Gay and Vasconcelos, *Linear Type Theory for Asynchronous Session Types*, JFP 20(1), 2010, pp. 19–50 (verified). This is a buffered semantics with buffer bounds read from session types. It does not by itself guarantee deadlock freedom.
- Lindley and Morris, *A Semantics for Propositions as Sessions*, ESOP 2015, LNCS pp. 560–584, DOI 10.1007/978-3-662-46669-8_23 (verified). It gives GV a small-step semantics and proves well-typed GV deadlock-free, deterministic and terminating. Its translations GV→CP and CP→GV both preserve reduction.
- Lindley and Morris, *Sessions as Propositions*, PLACES 2014, introducing HGV (verified as existing).
- Lindley and Morris, *Lightweight Functional Session Types*, in *Behavioural Types: from Theory to Tools*, River Publishers, 2017, pp. 265–286 (verified record). It integrates row types with session types in Links.
- Fowler, Lindley, Morris and Décova, *Exceptional Asynchronous Session Types: Session Types without Tiers*, PACMPL 3 (POPL) article 28, 2019, DOI 10.1145/3290341 (verified). Asynchronous sessions plus exceptions in Links; the abstract says they preserve progress, deadlock freedom, confluence and termination. The implementation "draws on existing work on effect handlers".

**Functional host.** Natively. Channels are linear values and `fork` is the cut.

**Proof status.** Paper proofs.

**How it maps onto us.** Here channels are first-class values, the effects-friendly option. It needs a `fork : (S ⊸ end) → S̄` discipline. A separate `new` combined with an arbitrary fork loses deadlock freedom.
- Kokke and Dardha's *Prioritise the Best Variation* (PGV), LMCS 2023, arXiv 2103.14466 (verified), separates `new` from `fork` and restores deadlock freedom with priorities.
- If a scheduler handler exposes `new` and `spawn` separately, PGV-style priorities, or GV's fused fork, are needed.

### 5. Adjoint session types (Pruiksma and Pfenning) and Rast
**Citations.**
- *A Message-Passing Interpretation of Adjoint Logic*, PLACES 2019, EPTCS 291, pp. 60–79, doi:10.4204/EPTCS.291.6; JLAMP 120:100637, 2021; arXiv 1904.01290 (all verified).
- Related:
  - *Back to Futures*, JFP 2022, arXiv 2002.04607 (verified). The language is Seax; it adds sequential composition, futures, fork/join and monadic concurrency.
  - DeYoung, Pfenning and Pruiksma, *Semi-Axiomatic Sequent Calculus*, FSCD 2020 (verified).
  - Pfenning and Pruiksma, *Relating Message Passing and Shared Memory, Proof-Theoretically*, COORDINATION 2023, LNCS 13908, pp. 3–27 (verified record).
  - Pruiksma's PhD thesis, *Adjoint Logic with Applications*, CMU-CS-24-103, 2024 (verified).
- Rast: Das and Pfenning, FSCD 2020, LIPIcs 167:33; LMCS 2022 (verified). It adds arithmetic refinements and work/span types.

**What it gives.** The abstract states proved session fidelity and deadlock freedom, plus a logically justified garbage collection. The calculus covers multicast, replicable services and cancellation.

**Logic.** Intuitionistic. Modes form a preorder, each mode has its own structural rules, and shifts ↑/↓ move between modes. The four modes are linear, affine, strict and unrestricted.

**Proof status.** Paper proofs only.

**How it maps onto us. This is the direct answer to "it's just adjoint".**
- Our three qualifiers (must resume, cancellable, unrestricted) line up with three of their four modes (linear, affine, unrestricted).
- CBPV's F/U is itself an adjunction.
- Their affine mode is what gives cancellation. That matters for handlers that discard continuations.
- Seax/SAX shows the same logic read as either message passing or shared memory, which bears on a sequential CBPV host.

We lack mode-indexed shifts as first-class connectives, and strict mode.

### 6. Manifest sharing (Balzer and Pfenning; Balzer, Toninho and Pfenning)
**Citations.**
- *Manifest Sharing with Session Types*, PACMPL 1 (ICFP) article 37, 2017, DOI 10.1145/3110281 (verified). Types are stratified into a linear layer and a shared layer, joined by modal shifts: acquire is ↑SL and release is ↓SL. Session fidelity and data-race freedom hold; deadlock freedom does *not*.
- *Manifest Deadlock-Freedom for Shared Session Types*, ESOP 2019, LNCS 11423, DOI 10.1007/978-3-030-17184-1_22 (verified). It restores deadlock freedom by tracking acquire order in types.
- The CONCUR 2018 follow-up embeds the untyped asynchronous π-calculus through a universal shared type (verified as existing).

**Logic.** Adjoint: two modes with shift modalities.

**How it maps onto us. This is the strongest structural analogue of a lexical lend block.**
- Acquire begins a critical region and release ends it.
- An equi-synchronising discipline requires the shared session to be released at the same type it was acquired at.
- That resembles a `mut` lend that must hand the resource back intact.

There is no analogue of `imm` (many readers), no lifetimes and no outlives order.

### 7. Shared state inside the logic (Rocha and Caires); client–server
**Citations.**
- Rocha and Caires, *Propositions-as-Types and Shared State*, ICFP 2021 (verified). The abstract claims session fidelity, progress, confluence and normalisation, with first-class shareable reference cells; it draws on differential linear logic.
- Rocha and Caires, *Safe Session-Based Concurrency with Shared Linear State*, ESOP 2023, DOI 10.1007/978-3-031-30044-8_16 (verified). Language CLASS; mutex-protected cells.
- Qian, Kavvos and Birkedal, *Client-Server Sessions in Linear Logic*, PACMPL 5 (ICFP) article 62, 2021 (verified). Coexponentials; the functional language is translated by the call-by-value embedding.

**How it maps onto us.** Both lines share state while staying in the propositions-as-types discipline. Neither has borrows or lifetimes. CLASS's mutex cells are the closest relative of a `mut` borrow over shared state.

### 8. Proof routes
- **Pérez, Caires, Pfenning and Toninho**, *Linear Logical Relations for Session-Based Concurrency*, ESOP 2012 (verified). Journal version: *…and Observational Equivalences…*, Information and Computation 239, 2014 (verified).
  - A unary logical relation gives strong normalisation; a binary one gives confluence and observational equivalence.
  - There is no step index, since the language has no general recursion.
  - Paper proof.
- **Balzer, Derakhshan et al.**, *Logical Relations for Session-Typed Concurrency*, arXiv 2309.00192 (verified). Earlier: Derakhshan and Balzer, *Recursive Session Logical Relations*, arXiv 2208.13741 (verified).
  - Progress-sensitive noninterference for intuitionistic linear session types *with recursion*, via biorthogonality.
  - The relation is indexed by *observations*, not steps, to stay closed under parallel composition.
  - Paper proof.
- **Hinrichsen, Bengtson and Krebbers**, *Actris*, PACMPL 4 (POPL) article 6, 2020 (verified); *Actris 2.0*, LMCS 2022 (verified).
  - A separation logic with session-type protocols.
  - Mechanised in Coq on Iris; proves functional correctness, not deadlock freedom.
- **Hinrichsen, Louwrink, Krebbers and Bengtson**, *Machine-Checked Semantic Session Typing*, CPP 2021, DOI 10.1145/3437992.3439914 (verified).
  - **A logical-relations model of affine asynchronous session types in Coq/Iris**, with polymorphism, recursion, subtyping, references and locks.
  - It proves type safety. Deadlock freedom is outside an affine model.
- **Jacobs, Balzer and Krebbers**, *Connectivity Graphs: A Method for Proving Deadlock Freedom Based on Separation Logic*, POPL 2022, DOI 10.1145/3498662 (verified).
  - The abstract claims the first mechanised proof of deadlock and leak freedom for a higher-order binary session-typed language, in Coq.
  - Multiparty GV appeared at ICFP 2022 (verified). Which proof assistant it uses was not confirmed.
- **Jacobs, Hinrichsen and Krebbers**, *Deadlock-Free Separation Logic* (LinearActris), PACMPL 8 (POPL) article 47, 2024, DOI 10.1145/3632889 (verified).
  - Deadlock and leak freedom from linearity alone.
  - A step-indexed model over connectivity graphs; soundness of a GV-style type system via logical relations; Coq.
- **Thiemann**, *Intrinsically-Typed Mechanized Semantics for Session Types*, PPDP 2019, arXiv 1908.02940 (verified). Agda, an intrinsically typed CEK machine; preservation and a form of progress.
- **Sano, Kavanagh and Pientka**, *Mechanizing Session-Types using a Structural View*, OOPSLA 2023, arXiv 2309.12466 (verified). Beluga; CLL sessions; preservation.
- **Lean.** I found no mechanisation of session types, GV or CP in Lean.

### 9. Session types and effects/handlers together
- **Orchard and Yoshida**, *Effects as Sessions, Sessions as Effects*, POPL 2016, DOI 10.1145/2837614.2837634 (verified). Encodings in both directions between an effect-typed PCF and a session π-calculus, plus a Haskell implementation.
- **Tang, Hillerström, Lindley and Morris**, *Soundly Handling Linearity*, PACMPL 8 (POPL), 2024, pp. 1600–1628, DOI 10.1145/3632896 (verified).
  - **This is the key hazard paper.** Handlers that drop or duplicate continuations break linearity, and this caused a real soundness bug in Links, whose sessions plus handlers were unsound.
  - The fix is *control-flow linearity*: a continuation that captures linear resources must be resumed exactly once.
  - Calculi F°eff and Q°eff; paper proofs.
- **Wenhao Tang**, *Session-Typed Effect Handlers*, POPL 2024 Student Research Competition (verified, abstract only). A CBPV calculus λ^ch_eff whose effect system is inspired by session types. No full paper found.
- Fowler et al., POPL 2019 (§4): exceptions and cancellation over sessions, implemented with handlers.

**T1 correspondence.** T1 ("an operation that resumes cannot cross a borrow") is a cousin of control-flow linearity. Both restrict what a captured continuation may hold across a perform/resume. Theirs: a linear resource in a continuation forces exactly-once resumption. Ours: a borrow forbids capture by a resuming operation.

So `send` and `recv` performed as effects would be resuming operations, and under T1 *a borrow could not be held across a communication*. That is consistent with the lexical-lend reading, but it means "lending over a channel" cannot be a plain perform inside a lend block. This is my inference, not a published result.

### 10. Session types with borrowing
- **Saffrich, Spaderna, Thiemann and Vasconcelos**, *Borrowing From Session Types*, PACMPL 9 (OOPSLA2), 2025, pp. 3426–3453, DOI 10.1145/3763173 (verified; abstract only). This is the same PACMPL volume as Wagner et al.
  - **The calculus is BGV.** Ordered linear typing plus an explicit operation that splits ownership of a channel.
  - A borrowed session type ends in a `Return` marker, after which the endpoint goes back to its owner. Exhausted borrows are explicitly dropped. (The `Return` and drop details come from a search summary, not the full text.)
  - **Proofs.** Type safety and deadlock freedom come by a type-preserving translation into PGV. The translation from the surface borrow notation to BGV is mechanised and verified, giving decidable checking; the proof assistant was not identified. A Zenodo artifact exists.
- **Saffrich, Nishida and Thiemann**, *Law and Order for Typestate with Borrowing*, PACMPL 8 (OOPSLA2), 2024, pp. 1475–1503, arXiv 2408.14031 (verified). Ordered types indexed by an ordered partial monoid of transitions, with borrowing; a syntactic soundness proof.
- **Chen, Balzer and Toninho**, *Ferrite: A Judgmental Embedding of Session Types in Rust*, ECOOP 2022, LIPIcs 222:22 (verified). It embeds SILL_S (linear plus shared sessions) in Rust's types. Whether Ferrite lets Rust borrows cross a channel is (unverified).
- **Jespersen, Munksgaard and Larsen**, *Session Types for Rust*, WGP 2015 (verified). Affine endpoints only, so endpoints can be dropped.
- **Voinea, Dardha and Gay** (2019): a channel is split into the channel itself and a separate capability to use it (verified as existing).
- **Marshall and Orchard**, *Functional Ownership through Fractional Uniqueness*, OOPSLA 2024 (title seen; contents unverified).
- **Fractional permissions on session endpoints.** No session-typed calculus with fractional endpoint permissions or read-only (`imm`-style) endpoint borrows turned up.

### 11. Deterministic parallelism by linearity
- **Kuper, Turon, Krishnaswami and Newton**, *Freeze After Writing*, POPL 2014 (verified). LVars are lattice cells with monotonic writes, giving determinism. With `freeze`, programs are quasi-deterministic: the same answer or an error. A Haskell library exists.
- **Bocchino et al.**, *A Type and Effect System for Deterministic Parallel Java*, OOPSLA 2009, pp. 97–116 (verified). Region read/write effects; noninterference of parallel branches gives determinism.
- **"Par as pure parallelism".** In CP, ⅋ types *receiving*, and parallel composition is the cut. Independent parallel composition is "mix", given a typed reading in Kokke, Montesi and Peressotti, *Better Late Than Never* (HCP), PACMPL 3 (POPL) article 24, 2019 (verified). There ⊗ separates hyperenvironments.
- **Mapping to our calculus.** Our `imm`/`mut` borrows are already a DPJ-style noninterference discipline.
  - A fork/join combinator whose branches hold disjoint `mut` borrows and shared `imm` borrows, joined before the lend block ends, would give deterministic parallelism without channels. This corresponds to the mix rule.
  - This is a conjecture: not proved anywhere for BoLo.
  - Its proof need is a parallel-composition case in our logical relation, with world splitting. Our resource algebra already has ⋆.

---

### Synthesis

**The most direct path.** Take the intuitionistic SILL/GV design and read it adjointly.
1. Add a value type of channel endpoints indexed by session types and closed under duality: ⊗ / ⊸ / & / ⊕ / 1 / !, and ν/μ for recursive sessions. Our `&` codata is the offer.
2. Make `fork` the cut, GV style (`fork : U(S̄ → F 1) → F S`), and perform send, receive and fork as operations interpreted by the scheduler handler. Keep `new` and `spawn` fused, or adopt PGV priorities.
3. Treat our qualifiers as Pruiksma–Pfenning modes. Use the affine mode for cancellable sessions, which suits handlers that abort. Model shared servers with Balzer-style shifts (acquire ↑ and release ↓), whose critical regions are lend-like.
4. Make handlers obey Tang et al.'s control-flow linearity whenever continuations hold channels. T1 already states the analogous rule for borrows.

None of this has been done in a CBPV kernel with deep handlers. Closest published: Links (sessions plus handlers, after the POPL 2024 repair), and Tang's SRC abstract (CBPV with session-inspired effect types, no proofs located).

**Has BoLo-style borrowing been combined with session types?** Not that I found.
- The nearest is BGV, *Borrowing From Session Types* (PACMPL 9 OOPSLA2, 3426–3453, DOI 10.1145/3763173). It borrows channel endpoints through ordered types and ownership splitting, but has no lifetimes, no outlives relation, and no imm/mut distinction that I could see in the abstract.
- Ferrite pairs session types with Rust's borrow checker only at the embedding level. Whether borrows cross channels there is unverified.
- Manifest sharing gives a lend-like acquire/release, but no lifetimes.
- I found no work that sends a *borrow* (a lifetime-bounded `imm` or `mut` reference) as a message, with the lender blocked until it returns.

**Recommended proof route, for logical relations in Lean.**
1. **Safety and fidelity first: a unary logical relation, as in CPP 2021 and ESOP 2012.** Extend our world with channel endpoints as linear resources, owned like borrows, and prove fidelity and type safety by our existing fundamental-property and adequacy pattern. Use Pérez et al.'s non-step-indexed relation when sessions are not recursive. With recursive sessions or general recursion, use an observation index (Derakhshan and Balzer) or a step index (Iris-style).
2. **Deadlock freedom does not fall out of a plain logical relation.** It needs a global acyclicity invariant: the connectivity graphs of Jacobs, Balzer and Krebbers (POPL 2022), and LinearActris (POPL 2024), which proves GV soundness *via* logical relations over that invariant. This is the mechanised template to port; it is in Coq, and nothing in Lean was found.
3. **An alternative is proof by translation.** BGV gets deadlock freedom from a type-preserving translation into PGV. If our session fragment translates into a GV or PGV core proved deadlock-free in Lean, only that core needs the graph argument.
4. **Determinism for borrow-disjoint fork/join** would be a separate, cheaper theorem: confluence from ⋆-disjointness. It is conjectured, not established.

**What is proved versus conjectured.**
- *Proved, on paper:* deadlock freedom and fidelity for Caires–Pfenning, CP, GV (Lindley–Morris), adjoint sessions, Balzer et al. 2019, and BGV (via PGV).
- *Proved and mechanised (Coq/Iris, Agda, Beluga):* CPP 2021, POPL 2022, POPL 2024, Thiemann 2019, Sano et al. 2023.
- *Conjectured, ours:* that T1 extends to channel operations; that disjoint-borrow fork/join is deterministic in BoLo; that channels hosted by handlers keep GV's progress argument. None of these has a published counterpart.
