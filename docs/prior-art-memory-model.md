# Prior art for the BoCa/BoLo memory model

This document is for the language designer. It is organised by design question (Q1–Q7). For each question it covers three things: what the literature already settles, what we can reuse directly, and where our setting differs. Our setting is:
- borrows scoped by callbacks (withbor, withload, withswap);
- `imm` cells that carry lifetime sets;
- a Kripke typed world;
- an adequacy theorem that gives both termination and leak-freedom;
- a CBPV core with `!T`;
- targets of C via clang, with verification against Wasm (Talos).

Citation notes: an entry is marked *(abstract only)* or *(secondary)* when the searchers did not read the full text. Venue and year corrections from verification are already applied.

---

## Q1 — Places vs cells; same-lifetime field projection

### What the literature settles

- **A place is a root plus a path, and a loan is keyed by a place.** Oxide defines places as `π ::= x | π.n` and place expressions as `p ::= π | *p | p.n`. A loan is a pair (uniq|shrd, place expression). Two loans conflict when one path is a prefix of, or overlaps, the other. At run time a pointer is a *referent*: a stack variable plus a path, not a heap cell. Oxide deliberately leaves `p[e]` and slices out of the place grammar, so borrowing one element claims the whole array. Weiss, Gierczak, Patterson, Ahmed (2019/2021), *Oxide: The Essence of Rust*, https://arxiv.org/abs/1903.00982. The full paper has no confirmed peer-reviewed venue; an SRC abstract appeared at POPL'19.
- **Same-lifetime projection has a semantic justification, but not in one place.** No single paper states a "projection lemma". Each of these systems justifies it differently:
  - **RustBelt.** A full borrow of `P * Q` splits into full borrows of `P` and of `Q` at the *same* lifetime (LftL-bor-split). The sharing predicate for a product is by definition the separating conjunction of the fields' sharing predicates at their offsets. So `&'a self.f` needs no new lifetime. Jung, Jourdan, Krebbers, Dreyer (2018), *RustBelt: Securing the Foundations of the Rust Programming Language*, https://people.mpi-sws.org/~dreyer/papers/rustbelt/paper.pdf. RustBelt addresses memory by location plus offset. It does not model source places.
  - **RefinedRust.** It adds place types (`place T`, `blocked'a T`, struct and array place types) with unfolding equations. For example, `place(struct T…) = struct(place T…)` gives `struct[blocked'a(i32); place(i32)]` when one field is borrowed. The paper says explicitly that RustBelt "makes no attempt to capture the notion of places". Gäher, Sammler, Jung, Krebbers, Dreyer (2024), *RefinedRust: A Type System for High-Assurance Verification of Rust Programs*, https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf.
  - **RustHornBelt.** Projection is partial prophecy resolution. The sub-borrow's final value is a fresh prophecy, and the parent's final value is its current value with the field set to that prophecy. Matsushita, Denis, Jourdan, Dreyer (2022), *RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code*, https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf.
  - **Pure Borrow.** Borrowers split along borrow paths (field accesses `.i`). A history model records updates `p ← x` at those paths. Matsushita, Ishii (2026), *Pure Borrow: Linear Haskell Meets Rust-Style Borrowing*, https://arxiv.org/abs/2604.15290. The correspondence between its mutative and denotational semantics is stated as Conjecture 5.5, not proved.
- **Value-tree memories with loans at sub-places.** LLBC stores a map from variables to value trees that contain `loan`/`borrow` markers. A mutable borrow of place `p` puts `loan^m l` at `p` and moves `v` into `borrow^m l v`. A reborrow through a reference nests a loan inside a borrow. Ho, Protzenko (2022), *Aeneas: Rust Verification by Functional Translation*, https://dl.acm.org/doi/10.1145/3547647; Ho, Fromherz, Protzenko (2024), *Sound Borrow-Checking for Rust via Symbolic Semantics*, https://arxiv.org/abs/2404.02680.
- **A mechanised "tree per object, permissions at the leaves" memory.** CH2O models each C object as a tree that follows its type (struct, union, array). Pointers are paths through the tree, and the leaves are bits annotated with permissions. Both the permission system and the memory are separation algebras, and it is mechanised in Coq. Krebbers (2016), *A Formal C Memory Model for Separation Logic*, https://arxiv.org/abs/1509.03339; Krebbers (2014), *Separation Algebras for C Verification in Coq*, VSTTE 2014, LNCS 8471, pp. 150–166, https://link.springer.com/chapter/10.1007/978-3-319-12154-3_10.
- **What real Rust tracks.** Place Capability Graphs are computed from MIR. Place nodes carry capabilities. Explicit `unpack`/`pack` edges split a place into its fields and rejoin them. Lifetime projections `p↓'a` stand for the borrows stored inside `p` at region `'a`. PCG covers more than 97% of functions in popular crates. It is a static model; the searchers found no semantic soundness theorem. Grannan et al. (2025), *Place Capability Graphs*, https://arxiv.org/abs/2503.21691.
- **Operational ground truth for what a reference may touch.** Stacked Borrows keeps a stack of tags per location, with the range fixed statically by type and reborrows well nested. Jung, Dang, Kang, Dreyer (2020), *Stacked Borrows*, https://plv.mpi-sws.org/rustbelt/stacked-borrows/. Tree Borrows keeps a tree of tags per allocation, with per-byte state and dynamic ranges. It adds a `Reserved` state for two-phase borrows. Villani, Hostert, Dreyer, Jung (2025), *Tree Borrows*, https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf. RFC 2025 specifies the two-phase borrow itself (`&mut2`): it behaves as shared while reserved and becomes unique when activated, and it applies only to autoref'd receivers. Matsakis (2017), *RFC 2025: Enable nested method calls*, https://rust-lang.github.io/rfcs/2025-nested-method-calls.html.
- **How places lower.** In MiniRust a place evaluates to a pointer with provenance, and projection is pointer arithmetic by layout. Jung et al. (ongoing), *MiniRust*, https://github.com/minirust/minirust. Only the syntax page was read.

### What we can reuse

- **Oxide's place grammar and prefix-overlap disjointness.** This is our direct ancestor (Gierczak and Ahmed are on both papers). Referents give us "location + path" pointers without a heap cell per field.
- **The CH2O/RefinedRust shape: cells at the leaves of a per-block tree.** Our own/imm/mut cells would become leaf annotations, and RefinedRust's `blocked'a` is exactly a per-leaf mut-loan marker with a lifetime.
- **RustBelt's two routes as the template for our same-lifetime projection.** For `mut`, use a LftL-bor-split analogue: a mut cell over a composite place decomposes into mut cells over its sub-places with the same lifetime set. For `imm`, define the product interpretation fieldwise.
- **PCG's `unpack`/`pack`** as the checker-side vocabulary for splitting and rejoining places.

### Where our setting differs or is open

- **Callback scoping may remove a whole mechanism.** RustHornBelt needs partial prophecy resolution because a Rust borrow's end is not syntactic. Under `withbor` the lender gets the value back when the callback returns, so projection may reduce to nesting a field-level `withbor` inside the parent's callback. That still has to be derived in BoLo; nobody has done it for a calculus of our kind.
- **Lifetime *sets* on imm cells have no direct counterpart.** RustBelt, RefinedRust and LLBC all use a single region or loan per borrow. What happens to lifetime sets when a cell is decomposed along a path is not in the literature. The question is whether the set sits only at leaves or is inherited down the tree.
- **Oxide's reborrow exclusion list is an open correspondence.** It is not yet known whether it matches anything in our reborrow rule ([TR] 6.55) or is purely syntactic.
- **Two-phase borrows are a surface-language decision.** Either encode them (end an imm borrow, then start a mut borrow on the same place) or avoid them through CBPV evaluation order.

---

## Q2 — `split_at_mut`, array segments, integer indices in types

### What the literature settles

- **The segment algebra itself.** ATS's `array_v(a, l, n)` is a linear view with two lemmas, `array_v_split {i ≤ n}` and `array_v_unsplit`. They form an isomorphism between one segment and two adjacent segments. The proofs are erased, so the split costs nothing at run time, and the constraint `i ≤ n` goes to a decidable arithmetic solver. Zhu, Xi (2005), *Safe Programming with Pointers through Stateful Views*, https://www.cs.bu.edu/~hwxi/atslangweb/MYDATA/SPPSV-padl05.pdf; Xi (n.d.), *ATS prelude: array_v_split / array_v_unsplit*, https://ats-lang.github.io/DOCUMENT/INT2PROGINATS/HTML/HTMLTOC/x3618.html. ATS has no lifetimes.
- **Index language design.** Types are indexed by *static* integer terms, not program terms, and a singleton type links a runtime value to its static index. Constraints are decided by a linear-arithmetic solver. Xi, Pfenning (1998), *Eliminating Array Bound Checking through Dependent Types*, https://dblp.org/db/conf/pldi/pldi98.html *(PDF not fetched)*.
- **The cost of solving.** In Array Separation Logic, satisfiability is NP-complete, entailment is decidable but expensive, and biabduction is NP. Brotherston, Gorogiannis, Kanovich (2017), *Biabduction (and Related Problems) in Array Separation Logic*, https://arxiv.org/abs/1607.01993. The lesson: make split points explicit and do not infer frames.
- **Intervals vs index sets.**
  - Interval-based ownership functions `{[m,n] ↦ u}` split pointwise and are inferred by CHC solving, but the single-interval restriction rules out strided splits. Tanaka, Sakayori, Kobayashi (2023), *Ownership Types for Verification of Programs with Pointer Arithmetic*, https://arxiv.org/abs/2312.06455.
  - An extension handles nested arrays (ownership indexed by outer indices). Fujiwara, Matsushita, Suenaga, Igarashi (2026), *Ownership Refinement Types for Pointer Arithmetic and Nested Arrays*, https://arxiv.org/abs/2604.22361 *(abstract only)*.
  - Iterated separating conjunction over arbitrary sets works, but needs quantifier reasoning in SMT. Müller, Schwerhoff, Summers (2016), *Automatic Verification of Iterated Separating Conjunctions using Symbolic Execution*, https://arxiv.org/abs/1603.00649.
  - CN's `each(i; 0 ≤ i < n){Owned(p+i*4)}` is the automatable middle ground over a real C memory model. Pulte et al. (2023), *CN: Verifying Systems C Code with Separation-Logic Refinement Types*, https://dl.acm.org/doi/10.1145/3571194 *(author list from memory)*.
- **Same-lifetime split, verified as a library.** RustHornBelt verifies `split_at_mut` and `iter_mut`. For `iter_mut`, a mut borrow becomes an iterated conjunction of per-element mut borrows at the same lifetime `α`, and the parent's prophecy is partially resolved as `↑x = [↑y₁..↑yₙ]`. Matsushita, Denis, Jourdan, Dreyer (2022), https://dl.acm.org/doi/10.1145/3519939.3523704. This is a proof about unsafe code, not a typing rule.
- **Safe split in a language with a scoped borrow.** Åkerblom et al. give array capabilities that split consecutively or with a stride, and merge. Children are re-indexed from 0. A lexically scoped `Borrow` restores the parent at scope exit "without forcing the programmer to manually merge all siblings". Åkerblom, Castegren, Wrigstad (2020), *Reference Capabilities for Safe Parallel Array Programming*, https://arxiv.org/abs/1905.13716. The searchers saw no mechanised proof and did not check the split details against the full text.
- **Safe split in a library with leak-freedom.** Pure Borrow offers `splitAt` on vector borrowers at the same lifetime. Matsushita, Ishii (2026), https://arxiv.org/abs/2604.15290. Part of its metatheory is conjectured.
- **Refinements on lengths.** Flux indexes vectors by length and infers refinements with a liquid fixpoint over SMT, but still calls Rust's unsafe `split_at_mut`. Lehmann, Geller, Vazou, Jhala (2023), *Flux: Liquid Types for Rust*, https://dl.acm.org/doi/10.1145/3591283.

### What we can reuse

- **The interface: ATS split/unsplit as a bijection on ghost cell structure, guarded by `i ≤ n`.** Carry element indices at source level and scale by `sizeof` only when lowering (Q5).
- **The index language: DML/ATS-style static index sorts.** Restrict constraints to a small fragment (difference constraints or Presburger) with a decision procedure. That keeps the checker decidable and the Lean side small.
- **The scoping reading: Åkerblom's "split inside the borrow, parent restored on exit".** This matches `withbor` structurally and suggests unsplit need not be a user-visible operation.

### Where our setting differs or is open

- **This is the most open question.** Every searcher reported that no published work makes a same-lifetime split of a lifetime-annotated mutable borrow a *primitive checked typing rule*. RustBelt and RustHornBelt treat it as verified unsafe code. ATS has no lifetimes. Åkerblom has no mechanised proof. Pure Borrow is a library whose correspondence result is conjectured. A derived rule in BoCa would be new; the candidate shape is two nested `withbor` on disjoint segment places inside the parent's callback.
- **Representation choice.** A segment cell `(base, n)` would be native to the cell map. The alternative is segments derived as iterated per-location cells, in the style of ATS's `ArraySome` (inductive) or CN (`each`). CN's form suits random access better.
- **Intervals vs sets.** Intervals keep everything decidable. Strided splits need index sets and quantified reasoning. Decide whether we need strided splits.
- **Child indexing.** Children can be re-indexed from 0 (Åkerblom: a view is a fresh array) or keep absolute paths into the parent (a place). The second fits Q1 better.

---

## Q3 — An abstract place algebra, generic over resource kinds

### What the literature settles

- **Generic soundness, per-kind axioms.** Views parameterises a program logic by a commutative semigroup of views plus a reification map to concrete state. Frame soundness is proved once, and each instance supplies its atomic axioms subject to one stability condition. Dinsdale-Young, Birkedal, Gardner, Parkinson, Yang (2013), *Views: Compositional Reasoning for Concurrent Programs*, https://www.doc.ic.ac.uk/~pg/publications/Dinsdale-Young2013Views.pdf.
- **The basic algebra and locality.** Separation algebras are cancellative partial commutative monoids, and local actions are the framable state transformers. Calcagno, O'Hearn, Yang (2007), *Local Action and Abstract Separation Logic*, http://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl.pdf. Cancellativity is assumed and fails for duplicable parts such as `imm` or `!T`.
- **Building algebras compositionally.** Products, function spaces and lifts, plus tree shares, which split permissions left and right without rationals. It is a Coq library (VST's MSL). Dockins, Hobor, Appel (2009), *A Fresh Look at Separation Algebras and Share Accounting*, https://vst.cs.princeton.edu/msl/fresh-sa.pdf.
- **Structure-preserving maps.** PCM morphisms and separating relations let one build sub-PCMs and abstractions. Farka, Nanevski, Banerjee, Delbianco, Fábregas (2021), *On Algebraic Abstractions for Concurrent Separation Logics*, https://arxiv.org/abs/2010.12686.
- **Whole plus fragments, with the relation as the per-kind parameter.** The Iris view camera takes a relation `view_rel a b` between an authoritative whole and its fragments. `Auth` is the special case where the relation is inclusion, and `gmap_view` instantiates it for finite maps. Iris project (library), *iris.algebra.view*, https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.view.html. No paper specific to the view camera was found.
- **An abstract part structure that differs from physical layout.** Fictional Separation Logic lets a module present its own separation algebra, related to the heap by an interpretation. Jensen, Birkedal (2012), *Fictional Separation Logic*, https://cs.au.dk/~birke/papers/sharing-conf.pdf.
- **Carve-out and collapse of sub-structures.** Structural addresses let a subtree be split off as its own cell and later glued back. The worked instances are the DOM and a POSIX file-system subset. Wright (2013), *Structural Separation Logic* (PhD thesis), https://vtss.doc.ic.ac.uk/publications/Wright2013Structural.pdf.
- **Fractions as the usual leaf algebra.** Fractional and counting permissions. Bornat, Calcagno, O'Hearn, Parkinson (2005), *Permission Accounting in Separation Logic*, http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/permissions_paper.pdf.
- **Typestate as the leaf algebra.** Resource types are indexed by an ordered partial monoid of state transitions, with borrowing. Saffrich, Nishida, Thiemann (2024), *Law and Order for Typestate with Borrowing*, OOPSLA 2024, https://arxiv.org/pdf/2408.14031.

### What we can reuse

- **Views' split, as a proof architecture.** A generic layer over an abstract view structure carries frame soundness and the FP skeleton. Each resource kind then discharges one obligation: its atomic commands, including our borrow axioms, satisfy the stability condition.
- **The Dockins constructors for building the place algebra.** A struct is a product, an array is a finite function space over indices, and a heap is a partial function space. They must be ported by hand to Lean, since Mathlib has no partial-algebra library for this.
- **A per-kind `view_rel`.** Instantiate it for memory, for array segments, and for a positional file (byte sequence plus offset-indexed fragments). Use the discrete specialisation, without step-indexing.
- **Farka et al.'s morphism laws** as the obligations a projection (field or segment) must meet.
- **Wright's carve-out/collapse** as the operational reading of "enter a borrow callback" and "leave it".

### Where our setting differs or is open

- **No generic place algebra exists.** No work packages *paths and projections* as the generic structure, generic over memory, files and other kinds. Views, `view_rel` and structural SL are each part of it.
- **Duplicable parts break cancellativity.** Our `imm` cells and `!T` are duplicable, so ASL results that assume cancellativity must be rechecked before they are used.
- **Lifetime sets have no slot in these frameworks.** None of them carries lifetime sets. They would have to live inside the leaf algebra, and it is open whether product and function-space constructions commute with lifetime-set annotation.
- **Is the typed world already a whole/fragment pair?** It may already be one (heap as the whole, typed cells as fragments). If so, stating it as a view relation gives Q3 genericity cheaply.

---

## Q4 — Allocation as an effect or handler; arenas and regions

### What the literature settles

- **Lexical regions and their limit.** `letregion ρ in e` with effect-inferred placement. It is strictly LIFO. Tofte, Talpin (1997), *Region-Based Memory Management*, http://ropas.snu.ac.kr/lib/dock/ToTa1997.pdf.
- **Regions in a C-like language.** Region-annotated pointer types, `rgn_malloc(r, …)` with the region as a value, stack frames treated as regions, and outlives subtyping. Soundness is proved on paper only, and the heap region relies on GC. Grossman, Morrisett, Jim, Hicks, Wang, Cheney (2002), *Region-Based Memory Management in Cyclone*, https://www.cs.umd.edu/projects/cyclone/papers/cyclone-regions.pdf.
- **Region liveness as a separate capability.** A static capability says a region is live, separately from the pointers into it. Freeing consumes the unique capability, which removes the LIFO requirement. Walker, Crary, Morrisett (2000), *Typed Memory Management via Static Capabilities*, https://www.cs.cornell.edu/talc/papers/capabilities.pdf.
- **Linear capabilities as the primitive.** With linear region capabilities, lexical regions become derivable and non-LIFO lifetimes become expressible. Fluet, Morrisett, Ahmed (2006), *Linear Regions Are All You Need*, https://link.springer.com/chapter/10.1007/11693024_2 *(summary from snippet)*.
- **Non-memory resources as instances.** Keys cover regions, files and locks, and adoption places a linear object under a region. DeLine, Fähndrich (2001), *Enforcing High-Level Protocols in Low-Level Software*, https://dl.acm.org/doi/10.1145/378795.378811; Fähndrich, DeLine (2002), *Adoption and Focus*, https://www.microsoft.com/en-us/research/wp-content/uploads/2002/05/pldi02.pdf.
- **Allocator strategy chosen per region.** Isolated regions each pick a strategy (arena, RC, tracing), and a thread has one "window of mutability" at a time. Arvidsson et al. (2023), *Reference Capabilities for Flexible Memory Management*, https://arxiv.org/abs/2309.02983.
- **Region splitting and sized allocation.** Sub-regions split off, sizes are bounded, and safety comes from effects rather than substructural types. Hughes, Vollmer, Batty (2025), *Spegion: Implicit and Non-Lexical Regions with Sized Allocations*, https://arxiv.org/abs/2506.02182.
- **Regions as second-class capabilities in handler/CPS languages.**
  - Schuster, Brachthäuser, Ostermann (2022), *Region-based Resource Management and Lexical Exception Handlers in Continuation-Passing Style*, https://se.informatik.uni-tuebingen.de/publications/schuster22region.pdf. This is Effekt's `region r { … }`; resuming a continuation restores region state.
  - Brachthäuser, Schuster, Ostermann (2020), *Effects as Capabilities*, https://ps.informatik.uni-tuebingen.de/publications/brachthaeuser20effects/.
  - Lowering to explicit regions with subregion evidence: Müller, Schuster, Starup, Ostermann, Brachthäuser (2023), *From Capabilities to Regions*, https://pl.cs.uni-tuebingen.de/publications/mueller23lift/.
- **Regions plus handlers, mechanised.** Non-local control breaks the stack discipline, and multi-shot handlers can exit a region twice. Yarrow Logic in Iris makes region exit a resource. Mathiasen, Timany, Birkedal (2026), *Yarrow: Reconciling Effect Handlers and Region-Based Memory Management*, https://arxiv.org/abs/2607.15876.
- **Encoding in a host type system.** Nested regions via rank-2 branding. Kiselyov, Shan (2008), *Lightweight Monadic Regions*, https://homes.luddy.indiana.edu/ccshan/capability/region-io.pdf.
- **The practical discipline in Rust.** `Bump::alloc(&self, T) -> &mut T` at the lifetime of the shared arena borrow. `reset(&mut self)` frees en masse and needs exclusivity. Drop is not run. Fitzgerald et al., *bumpalo*, https://docs.rs/bumpalo/latest/bumpalo/struct.Bump.html.
- **Dynamic ownership as an escape hatch.** Adoption and abandon with a dynamic check. Balabonski, Pottier, Protzenko (2016), *The Design and Formalization of Mezzo*, https://dl.acm.org/doi/10.1145/2837022.

### What we can reuse

- **Fluet–Morrisett–Ahmed as the architecture.** The arena is a linear owned capability, and the callback form is derived from it. Consuming the capability is freeing, which fits leak-freedom adequacy directly.
- **The Capability Calculus / bumpalo split** between a liveness capability (the own cell) and the references it hands out (borrows).
- **Cyclone's region-as-value parameter and outlives subtyping,** which should match lifetime-set inclusion.
- **Effekt's second-class capability plus capture sets.** Our lifetime sets on thunks and `!T` may already play the role of the capture set.

### Where our setting differs or is open

- **No formal account of allocation itself as an effect.** Nothing peer-reviewed treats malloc/free or the choice of arena as an algebraic effect with a proved safety result. Yarrow and Schuster et al. are the nearest.
- **Minting mut cells from an imm borrow needs a new axiom.** bumpalo's `&'arena mut T` comes from an *imm* borrow of the arena, at that borrow's lifetime. In BoCa terms, an imm borrow of an owned allocator cell mints fresh mut cells at the same lifetime set. That is a new axiom next to withbor, withload and withswap, and nobody has proved it sound for lifetime-set cells.
- **Leak-freedom against mass free.** bumpalo skips Drop, which is a leak under our adequacy theorem. Either arenas hold only trivially droppable (copyable, `!T`) contents, or arena-free must consume its linear contents, as Vault's adoption requires.
- **Multi-shot continuations.** Before allocation becomes a handler in the CBPV core, continuations captured across a `withbor`/arena scope must be one-shot. Yarrow names this hazard.

---

## Q5 — Abstract source memory to bytes and Wasm linear memory

### What the literature settles

- **Injections as the standard relation.** Memory is blocks of memvals, which include pointer fragments `Pointer(b,i,n)`. Permissions form a chain `Nonempty < Readable < Writable < Freeable`, tracked as both Cur and Max. `meminj : block → option (block × Z)` has no-overlap conditions, and each memory operation is proved to preserve injections. Leroy, Appel, Blazy, Stewart (2012), *The CompCert Memory Model, Version 2*, https://inria.hal.science/hal-00703441/PDF/RR-7987.pdf.
- **World-indexed memory relations.** CKLRs generalise injections into Kripke logical relations with an accessibility relation. `injp` adds protection: memory the other side does not own is unchanged across external calls. Koenig, Shao (2021), *CompCertO*, https://www.semanticscholar.org/paper/CompCertO:-compiling-certified-open-C-components-Koenig-Shao/6fb5d0610a25dc82cadf0332860bafe6d60302cd *(secondary)*. A single `injp` relation can serve as the uniform interface for the whole compiler. Zhang, Wang, Wu, Koenig, Shao (2024), *Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules*, https://dl.acm.org/doi/10.1145/3632914.
- **Finite memory.**
  - The abstract model is proved to abstract a concrete 32-bit model. Besson, Blazy, Wilke (2015), *A Concrete Memory Model for CompCert*, http://cs.yale.edu/homes/wilke-pierre/itp-15.pdf.
  - An infinite and a finite model are connected by refinement, with OOM as an allowed target behaviour. Beck, Yoon, Chen, Zakowski, Zdancewic (2024), *A Two-Phase Infinite/Finite Low-Level Memory Model*, PACMPL 8 ICFP, Art. 263, https://arxiv.org/abs/2404.16143.
- **A tree/path memory refined to bits.** CH2O memory refinements are proved invariant under all operations. Krebbers (2016), https://arxiv.org/abs/1509.03339.
- **Borrow-level to address-level simulation.** LLBC is proved a correct view over a CompCert-style heap by local commutation diagrams, usable forward or backward. It is mechanised in Rocq. Ho, Fromherz, Protzenko (2024), https://arxiv.org/abs/2404.02680.
- **Typed Wasm with capabilities, from Ahmed's group.** RichWasm has L3-style linear/unrestricted capabilities that split into read-only ones and are erased. Its memories map locations to high-level values. Type safety is proved in Coq. The lowering to Wasm is described as type-directed, and the searchers saw **no proof** of it. Lifetimes and fractional capabilities for immutable borrows are listed as future work. Fitzgibbons et al. (2024), *RichWasm*, https://arxiv.org/abs/2401.08287.
- **Separation logic on Wasm bytes.** Iris-Wasm has byte points-tos `n ↦[wm]_i b` and a robust-safety logical relation. Rao et al. (2023), *Iris-Wasm*, https://iris-project.org/pdfs/2023-pldi-iris-wasm.pdf.
- **Our target.** Talos is a Lean 4 Wasm interpreter with a WP calculus. `WasmHeap.lean` uses iris-lean `GenHeap` with `Location = (memId × UInt32)` and `Value = Option UInt8`. There are SmallStep adequacy files, including total lifting. The licence is AGPL-3.0. sgraf812 (fork of cajal-technologies), *Talos*, https://github.com/sgraf812/talos. Only one file header was read.
- **A verified backend into linear memory.** Bump allocation via `mem_ptr`, no free, and a theorem of the form "related, or out of memory". Meier, Pichon-Pharabod, Spitters (2025), *CertiCoq-Wasm*, https://dl.acm.org/doi/10.1145/3703595.3705879.
- **Blocks as segments.** MSWasm adds handle-guarded segments. Michael et al. (2023), *MSWasm*, https://dl.acm.org/doi/10.1145/3571208. Iris-MSWasm gives the handle invariants. Legoupil, Rousseau, Georges, Pichon-Pharabod, Birkedal (2024), https://iris-project.org/pdfs/2024-oopsla-iris-mswasm.pdf.
- **Layout without commitment.** RefinedRust parameterises struct layout by an arbitrary layout algorithm. Gäher et al. (2024).
- **Sub-buffers over a block model.** Low*'s `B.sub` is (base, idx, len), and only the base block can be freed. Protzenko et al. (2017), *Verified Low-Level Programming Embedded in F\**, https://arxiv.org/abs/1703.00053.
- **Provenance on the C path.** Zaliva et al. (2025), *A CHERI C Memory Model for Verified Temporal Safety*, https://popl25.sigplan.org/details/CPP-2025-papers/8/A-CHERI-C-Memory-Model-for-Verified-Temporal-Safety. This matters only if CHERI is a target.

### What we can reuse

- **A CKLR-shaped relation.** Use a world-indexed injection from BoCa locations (or places) to `(memId, UInt32)`. The accessibility relation says borrowed or frozen cells do not change during callbacks. Following Zhang et al., keep a *single* relation and do not build a tower of intermediate memory models.
- **Beck et al.'s two-phase pattern.** Keep FP and adequacy over an infinite store and put OOM in the refinement. Besson et al. give the same lesson: do not push concrete addresses into the source.
- **Source-level shape.** Take the layout parameterisation from RefinedRust, the tree-to-bytes refinement from CH2O, and Low*'s (block, offset, len) with free-only-on-base. The last matches own vs borrow.
- **Proof style.** LLBC's local-commutation simulations. Alternatively, an Iris-Wasm-style semantic interpretation of our world as invariants over Talos byte points-tos.
- **Permission erasure.** A candidate mapping is imm → Readable, mut → Writable, own → Freeable, with lifetimes erased or carried as ghost state.

### Where our setting differs or is open

- **No verified compiler from a borrow/lifetime calculus to Wasm or bytes was found.** RichWasm's lowering appears unverified, and RichWasm lacks borrows.
- **Nothing relates a place/tree memory to Wasm linear memory.** CH2O does it for C bits only.
- **Carrier bridge.** Talos sits on iris-lean's cmra, and BoCa uses its own PMap carrier, so a bridge is needed. The AGPL licence also needs checking.
- **Allocation failure.** Talos's handling of `memory.grow` failure is unknown. It decides whether OOM is a refinement escape or an effect visible in types (Q4).

---

## Q6 — Resources beyond memory: places vs streams

### What the literature settles

- **A split between name and access right.** In L3 a duplicable pointer is paired with a linear capability that records the current contents, and well-typed programs terminate. Ahmed, Fluet, Morrisett (2005), *L3: A Linear Language with Locations*, https://www.khoury.northeastern.edu/home/amal/papers/linloc.pdf. For a file, this gives a duplicable descriptor name plus a linear capability carrying typestate.
- **Streams are protocols, not part/whole structures.** Actris models channel endpoints as owned resources carrying dependent separation protocols, mechanised in Iris. Hinrichsen, Bengtson, Krebbers (2020), *Actris*, https://iris-project.org/pdfs/2020-popl-actris-final.pdf.
- **File systems are tree-structured places, but global names break disjointness.** Paths, `..` and symlinks overlap local updates; the fix is an effect frame rule. Ntzik, Gardner (2015), *Reasoning about the POSIX File System*, https://www.doc.ic.ac.uk/~pg/publications/Ntzik2015Reasoning.pdf. Wright (2013) also treats POSIX as a structural instance.
- **Typestate with borrowing.** Saffrich, Nishida, Thiemann (2024), https://arxiv.org/pdf/2408.14031.
- **One mechanism for memory and OS resources.** Vault keys (DeLine, Fähndrich 2001) and monadic regions over file handles (Kiselyov, Shan 2008).
- **Handles as capabilities on the target.** MSWasm and Iris-MSWasm.

### What we can reuse

- **A working classification.** *Places* have a part-of structure and positional access: memory, positional files (byte ranges), and file-system trees reached through owned handles. *Streams* are sockets, pipes and sequential files. They are linear handles indexed by a protocol or typestate, with no projection views, following L3 and Actris.
- **Saffrich et al.'s ordered partial monoid** as a candidate leaf algebra for typestate resources in the Q3 framework.
- **Keep path-based naming out of the place algebra.** Following Ntzik and Gardner, require resources to be reached through owned handles.

### Where our setting differs or is open

- **The places-vs-streams distinction is not named in the literature.** Actris and L3 supply building blocks only.
- **Borrowing a session endpoint is untreated.** No formal account covers lending an endpoint to a callback and getting it back at an advanced protocol state. Our `withswap`-style callbacks are the natural shape. The open question is whether the protocol state may change during the borrow; Rust-like rules suggest it may not.
- **Leak-freedom for protocols.** Whether leak-freedom extends to "protocol finished" obligations on stream handles is open.

---

## Q7 — Borrows as views, lenses, backward functions, prophecies

### What the literature settles

- **Backward functions.** In Aeneas, a function returning `&'a mut T` becomes `f_fwd : in → T` and `f_back : in → T → in'`. For field projection, `f_back` is the field setter, which is the put half of a lens. Ho, Protzenko (2022), https://dl.acm.org/doi/10.1145/3547647.
- **Prophecies.**
  - A mutable borrow is a pair (current value, final value), and the translation goes to CHCs. Matsushita, Tsukada, Kobayashi (2020), *RustHorn: CHC-based Verification for Rust Programs*, https://arxiv.org/pdf/2002.09002.
  - The semantic foundation, with parametric prophecies, partial resolution for subdivided borrows, and mechanisation in Iris: Matsushita, Denis, Jourdan, Dreyer (2022), https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf.
  - Surface syntax `*x` (current) and `^x` (final): Denis, Jourdan, Marché (2022), *Creusot*, https://link.springer.com/chapter/10.1007/978-3-031-17244-1_6.
- **Histories instead of prophecies.** Pure Borrow records updates at borrow paths, and the dead lifetime token reconstructs the final value (Matsushita, Ishii 2026). The mutative/denotational correspondence is conjectured.
- **Borrows as separation-logic views.** RustBelt's full borrows (Jung et al. 2018). RefinedRust combines place types with prophecy borrow names (Gäher et al. 2024).
- **Scoped regain of linear access.** Focus temporarily regains linear, strong-update access to one aliased object (Fähndrich, DeLine 2002). This is an early form of `withbor`.

### What we can reuse

- **Backward functions from `withbor`.** Our callback's return (together with the cell's final value) *is* the backward function, so an Aeneas-style forward/backward reading of withbor/withswap in the CBPV core looks derivable. Projection `&mut S → &mut S.f` gets the field setter as its put.
- **Prophecies only if we want first-order specs.** For a functional spec layer on the FP, RustHornBelt is the blueprint: carry a final-value ghost component in the world, without importing step-indexing.

### Where our setting differs or is open

- **No formal paper treats Rust-style borrows as lenses or optics.** None states lens laws, optic composition, or ties optics to lifetimes. Aeneas, RustHorn and Pure Borrow each implement one half informally.
- **Callback scoping may make prophecies redundant.** The lender regains the value at a syntactic point, so the final value is always available. Whether that holds for borrows that *escape* as results, within their lifetime, is the case to check.

---

## What to read first

1. **Oxide** (Weiss et al. 2019/2021), https://arxiv.org/abs/1903.00982. Our direct ancestor. It gives the place grammar, place-keyed loans, and the array exclusion we must lift.
2. **RustBelt** (Jung et al. 2018), https://people.mpi-sws.org/~dreyer/papers/rustbelt/paper.pdf. The semantic justification of same-lifetime splitting (LftL-bor-split, product sharing), which is exactly what BoLo needs to state.
3. **A Formal C Memory Model for Separation Logic** (Krebbers 2016), https://arxiv.org/abs/1509.03339. It covers places with leaf permissions and the refinement to bytes in one mechanised design, so it answers Q1 and Q5 together.
4. **Safe Programming with Pointers through Stateful Views** (Zhu, Xi 2005), https://www.cs.bu.edu/~hwxi/atslangweb/MYDATA/SPPSV-padl05.pdf, together with the ATS `array_v_split` page. The whole segment algebra and static-index design for Q2 in a few pages.
5. **Linear Regions Are All You Need** (Fluet, Morrisett, Ahmed 2006), https://link.springer.com/chapter/10.1007/11693024_2. Shows arenas as linear capabilities with the scoped form derived, which fits leak-freedom.
6. **CompCertO** (Koenig, Shao 2021) together with **Direct Refinements** (Zhang et al. 2024), https://dl.acm.org/doi/10.1145/3632914. The Kripke memory relation with protection (`injp`) is the right shape for the relation from BoCa to Talos.

---

## What the literature does not seem to answer

- **Same-lifetime `split_at_mut` as a checked typing rule.** Every precedent is either verified unsafe code (RustBelt, RustHornBelt), lifetime-free (ATS), unmechanised (Åkerblom), or conjectured in part (Pure Borrow). A derived rule in BoCa, nested `withbor` on disjoint segment places, would be new.
- **Field and segment decomposition of cells that carry lifetime *sets*.** Every precedent uses one region or loan per borrow. How a lifetime set on an imm cell distributes over a place tree has no precedent.
- **A place algebra generic over resource kinds, with paths as the generic structure.** Views, `view_rel` and structural SL each supply a piece, but none combines them. The same holds for a formal classification of places vs streams.
- **Borrowing a protocol-typed handle.** Lending a session or typestate endpoint to a callback and getting it back is untreated.
- **Arenas in a borrow calculus with leak-freedom.** There is no mechanised account of "an imm borrow of an allocator mints mut cells at the same lifetime", and none of how mass free interacts with linear contents under leak-freedom adequacy.
- **Allocation as an effect with a safety proof.** Only Yarrow (regions plus handlers) and a blog post exist.
- **A verified lowering from a borrow/lifetime calculus to Wasm, and from a place/tree memory to Wasm linear memory.** RichWasm stops short of borrows and of a proved lowering. CH2O targets C bits only.
- **Borrows as lenses with stated laws.** Aeneas and RustHorn have the ingredients but state no lens laws. Callback-scoped borrows may be the first setting where the lens reading is derivable directly from the fundamental property.
---

## Move

Move (Sui, Aptos) is the one production borrow checker with **second-class references**: a
reference can never be stored in a struct, vector, global storage or (on Aptos) a closure.
Sources were fetched and read in full unless marked.

### What Move settles

- **A reference is a rooted access path, because values are trees.** Records and vectors never
  hold references, and `&&T` is forbidden, so values and global storage stay tree-shaped and a
  reference is a location plus a field path, `ref⟨c, p⟩`. `BorrowField⟨f⟩` extends the path;
  `WriteRef` updates `M[c ↦ v[p := v′]]`. Blackshear, Mitchell, Nowacki, Qadeer (2022),
  *The Move Borrow Checker*, arXiv:2205.05181, https://arxiv.org/abs/2205.05181 (no peer-reviewed
  venue found).
- **The deployed checker is abstract interpretation over a path-labelled borrow graph.** An edge
  `x –p→ y` means "`x.p` is borrowed by `y`"; paths are fixed or extensible (`p∗`); vector elements
  get `∗` because the index is unknown. A borrow ends when the reference *value is destroyed*;
  eliminating a node splices in-edges with out-edges, so transitive borrows survive. Writes need no
  outgoing edges; reads and freezes need everything borrowing from the reference to be immutable;
  calls add `∗` edges from input to output references. The soundness proof is a pen-and-paper sketch
  over a subset with records but no vectors; globals are informal.
- **The mechanised successor (2026) labels edges with regular expressions.** A path environment
  maps pairs of references to regexes over field names, kept transitively closed. Extending a borrow
  by `p` uses concatenation for edges into the new reference and the **Brzozowski derivative**
  `δ(paths, p)` for edges out of it; the write check is `ℒ(paths(ρ,ρ′)) ⊆ {ε}`. Returned mutable
  references must be pairwise disjoint and outbound-clean, and must not borrow a local. Type
  soundness is mechanised in about 39K lines of Lean 4 with no sorry or axioms; generics, abilities,
  globals and references inside records are not covered. It accepts all 292,141 published Sui
  packages but is not yet in production. Nowacki, Blackshear, Mitchell, Qadeer, Sergey (2026),
  *Tracking Borrows with Regular Expressions*, PACMPL 10 OOPSLA2, Art. 389,
  https://doi.org/10.1145/3839521 (PDF https://verse-lab.org/papers/regex-borrows-oopsla26.pdf;
  artefact https://github.com/ilyasergey/lean-move).
- **Move's invariant is "no invalidation", not aliasing-XOR-mutation.** `&mut` has `copy` and
  `drop`; the checker restricts uses. The 2026 paper accepts a write through `&mut a` while `&a` is
  live, on the grounds that a type-preserving write leaves aliases of the same location valid, and
  notes that a concurrent setting would need exclusivity. Move Book, *References*,
  https://move-book.com/reference/primitive-types/references.
- **Abilities are per-type structural rules, checked field-wise.** `copy` gates copying and reading
  through a reference; `drop` gates discarding and overwriting (including writing through a
  reference); `store` says a value may live inside stored data; `key` says it may be a top-level
  storage entry. A type has an ability only if all its fields do; generics get abilities
  conditionally. References have `copy` and `drop` but not `store`. Move Book, *Abilities*,
  https://move-book.com/reference/abilities.
- **Resource conservation.** Before abilities, resources could only be moved; Theorem 5.10 states
  resources are created only by `Pack` and destroyed only by `Unpack`, proved on a concrete semantics
  independently of the verifier. Blackshear et al. (2020), *Resources: A Safe Language Abstraction
  for Money*, arXiv:2004.05106, https://arxiv.org/abs/2004.05106.
- **The Move Prover eliminates references** using the checker's guarantees: `&T` becomes a value and
  `&mut` a read-update-write cycle written back when the borrow ends. Dill et al. (2022), *Fast and
  Reliable Formal Verification of Smart Contracts with the Move Prover*, TACAS 2022,
  https://arxiv.org/abs/2110.08362.
- **The verifier has had exploitable bugs** (non-canonical enum field labels allowing aliased
  `&mut`; ability subtyping through `&mut` duplicating a resource), and Aptos now runs runtime
  checks with per-root access-path trees alongside it. Gao et al. (2026), *Defense-in-Depth Runtime
  Safety in Move*, arXiv:2606.18064, https://arxiv.org/abs/2606.18064.

### What we can reuse

- **The derivative as the projection rule on a place tree**, and regex emptiness (`⊆ {ε}`) as the
  disjointness check; `.∗` covers loss of precision in the same notation.
- **Two lemmas as templates:** path–heap coherence (a regex path from `ρ` to `ρ′` is realised in
  memory) for the typed world's static-to-heap clause; path transfer (same type, same navigable
  paths) for type-preserving writes. The flat enum encoding answers sum-typed cells: a variant-changing
  write must invalidate payload views.
- **The call/return contract from the signature alone:** returned mutable views disjoint and
  outbound-clean, nothing returned borrows a local, outputs related to inputs by `.∗`.
- **Abilities as surface syntax for modes:** `copy+drop` = unr, `drop` = the mode with weakening
  only, neither = lin; the field rule and conditional abilities on generics. Reading through a view
  needs `copy`, overwriting needs `drop`, swapping needs neither — the structural reading of
  `withload` and `withswap`.
- **Evidence second-class references scale:** over half of measured Move signatures contain a
  reference; the only reported friction was not being able to return references to globals.

### Where our setting differs or is open

- **Borrow end:** Move's is flow-sensitive (the reference value is destroyed); ours is syntactic
  (the callback returns). Move is first-order; we are higher-order CBPV.
- **Second-class views suffice for getters, field borrows and field-disjoint `&mut` returns.** They
  do not suffice for split at an **index** (Move conflates all indices), iterators over slices, or
  borrowed method records — all of which need views stored in data, which Move names as future work
  gated on a `store`-like ability.
- **Exclusivity:** do not import Move's weaker no-invalidation invariant; our `imm` cells promise
  immutability and any concurrency needs the stronger rule.
- **Relevant types:** Move allows `copy` without `drop`; our lin/cancel/unr qualifiers have no such
  point.
- **Assurance:** no mechanised combination of abilities, borrowing and leak-freedom exists; that is
  what our adequacy theorem would provide.
