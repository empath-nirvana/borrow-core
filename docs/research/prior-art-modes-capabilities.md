## Modes and capabilities in practical languages: what prior art did for modes, ownership, interior mutability and data-race freedom

I did not edit the repo. Two scratch files are in the scratchpad: text extracted from the DRFCaml paper at `/private/tmp/claude-501/-Users-johnthompson-repos-borrow-lang/8e4045bd-7129-41e8-acf7-6b8f9fa81f6a/scratchpad/pdfs/drf.txt`, and from Lorenzen et al. at `/private/tmp/claude-501/-Users-johnthompson-repos-borrow-lang/8e4045bd-7129-41e8-acf7-6b8f9fa81f6a/scratchpad/pdfs/ox.txt`. I read the full text of the DRFCaml paper, the Oxidizing OCaml paper, the Mode Crossing paper's front matter, and the Pony deny-capabilities paper. Everything else comes from official documentation or search abstracts. Any claim I did not confirm this session is marked **(unverified)**.

---

### 1. OxCaml / Jane Street modes

**Sources this session**
- Lorenzen, White, Dolan, Eisenberg, Lindley, *Oxidizing OCaml with Modal Memory Management*, PACMPL 8 ICFP, Art. 253 (2024).
- Georges, Peters, Elbeheiry, White, Dolan, Eisenberg, Casinghino, Pottier, Dreyer, *Data Race Freedom à la Mode* (DRFCaml), PACMPL 9 POPL, Art. 23 (2025), doi 10.1145/3704859. It won a Distinguished Paper award, according to Pottier's page.
- Peters, Jacobs, Kalinichenko, Stevenson, Smith, Dreyer, Eisenberg, *Mode Crossing*, PACMPL 10 ICFP, Art. 283 (2026).
- The oxcaml.org documentation: modes intro and reference, capsules, uniqueness/borrow, and parallelism tutorial part 1.

**Modes and what each guarantees**

The ICFP'24 paper has three axes:
- **Locality** (`global ≤ local`): a local value cannot escape its region. Regions are function and loop bodies; `exclave` ends a region early. This gives sound stack allocation.
- **Uniqueness** (`unique ≤ aliased`): a past axis, meaning "has not been duplicated". It licenses in-place reuse (`overwrite`).
- **Affinity** (`many ≤ once`): a future axis, meaning "used at most once".

These are tied together by one rule: a closure that captures a unique value must be `once`. Modes are deep. Modalities (`'a @@ m`) stop the depth, but only some modes have one (`@@ unique` does not exist).

DRFCaml (POPL'25) adds two axes:
- **Contention** (`uncontended ≤ shared ≤ contended`): an uncontended value's mutable fields may be read and written; a shared value's may only be read; a contended value's may not be accessed at all.
- **Portability** (`portable ≤ nonportable`): whether a value may be sent to another thread.

The implication between them, quoted from the paper: "a closure that captures an uncontended or shared value must be nonportable", or equivalently "the free variables of a portable closure must be contended".

The legacy mode, at which all existing OCaml type-checks, is `(global, many, aliased, nonportable, uncontended)`.

The current OxCaml documentation goes beyond the paper. It classifies each axis as "past" (monadic) or "future" (comonadic), and adds:
- `shareable` and `corruptible` points on portability, and `corrupted` on contention, making each a diamond;
- **visibility** (`read_write`, `read`, `write`, `immutable`; past);
- **statefulness** (`stateless`, `reading`, `writing`, `stateful`; future). Stateless closures capture at visibility `immutable`;
- **forkable** (future): "whether a function is permitted to access shared values in its parent stack";
- **yielding** (future): "whether a function is permitted to perform effects" handled in its parent stack. The default depends on locality: global values default to unyielding, local ones to yielding.

None of these later axes is covered by the POPL'25 formalisation. Its Figure 2 has exactly five axes.

**Borrowing and aliasing**
- OxCaml does not enforce aliasing-XOR-mutability. Aliased mutable state is the default, because the language is garbage-collected.
- Borrowing is lexical and read-only. `borrow_ x` (allowed in `let`, argument or `match` position) yields a value that is `aliased` and `local` for the region; afterwards `x` is unique again.
- There is no mutable borrow.
- Locality is coarse: one "current region", no lifetime variables. The DRFCaml paper names this limitation itself. NaStore cannot write a local value into a local reference, and supporting "local to some parent region", as Verona's Reggio does, is listed as future work.

**Interior mutability**
- Within one thread, every `ref` or mutable field is interior-mutable at no cost.
- Across threads, the mechanism is **capsules**, inspired by Rust's GhostCell: data `('a,'k) Data.t` is protected by a zero-size ghost key `'k Key.t`.
  - A **unique key** allows read and write, through `map`, `extract` and `destroy`.
  - An **aliased, local key** allows read-only access at mode `shared`, through `map_shared` and `extract_shared`.
  - All callbacks must be `portable`. That is what stops one capsule's data from being aliased into another capsule, or the callback from touching other mutable state. This is effectively re-entrancy and aliasing exclusion through the callback's mode.
- Keys are moved between threads by a reader–writer lock (`RwKeyLock.unique_protect` and `shared_protect`), which costs a run-time lock. Readers get only a `local` key, so they cannot keep it.
- Shipping OxCaml has a refined capsule API: `Password` (local), `Key` (unique), `Access` (uncontended, nonportable) and `Capsule.Mutex` (unrestricted; `with_lock` yields a password). On that docs page, Rwlock is listed as "Coming Soon".
- Atomics are always portable and accessible even when contended. Their contents must be `global, many, aliased, portable, contended`.

**Data-race freedom**
- Enforced statically by contention and portability. Fork requires a portable closure.
- One rule needs care. A portable closure may not capture even a `shared` value, because the parent may still hold an `uncontended` alias and write through it.
- The paper names the alternative it did not take: allowing `uncontended → shared` only for unique values. It was rejected because it would complicate submoding.
- The tutorial claims that programs without data races are sequentially consistent.

**Proof status**
- **Oxidizing OCaml:** pen-and-paper proofs of progress and preservation against a usage-aware store semantics (Appendix A.3), plus a relation to a graded fine-grain call-by-value calculus with a hand-built semiring. Nothing is mechanised. The paper reports deployment to "hundreds of developers".
- **DRFCaml:** "We formalize the complete system … All results in this paper have been mechanized in Rocq."
  - The method is a logical relation in Iris, indexed by `εmut` (read-write references), `εro` (read-only references) and `Δ` (locals), with ten "core conditions" (monotonicity requirements).
  - The results are Compatibility (5.1), the Fundamental Theorem (5.2), and "semantically typed ⇒ safe and data-race free" (5.3).
  - Theorem 3.1 ("No crash implies no race") runs over an instrumented semantics. Each non-atomic access takes two steps, with a per-location lock state, so a race gets stuck.
  - Capsules and RwLocks are implemented with `Obj.magic` and are proved semantically sound as separate theorems (6.1, 6.2), in the RustBelt style.
  - The scope is a core λ-calculus, not the OxCaml compiler.
- **Mode Crossing (ICFP'26):** modal kinds are interpreted as monotone functions on the mode lattice. Soundness of the core "SMoKi" is verified in Rocq/Iris, and the design is deployed in the compiler.

**Mapping onto our calculus**
- Our `imm` view is OxCaml's borrow (aliased + local) plus `shared` contention plus `read` visibility. Ours is stronger, because an `imm` view **freezes** the place.
- Our `mut` has no OxCaml counterpart.
- Our affine and unrestricted qualifiers correspond to `once` and `many`. OxCaml has no *linear* (must-use) mode.
- Uniqueness is a separate past axis in OxCaml. For us it is implied by ownership.
- Our effect rows cover yielding and statefulness, and more.
- Our lifetimes are finer than locality.

What we lack:
- a portability or contention axis;
- atomics;
- an explicit past/future (monadic/comonadic) split;
- mode crossing;
- a race-instrumented semantics;
- a semantic soundness route for library APIs whose implementation is unsafe.

---

### 2. Pony reference capabilities

**Source:** Clebsch, Drossopoulou, Blessing, McNeil, *Deny Capabilities for Safe, Fast Actors*, AGERE 2015 (full text read), plus the Pony tutorial.

**Modes and what each guarantees**

Each capability is a pair (what local aliases are denied, what global aliases are denied). "Local" means within the same actor; "global" means other actors.

| Capability | Meaning | Sendable |
|---|---|---|
| `iso` | denies all other read/write aliases, local and global | yes |
| `trn` | write-unique with local read-only aliases; can later become `val` | no (unverified) |
| `ref` | aliased mutable, actor-local | no |
| `val` | deeply immutable | yes |
| `box` | read-only view; denies global write aliases only | no |
| `tag` | identity only, no read or write; actors are typed `tag` | yes |

**Borrowing and aliasing**
- There are no lifetimes.
- Ownership is moved with destructive reads (`consume`, swap).
- Temporaries combine with **viewpoint adaptation**: the capability of a field depends on the capability of the path used to reach it.
- `recover` blocks lift a capability, for example `ref` to `iso`, when the block uses only sendable state.

**Interior mutability**
- Inside an actor, `ref` is freely aliased and mutable at zero cost. Actor bodies never run concurrently.
- There is no shared mutable state across actors and no locks.
- Communication is by message passing of `iso`, `val` or `tag` values.

**Data-race freedom**
- Every capability carried in a message must be sendable.
- The paper's Theorem 1 states "A well-formed heap ensures data race freedom"; Theorem 2 states well-formedness is preserved.
- It also claims atomic behaviours, meaning each actor's behaviour runs atomically.

**Proof status:** pen-and-paper, for a minimal actor language, with lemmas in the appendix. I found no mechanisation. Steed's later talk presents a revised formal model "with more permissive definitions" (unverified detail). Reports of soundness holes in `ponyc` are (unverified).

**Mapping onto our calculus**
- `box` corresponds to `imm`. `iso`, and a temporary `ref` under a lend, correspond to `mut`.
- `val` corresponds to frozen-forever data.
- `tag` corresponds to OxCaml's contended.
- `recover` corresponds to what Swift's region analysis and OxCaml's capsule `create` (with its portable constructor) do.
- Pony's lesson is that you can get DRF with *no* run-time cost and *no* lifetimes, provided concurrency is actors. It does not fit fork-join or shared state.

---

### 3. Scala 3 capture checking and capabilities as types

**Sources:**
- Boruch-Gruszecki, Odersky, Lee, Lhoták, Brachthäuser, *Capturing Types*, TOPLAS 45(4):21 (2023): the calculus CC<:□.
- Xu, Boruch-Gruszecki, Odersky, *Degrees of Separation*, OOPSLA 2024: System CSC.
- The Scala 3 documentation page on Mutability (separation checking).

**Modes and what each guarantees**
- Types carry capture sets (`T^{x,y}`), with a universal capability `cap`. The box type stops capture sets from propagating where a variable is not used directly.
- CSC adds root capabilities `ref` (mutation) and `rdr` (read). `rdr` is separate from itself, but not from `ref`.

**Borrowing and aliasing**
- Aliasing is allowed by default and tracked descriptively.
- A parallel composition type-checks only if the capture sets of its branches are "separate".
- The newer, experimental **separation checking** adds `Mutable` (or `Stateful`) classes:
  - `update` methods may use exclusive capabilities;
  - ordinary methods are read-only with respect to the receiver;
  - `x.rd` is the read-only capability and "counts as a shared capability";
  - an `update` method cannot override a normal one.
- `transparent` vars bypass the check, and that bypass is the programmer's responsibility.

**Interior mutability:** static. Read-only versus exclusive access is decided per method, with no run-time cost.

**Data-race freedom:** CSC handles structured fork-join only. DRFCaml's related-work section points this out. CSC proves type soundness and **confluence** of well-typed programs, and confluence stands in for DRF.

**Proof status**
- CC<:□: proved on paper in TOPLAS. The mechanisation is separate: Fourment & Xu's Coq work on the box calculus. Lee & Lhoták's System F<:C has a mechanised Coq proof.
- CSC: proved on paper. I found no mechanisation (unverified).
- Separation checking and `Mutable`: no proof is stated. The documentation says several restrictions are "currently not enforced".

**Mapping onto our calculus**
- `update` methods versus read methods on a `Mutable` class are the **closest existing design to "codata objects whose observations take exclusive access for one step"**. The `update` mark is the exclusive observation, and plain methods are `imm` observations.
- Capture sets are a close cousin of our effect rows: capabilities as effects, the Effekt / System C line.
- CSC's separate-branches rule is our pair-splitting fork-join.

---

### 4. Swift

**Sources:** SE-0176 (exclusivity) and SE-0414 (region-based isolation), read this session. SE-0430 (`sending`) and SE-0433 (`Mutex`) were confirmed accepted from forum listings only. Details of SE-0377 (`borrowing`/`consuming`), SE-0390 (noncopyable types) and SE-0446 (`~Escapable`) are (unverified).

**Modes and what each guarantees**
- `Sendable` is a type-level conformance: safe to cross an isolation domain.
- Actor isolation and global-actor isolation.
- `sending` parameters and results.
- Ownership modifiers `borrowing`, `consuming` and `inout`. Noncopyable types (`~Copyable`) and non-escapable types (`~Escapable`) (unverified detail).

**Borrowing and aliasing:** the Law of Exclusivity (SE-0176), "two accesses to the same variable are not allowed to overlap unless both accesses are reads".
- Static enforcement covers locals, `inout`, struct properties and non-escaping captures.
- Dynamic enforcement covers class properties, globals and locals captured by escaping closures.
- `@exclusivity(unchecked)` opts out.

**Interior mutability**
- Class instances are aliased and mutable, with run-time exclusivity checks.
- `Mutex` (SE-0433) is noncopyable and runtime-locked (unverified detail).
- Actors serialise access.

**Data-race freedom**
- Swift 6 enforces it through `Sendable`, actor isolation and region-based isolation.
- SE-0414 uses a forward dataflow analysis. Regions are disconnected, actor-isolated or task-isolated, and a disconnected region may be transferred.
- SE-0414 credits Milano, Turcotti & Myers, *A Flexible Type System for Fearless Concurrency* (PLDI 2022), whose authors' site claims a formal correctness proof (unverified: whether it is mechanised).
- SE-0176's dynamic checks do **not** detect concurrent races: "Dynamic enforcement is not required to detect concurrent conflicting accesses."

**Proof status:** the proposals contain no soundness proof. SE-0414 has only a convergence argument for its dataflow.

**Mapping onto our calculus**
- `inout` and `borrowing` correspond to `mut` and `imm`, but Swift's are second-class (parameter-only).
- `consuming` and `~Copyable` correspond to our linear/affine qualifiers.
- Swift is the cautionary case: exclusivity for heap data is dynamic because classes alias freely.

---

### 5. Rust

**Sources:** RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018), from the project page and the authors' blog. RustBelt Relaxed (Dang, Jourdan, Kaiser, Dreyer, POPL 2019). GhostCell (Yanovski, Dang, Jung, Dreyer, ICFP 2021), cited in DRFCaml.

**Modes and what each guarantees**
- `&T` (shared) and `&mut T` (unique), with lifetimes, enforce aliasing-XOR-mutability.
- `Send` (ownership may move to another thread) and `Sync` (`&T` may be shared, i.e. `T: Sync ⇔ &T: Send`). These are auto traits computed structurally.

**Interior mutability**
- `Cell`: zero cost; never hands out interior references; `!Sync`.
- `RefCell`: a run-time borrow flag; `!Sync`.
- `Mutex` and `RwLock`: run-time locks; `Sync`.
- Atomics.
- `GhostCell`: zero cost; a branded token separates the permission from the data.

**Data-race freedom:** aliasing-XOR-mutability plus `Send`/`Sync`. Scoped threads give fork-join with borrowed `&T` when `T: Sync`.

**Proof status**
- RustBelt mechanises λRust in Coq/Iris with a lifetime logic. Verified libraries, per the blog: `Rc`, `Arc`, `Cell`, `RefCell`, `Mutex`, `RwLock`, `thread::spawn`, `mem::swap`, `take_mut`.
- It found a real bug in `MutexGuard`. Unwinding is omitted.
- RustBelt Relaxed moves the model to relaxed memory and found a data race in `Arc`, which was fixed upstream.
- The real compiler is not verified. Exactly how `Send`/`Sync` are encoded semantically is (unverified).

**Mapping onto our calculus:** this is the closest match for `imm`/`mut`, lifetimes and freezing. The direct models for codata interior mutability are `Cell` (copy-in/copy-out, no interior references, so no re-entrancy hazard) and GhostCell. We lack `Send`/`Sync` or an equivalent.

---

### 6. The rest

**Verona**
- *Reggio*: Arvidsson et al., *Reference Capabilities for Flexible Memory Management*, PACMPL 7 OOPSLA2 (2023).
- A forest of isolated regions with reference capabilities.
- `enter` on a unique bridge object activates a region lexically. Entering another region suspends the current one (accessible but immutable). There is a single "window of mutability".
- Concurrency is Behaviour-Oriented Concurrency. Cowns ("concurrent owners") wrap an `iso` region. Behaviours run when all their cowns are available, and are claimed deadlock-free, data-race-free and atomic (Cheeseman et al.; the OOPSLA 2023 venue is unverified).
- Proof status: unverified.
- Mapping: a lend block per region; the cown corresponds to OxCaml's mutex-guarded capsule.

**Vale**
- Generational references: each allocation carries a generation number, checked at run time on dereference.
- Opt-in "region borrowing" freezes a region (all data in a thread, inside a mutex, or inside an `iso`) so the checks can be skipped. Vale's own blog calls region borrowing a prototype.
- No formal proof.
- Interior mutability is paid for in generation checks. This is the opposite trade-off to our static `imm` freeze.

**Hylo**
- Mutable value semantics (Racordon, Shabalin, Zheng, Abrahams, Saeta, *Implementation Strategies for MVS*, JOT): "references … only created implicitly, at function boundaries", and never stored.
- So there is no shared mutable state and no interior mutability in the safe language. Copy-on-write is used for containers.
- `inout`, `let`, `sink` and `set` correspond to `mut`, `imm` and linear transfer. Subscripts and projections that yield are the closest analogue of codata observations (unverified details).
- I found no proof (unverified).

**Austral**
- Linear and Free type universes.
- `borrow X as X' in R do … end` gives `&[T,R]`, and `borrow!` gives `&![T,R]`. "X cannot be used in B"; "Borrow expressions cannot escape the statement where they appear."
- **This is the nearest syntactic match to our lexical lend blocks with named regions.**
- Capabilities are linear values (ocap security).
- No concurrency, no interior mutability, no formal proof.

**Mezzo** (Balabonski, Pottier, Protzenko, TOPLAS 2016)
- Permissions, with an affine/duplicable split.
- Locks and adoption/abandon: dynamic ownership tests with a hidden field and a run-time check.
- Proved that well-typed programs do not go wrong *and* are data-race free, **machine-checked in Coq**: a core affine λ-calculus extended with references, locks and adoption/abandon.
- Interior mutability through adoption costs run-time checks. Pottier carried this line into DRFCaml.

**Cyclone**
- Regions, unique pointers, reference-counted pointers.
- *Type-Safe Multithreading in Cyclone* (Grossman, TLDI 2003): shared data must be guarded by a named lock, using effects and existentials; thread-local data may not escape its thread.
- The follow-up is Gerakios, Papaspyrou, Sagonas, 2010.
- Proof status: (unverified).
- This is the closest precedent for **lock names as effects**.

---

### 7. Proof status at a glance

| System | What is proved | Mechanised? |
|---|---|---|
| DRFCaml (5 axes, references, atomics, fork, borrow, capsules, RwLock) | Fundamental Theorem; well-typed programs are data-race free; APIs sound | **Yes**: Rocq/Iris, on a core calculus |
| OxCaml mode crossing (SMoKi) | soundness of modal kinds | **Yes**: Rocq/Iris |
| Oxidizing OCaml | progress and preservation | No: paper proof |
| OxCaml's later axes (visibility, statefulness, forkable, yielding, shareable/corrupted) | — | none found |
| RustBelt | λRust plus `Cell`/`RefCell`/`Mutex`/`Arc`… | **Yes**: Coq/Iris |
| Mezzo | soundness and DRF | **Yes**: Coq |
| Pony | well-formed heap ⇒ DRF, preservation | No: paper proof |
| CC<:□ / CSC | soundness / confluence | Paper proofs; parts mechanised separately |
| Swift | — | Implementation only; the PLDI'22 basis has a formal proof (unverified) |
| Vale, Austral, Hylo, Verona | — | none found (Verona unverified) |

---

### 8. Synthesis

**Which mode set is closest to what we need**

No single system matches. The best fit is **Rust's borrow structure plus OxCaml's thread axes**.

- Our `imm` (freezing) and `mut` (exclusive) already give aliasing-XOR-mutability for owned and borrowed data. As in Rust and CSC, fork-join with a context split is DRF with no extra modes.
- Interior mutability is the one thing that reopens races. Rust needs `Sync` exactly because of `Cell` and `RefCell`. OxCaml needs contention exactly because OCaml refs are aliased and mutable.
- For single-thread interior mutability, the closest designs are:
  - **Scala's `Mutable` + `update` methods**, where an exclusive observation is a method;
  - **OxCaml's capsule `map` with a portable callback**, where the mode of the callback rules out touching other state. That is our planned "re-entrancy excluded by effect rows";
  - **Rust `Cell` / GhostCell**, for zero cost.

**The minimal mode set that gives data-race freedom in prior art**
- With aliasing-XOR-mutability and structured fork-join: nothing beyond the split itself (Rust scoped threads, CSC).
- With unstructured threads, or interior-mutable shared state: a **dual pair**, one past and one future:
  - Rust's `Sync`/`Send`;
  - DRFCaml's contention/portability. Two contention points suffice if there is no read-sharing; `shared` exists for reader–writer locks.
  - Pony's sendable subset {`iso`, `val`, `tag`} plus actor-locality is the same idea for actors.
- Unique tokens (uniqueness + locality: OxCaml keys, GhostCell, LaCasa) then let shared mutable state be mediated with no run-time cost. A lock is needed only to hand the token across threads dynamically.

**What OxCaml worked out that we should adopt**
1. **The past/future duality, with implications attached to closure capture.** Capturing `unique` makes a closure `once`; capturing `uncontended` makes it `nonportable`. Our linear/affine qualifiers are the future side. We should name the past side (uniqueness from ownership; "not shared with another thread").
2. **Mode crossing through structurally computed modal kinds** (with-bounds, least-fixpoint recursive kinds), rather than traits. OxCaml chose this explicitly ("OxCaml does not support traits"). It fits our working default of no traits and structural derive. Deeply immutable data crosses contention and portability.
3. **Separating the permission from the data** (capsule/key/password). Zero-cost interior mutability, with a lock only for cross-thread transfer.
4. **Using the callback's mode to exclude re-entrancy.** Their portable-callback rule is the precedent for our effect-row exclusion.
5. **Their proof architecture.**
   - An Iris-style semantic logical relation with monotonicity "core conditions".
   - Unsafe-implemented APIs proved semantically as extra compatibility lemmas.
   - A race-detecting operational semantics (non-atomic access in two steps, with a lock state) so that "safe ⇒ race-free".
   This lines up with our Lean fundamental-property and adequacy approach.
6. **The `forkable` and `yielding` axes.** These are the only prior art I found that tracks *effects handled in the parent stack* together with thread-forking. That is directly the effects × threads interface we need.

**Where we should deliberately differ from OxCaml**
1. **We have no GC, so we need aliasing-XOR-mutability anyway.** Contention can largely be *derived* from `imm`/`mut`. The extra axis is needed only for interior-mutable codata and for shared or atomic cells.
2. **Our freezing `imm` fixes the gap DRFCaml documents.** DRFCaml must forbid a portable closure from capturing even `shared` data, because the parent may still write through an `uncontended` alias. The alternative it named — weaken to `shared` only from unique — is what a freezing lend gives us. So a thread may capture an `imm` view (as with Rust's `&T` under `T: Sync`).
3. **Our lifetimes are finer than locality.** DRFCaml cannot store a local value into a local reference, and lists "local to some parent region" as future work.
4. **We have a linear (must-use) qualifier; OxCaml has only `once`.**
5. **We have a mutable borrow (`mut`); OxCaml has only read-only borrows.**
6. **Decide deliberately whether our modes are deep, as OxCaml's are (with modalities to stop them), or shallow.**

---

### Sources
- [DRFCaml paper PDF](https://iris-project.org/pdfs/2025-popl-drfcaml.pdf)
- [DRFCaml POPL'25 page](https://popl25.sigplan.org/details/POPL-2025-popl-research-papers/23/Data-Race-Freedom-la-Mode)
- [Oxidizing OCaml ICFP'24 page](https://icfp24.sigplan.org/details/icfp-2024-papers/19/Oxidizing-OCaml-with-Modal-Memory-Management)
- [Oxidizing OCaml preprint](https://antonlorenzen.de/oxidizing-ocaml-modal-memory-management.pdf)
- [Mode Crossing (ICFP'26)](https://iris-project.org/pdfs/2026-icfp-modecrossing.pdf)
- [OxCaml modes intro](https://oxcaml.org/documentation/modes/intro/)
- [OxCaml modes reference](https://oxcaml.org/documentation/modes/reference/)
- [OxCaml capsules](https://oxcaml.org/documentation/parallelism/capsules/)
- [OxCaml borrowing](https://oxcaml.org/documentation/uniqueness/borrow/)
- [OxCaml parallelism tutorial, part 1](https://oxcaml.org/documentation/tutorials/intro-to-parallelism-part-1/)
- [janestreet/parallel](https://github.com/janestreet/parallel)
- [Pony deny capabilities (with proof)](https://www.ponylang.io/media/papers/fast-cheap-with-proof.pdf)
- [Pony tutorial: reference capabilities](https://tutorial.ponylang.io/reference-capabilities/reference-capabilities.html)
- [Capturing Types](https://pl.cs.uni-tuebingen.de/publications/boruch2023capturing/)
- [Box-calculus mechanisation](https://infosciences.epfl.ch/record/302949/files/a-mechanized-theory-of-the-box-calculus.pdf)
- [Degrees of Separation](https://infoscience.epfl.ch/record/310307/files/paper.pdf)
- [Scala 3 capture checking: mutability](https://scala-lang.org/api/docs/experimental/capture-checking/mutability.html)
- [Swift SE-0414](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0414-region-based-isolation.md)
- [Swift SE-0176](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0176-enforce-exclusive-access-to-memory.md)
- [Milano et al., PLDI'22](https://www.cs.cornell.edu/andru/papers/gallifrey-types)
- [RustBelt POPL'18](https://plv.mpi-sws.org/rustbelt/popl18/)
- [RustBelt Relaxed](https://people.mpi-sws.org/~dreyer/papers/rbrlx/paper.pdf)
- [Reggio / Verona](https://arxiv.org/pdf/2309.02983)
- [Vale regions blog](https://vale.dev/blog/zero-cost-borrowing-regions-part-1-immutable-borrowing)
- [Mutable value semantics paper](https://daveabrahams.com/wp-content/uploads/2022/02/implementation_strategies_for_mutable_value_semantics-preprint.pdf)
- [Austral specification](https://austral-lang.org/spec/spec.html)
- [Mezzo TOPLAS 2016](https://usr.lmf.cnrs.fr/~blsk/Publications/Balabonski-Pottier-Protzenko-Mezzo-TOPLAS2016.pdf)
- [Grossman, Cyclone multithreading](https://web.eecs.umich.edu/~bchandra/courses/papers/Grossman_Racefree.pdf)