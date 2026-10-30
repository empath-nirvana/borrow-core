# Prior art: borrows across suspension points

A literature and prior-art survey for #270. It changes no code and proposes no kernel rule; §6 is
a recommendation for the design decision #269 asks for.

**The question.** How have others sliced borrows and references across suspension points
(effect handlers, coroutines, generators, async)? Is there a known, principled cut, and is it
proved sound, ideally without step-indexing?

**Our working hypothesis** (#269, #270). The cases that keep descending in
`experiments/GhostEnd` (#249–#268) are all **self-referential suspended state**: a lend of data
owned *inside* the suspended computation that is still open at a suspension. Lends of data owned
*outside* are finite and easy.

**How claims are marked.**

- **[read]**: the passage was fetched and read for this survey; quotations are from it.
- **[Crossref]**: title, authors, venue and year checked against Crossref's record of the DOI.
- **[repo]**: cited as an existing borrow-core document cites it, not re-read here. The document
  is named.
- **[recalled]**: from memory, not checked for this survey. Treat as a lead, not a fact.
- **[inspection]**: my reading of our own documents or code, with no proof.

**Limits.** The web-search budget of the session ran out early. After that, sources were reached
only by fetching known URLs: the Rust reference and RFC pages, Swift Evolution, OxCaml's
documentation, arXiv, and Crossref. Every claim about a source I could not reach is marked
[recalled]. The two places where that matters most are named in §7.

---

## 0. Answers

1. **There is a standard slice, and it is ours already.** A borrow of data owned by the
   suspended computation may not be live at a suspension that reifies the continuation. Borrows
   of data owned outside may be live there, provided they outlive the suspended computation.
   - **Rust** states it as error E0626 for every movable coroutine and every `gen` block: "a
     borrow in a movable coroutine persists across a yield point" [read]. Only an immovable
     coroutine (`static`, or any `async` block), used through `Pin`, may do it.
   - **Our kernel** already has the same rule (T1, #172). SPEC §19, *Which
     operations cross a borrow's scope*, lets an answering operation (a call) or an abortive one
     (unwinding) cross a borrow's scope, but not "any other control operation: its `κ` is
     reified, and a stored `κ` would hold a lend across a suspension".
   - **The same shape recurs** elsewhere: "nothing of kind K may be live at a suspension of kind
     S".
     - Tang et al. and Affect: no linear or affine value (in their sense) in a multi-shot
       continuation.
     - Swift: no actor-isolated `inout` across an `await`.
     - OxCaml's *yielding* axis.
     - Koka's tail-resumptive `fun` operations, which, like our answering operations, are not
       suspensions at all.
2. **Self-referential suspended state made safe without `Pin`/`unsafe` exists, in two families.
   Neither carries over to a semantic, lifetime-stratified model like ours.**
   - **The frame is never a movable value.** Swift async frames, OCaml 5 fibers, Gears on
     virtual threads or delimited continuations, and Effekt all allocate the suspended stack
     once and hand out a pointer to it. `Pin` exists only because a Rust future is an inline
     value that `memcpy` may move. Our semantics has abstract locations and never moves a
     continuation's cells, so **`Pin`'s problem, address stability, does not arise for us at
     all** [inspection]. What does arise is the lifetime side, which these languages handle
     dynamically, or by GC, or by not having borrows.
   - **Internal names are bound inside the continuation.** System C (Effekt) and Scala's capture
     checking prove soundness syntactically. There, a capability bound inside the handled
     computation is a bound variable of the continuation, and α-renaming gives it a fresh name
     whenever needed. rustc does the analogue in its type system: the regions of a coroutine's
     internal borrows are not part of the coroutine's type [recalled]. **GhostEnd's re-lend at a
     fresh lifetime at each resumption is the semantic counterpart of that α-renaming**
     [inspection]. I found no semantic model, step-indexed or not, that does this for
     lifetimes.
3. **What is proved, and how.**
   - **Syntactic, so step-index-free.** Second-class values (Coq). System C (Coq; progress and
     preservation). Capturing types [recalled]. The capability calculus of Crary, Walker and
     Morrisett, which is CPS throughout, so every suspension is a call. Tofte–Talpin's region
     soundness (a co-inductive consistency relation).
   - **Semantic, in Iris, so step-indexed.** RustBelt (lifetimes as tokens), Hazel, Affect (step
     indexing named in its introduction [read]), blaze (POPL 2026) and Yarrow (regions with one-
     and multi-shot handlers, 2026).
   - **Not proved anywhere I found.** Rust's E0626 slice and `Pin` have no mechanised proof.
     Jung's 2018 formal treatment of pinning is, by its author's own description, a simplified
     sketch [read].
   - **Semantic and step-index-free:** only BoLo and our own T14.6. T14.6 is a candidate paper
     proof (`docs/effects-tr/15-mut-cell.md` §14.4) that every body with no lend spanning a
     suspension produces rebased continuations.
4. **Recommendation (§6).**
   - **The slice.** Adopt the standard slice formally: keep SPEC §19's rule as the kernel's
     definition. It is the right cut, and the literature has no better one that is proved.
   - **Two refinements, both outside the kernel.** Make it liveness-based by elaboration: split
     a lend at a suspension where its view is dead. And make "owned buffer in, owned buffer out"
     the idiom for operations that suspend.
   - **What it costs.** A generator iterating a collection it owns through a borrowing iterator;
     an async task holding a borrow of its own buffer across an `await`; a generator that lends
     its own data out. These are exactly the programs Rust rejects without `Pin`, and they have
     the same workarounds.
   - **What it removes.** It lets us **stop the ghost-end line for internal lends**. #268's three
     unknowns, and the open-lend stack #269 worries about, are all inside that line.
   - **What stays.** Rebasing (T14.5/T14.6) stays: it is what makes *external* borrows and stored
     continuations sound.
   - **What is banked.** GhostEnd's machine-checked results remain as a possible second tier: one
     `Mut` lend spanning resuming yields, which Rust cannot offer without `Pin`. Adopt that tier
     only if a forcing program asks for it.

---

## 1. Rust

### 1.1 Coroutines, `async`, and E0626: the slice, stated by the compiler

- **E0626** [read, https://doc.rust-lang.org/error_codes/E0626.html]: "This error occurs because
  a borrow in a movable coroutine persists across a yield point." "Coroutines may be either
  unmarked, or marked with `static`. If it is unmarked, then the coroutine is considered
  'movable'. At present, it is not permitted to have a yield in a movable coroutine that occurs
  while a borrow is still in scope."
- The erroneous example is precisely an internal lend spanning a stop:

      let mut b = #[coroutine] || {
          let a = &String::new(); // <-- This borrow...
          yield ();               // ...is still in scope here, when the yield occurs.
          println!("{}", a);
      };

  The fix offered is `static ||`, after which the coroutine can only be resumed through
  `Pin<&mut _>` (`std::pin::pin!(b)`).
- **The slice therefore has two tiers.** The lower tier is movable: no internal borrow is live
  at a yield, and borrows of captured outside data, at the coroutine's lifetime parameters, are
  allowed. The upper tier is immovable: internal borrows are allowed, and the value must be
  pinned. `async fn`/`async {}` futures are always on the upper tier; that is why every future is
  polled through `Pin<&mut Self>` [recalled].
- **The check is liveness-based**, run by MIR borrowck: it rejects a borrow *live* at the yield,
  not one lexically enclosing it [recalled; consistent with the wording "still in use" in the
  `gen` diagnostic below].
- **How rustc types the internal borrows.** The types held across a yield (the coroutine's
  "witness") do not carry the regions of internal borrows as free parameters of the coroutine's
  type. Historically they were erased or bound by a binder [recalled; the rustc-dev-guide page on
  coroutine closures, read, names the witness but does not describe its regions]. This is the
  type-level form of "internal lifetimes are abstracted by the continuation's obligation"
  (`docs/effects-tr/15-mut-cell.md` §14.0 item 2).
- **Soundness.** No proof. RustBelt's λRust has no coroutines [recalled].

### 1.2 `Pin`: what it actually fixes

- **The standard library's account** [read, https://doc.rust-lang.org/std/pin/index.html]: a
  self-referential type "contains a pointer to another piece of its own data … if that value is
  _moved_, the pointer will still point to the old address". `Pin` guarantees the pinned value
  "must remain, valid, at that same address in memory, until its `drop` handler is called". The
  **drop guarantee** is part of soundness, not hygiene.
- **The aliasing side** [read, RFC 3467 `unsafe_pinned`, start date 2022-11-05,
  https://rust-lang.github.io/rfcs/3467-unsafe-pinned.html]. A self-borrow across a yield makes
  the `&mut Self` passed to `resume`/`poll` alias the internal pointer. That contradicts the
  uniqueness of `&mut` assumed by `noalias` and by Stacked Borrows. Today rustc suppresses
  `noalias` on `!Unpin` types, a hack the RFC calls a misuse of `Unpin`. `UnsafePinned` makes the
  exception explicit.
- **Formal treatment.** Jung, *A Formal Look at Pinning*, blog post, 2018-04-05 [read,
  https://www.ralfj.de/blog/2018/04/05/a-formal-look-at-pinning.html]. It adds a third typestate
  `T.pin` beside RustBelt's `T.own` and `T.shr`. In the author's words, it is a simplified version
  of the paper's formalism that "glosses over many of the details". It is **not mechanised**. A
  follow-up, *Sharing for a Pinned Type*, exists [recalled]. I found no later mechanised proof of
  `Pin`, and I have not verified that none exists.
- **Proposals to replace it.** Without Boats, *Pinned places*, 2024-07-23 [read,
  https://without.boats/blog/pinned-places/], makes pinnedness a property of places, like
  `mut`. It argues against a `Move` trait on backward-compatibility grounds. Neither proposal
  changes the slice; they change its ergonomics.
- **For us** [inspection]:
  - `Pin` solves **address stability under moves** and the **aliasing of `&mut Self`**.
    Neither exists in BoLo's semantics. Locations are abstract. A continuation is a value whose
    cells stay where they are when the value is moved. And our `Mut` view is a cell in `Res`,
    not a `noalias` promise about a machine address.
  - What our hypothesis shares with `Pin` is the **case**: the internal lend live at the stop.
    The **reason** it is hard differs. For Rust it is the representation; for us it is the
    placement of an internal lifetime in the stratification at a resumption the body did not
    choose (`docs/effects-tr/15-mut-cell.md` O14.1, `refoldKripke_false`).

### 1.3 `gen` blocks and lending iterators

- **RFC 3513, `gen` blocks** [read, https://rust-lang.github.io/rfcs/3513-gen-blocks.html, start
  date 2023-10-10; authors not shown on the page fetched, Oli Scherer and Travis Cross
  recalled]. Because `Iterator::next` takes `&mut self`, not `Pin<&mut Self>`, "we cannot create
  self-referential `gen` blocks". The RFC's own example is the canonical cost:

      gen {
          let xs = vec![1, 2, 3, 4];
          for x in xs.iter() {
              yield x * 2;
          }
          //~^ ERROR borrow may still be in use when `gen` block yields
      }

  The RFC calls this "a severe and surprising limitation", and lists three ways out as
  unresolved: a separate pinned-iteration trait; changing `next`'s receiver; or implementing
  `Iterator` for `Pin<&mut G>`. **The slice is the shipped default; lifting it is open design.**
- **Lending iterators** (GATs, stable in Rust 1.65, 2022-11-03) [read,
  https://blog.rust-lang.org/2022/10/28/gats-stabilization/]:

      trait LendingIterator { type Item<'a> where Self: 'a;
                              fn next<'a>(&'a mut self) -> Self::Item<'a>; }

  This is the **dual** direction: the suspended state lends its own data *out* to the consumer,
  and the lend must end before the next resumption, because `next` holds `&'a mut self`. That
  is a borrow across a suspension in the other direction. It is safe because the resumer's
  `&mut` keeps the state still for the lend's duration: a scoped, second-class resumption.
- **Keyword generics / the effects initiative.** It makes `async`, `const` and `try` generic
  parameters of functions and traits [recalled]. I know of no rule in it about borrows across
  suspension; it inherits E0626.
- **Polonius.** A location-sensitive reformulation of borrowck. It accepts more programs within
  a body, but has no rule specific to yields [recalled]. It would refine *which* borrows are live
  at a yield, not the slice.

### 1.4 Cancellation and borrowed buffers: a cost data point

Without Boats, *Notes on io-uring*, 2020-05-06 [read, https://without.boats/blog/io-uring/]:
"if you pass a slice to be used as a buffer for IO and then cancel the future waiting on that
IO, you cannot use that slice again until the kernel has actually completed". Since "any object
can be leaked in Rust", "there's no sound way to take a borrowed slice, pass it to the kernel, and
wait for the kernel to finish its IO". The answer is **owned buffers**: the operation takes the
buffer and gives it back.

For us [inspection]: our continuations are linear with a cancel branch, and cancellation is
finalisation (`docs/effects-tr/` D1.8, §8), so the leak half of that argument does not apply. The
ownership half does: a suspending I/O operation whose payload is a *lend* is exactly a lend spanning
the stop. Under the slice, the payload is the owned buffer, and the answer returns it.

---

## 2. OCaml with modes (OxCaml)

- **Lorenzen, White, Dolan, Eisenberg & Lindley, *Oxidizing OCaml with Modal Memory
  Management*, PACMPL 8 (ICFP), 2024**, DOI 10.1145/3674642 [Crossref]. It covers the locality,
  uniqueness and linearity (`once`) modes. I could not fetch the paper (403), so what it says
  about effect handlers is not verified here.
- **The *yielding* axis** [read, https://oxcaml.org/documentation/modes/intro/]: "Yielding is a
  future axis that tracks whether a function is permitted to perform effects that will be
  handled in its parent stack." "_global_ values are defaulted to _unyielding_, while _local_
  values are defaulted to _yielding_." Function types "mode cross" it. A sibling axis,
  *forkable*, "tracks whether a function is permitted to access shared values in its parent
  stack" (global defaults to forkable, local to unforkable).
- **Reading** [inspection, not stated on the page]:
  - OxCaml slices **by mode on the function that might suspend**, not by a rule about which
    borrows are open.
  - Locality bounds a value to its region, and the stack-allocation reference says only global
    exceptions may be raised [read, https://oxcaml.org/documentation/stack-allocation/reference/].
    So the slice for *abortive* control is "the payload is global", which is our "payload outlives
    the scope" for `raise`.
  - The pages read give no rationale for the yielding defaults and cite no soundness proof.
    Treat the mapping to our cut as a lead.
- **Tang, White, Dolan, Hillerström, Lindley & Lorenzen, *Modal Effect Types***, arXiv
  2407.11816 (revised 2025-03-18) [read, abstract]. Effect *modes* instead of effect
  polymorphism; the venue is not stated on arXiv (OOPSLA 2025 [repo:
  `docs/prior-art-effects-coeffects.md`]). The abstract names no proof technique.
- **Data race freedom à la mode** (POPL 2025): `portable`/`contended`, i.e. what may cross to
  another domain [repo: `docs/prior-art-borrow-splitting.md`]. This is the thread analogue of
  "what may cross a suspension".

---

## 3. Capabilities and second-class values

### 3.1 Scala 3 capture checking, `CanThrow`, Gears

- **Boruch-Gruszecki, Odersky, Lee, Lhoták & Brachthäuser, *Capturing Types*, TOPLAS 45(4),
  2023**, DOI 10.1145/3618003 [Crossref]. Soundness is progress and preservation for CC<:□
  [recalled; the Scala reference page cites the theory but states no proof, read].
- **The slice is scope, not suspension.** The reference [read,
  https://docs.scala-lang.org/scala3/reference/experimental/cc.html] says a `try`'s result type
  "is not allowed to capture the universal capability", which stops a `CanThrow` escaping the
  `try`. In the `usingLogFile` example, a closure capturing the file "persists longer than its
  allowed lifetime" and is rejected. **Boxing** stops capture propagation through type
  parameters, and an unbox re-charges the capture set.
- **Gears** [read, https://blog.nkagami.me/gears-book/]: direct-style `async` with a
  `using Async` capability. Suspension is by JVM virtual threads (JRE 21) or by Scala Native's
  delimited continuations. The stack is never a movable value, so self-reference is a non-issue,
  and capture checking bounds which capabilities a `Future` may hold (structured concurrency).
  The reference page I read does not mention Gears or continuations.
- **For us** [inspection]: capture checking is about *escape from a scope*. That is our `[]I`
  and outlives side condition, which already covers *external* lends across a suspension (T14.6's
  `Δ ⊢ Γ ⊐ @c`). It adds no rule for internal ones, because nothing in Scala's model depends on
  where an internal capability's lifetime sits.

### 3.2 Effekt and System C

- **Brachthäuser, Schuster, Lee & Boruch-Gruszecki, *Effects, Capabilities, and Boxes*, OOPSLA
  2022**, DOI 10.1145/3527320. **Brachthäuser, Schuster & Ostermann, *Effects as
  Capabilities*, OOPSLA 2020**, DOI 10.1145/3428194. **Müller, Schuster, Starup, Ostermann &
  Brachthäuser, *From Capabilities to Regions*, OOPSLA 2023**, DOI 10.1145/3622831. All three
  [repo: `docs/second-class-and-system-c.md`, which read them and their Coq development].
- **Soundness.** Effect safety is progress and preservation in Coq [repo]. It is syntactic, so
  step-index-free.
- **How internal capabilities cross a suspension.** A capability bound *inside* a handled
  computation, such as a local `var` or a `region`, is a bound variable of the captured
  continuation. It is not in the continuation's capture set; only capabilities free in the
  handler's context are. So there is no restriction to state, and preservation handles freshness
  by substitution [inspection of the calculus as `docs/second-class-and-system-c.md` describes it].
- **Regions and control.** Schuster, Brachthäuser & Ostermann, *Region-based Resource
  Management and Lexical Exception Handlers in Continuation-Passing Style*, ESOP 2022 [repo:
  `docs/prior-art-memory-model.md`]: resuming a continuation restores the region's state, i.e.
  region state is part of what is captured. Muhcu, Schuster, Steuwer & Brachthäuser, *Multiple
  Resumptions and Local Mutable State, Directly*, ICFP 2025, DOI 10.1145/3747529 [repo] is its
  direct-style successor.

### 3.3 Second-class values

- **Osvald, Essertel, Wu, González Alayón & Rompf, *Gentrification Gone too Far? Affordable
  2nd-Class Values for Fun and (Co-)Effect*, OOPSLA 2016**, DOI 10.1145/2983990.2984009
  [Crossref]. Second-class values may not escape their scope. The paper proves type soundness and
  "never leaks stack references" (Thm 3.2) for a big-step semantics, in Coq [repo:
  `docs/prior-art-effects-coeffects.md` §3.5].
- **Osvald & Rompf, *Rust-like Borrowing with 2nd-Class Values*, SCALA 2017** [repo]. Each borrow
  is written as a callback whose parameter is second-class: `bindMut(x) { y => … }`. This is our
  `withbor` exactly.
- **Consequence** [inspection]: if a reified continuation is first-class (storable), a
  second-class lend cannot be live in it. Second-class lends *are* the standard slice, stated as
  a scoping discipline. Our callback-scoped `withbor` with SPEC §19's rule is that discipline.

### 3.4 Koka's tail-resumptive operations

- Xie & Leijen, *Generalized Evidence Passing for Effect Handlers*, PACMPL 5 (ICFP), 2021, DOI
  10.1145/3473576 [Crossref].
- Koka distinguishes `fun` operations (tail-resumptive, run in place, no continuation captured)
  from `ctl` operations (which capture one) [recalled].
- That is our split between *answering* and *other control* operations in SPEC §19. An
  answering operation is a call, so a lend may span it; this is the in-place half of T9.2.

---

## 4. Value semantics: Hylo, Swift, Vale, Austral

- **Hylo** has no first-class references [repo: `docs/prior-art-optics.md`; Racordon, Shabalin,
  Zheng, Abrahams & Saeta, *Implementation Strategies for Mutable Value Semantics*, JOT 21(2),
  2022]. Subscripts `yield` a projection and resume when the access ends: a *yield-once*,
  lexically scoped coroutine. The suspended frame lends its own data out across the suspension,
  and this is safe because the resumption is second-class, as with lending iterators (§1.3).
- **Swift.**
  - **Yielding accessors.** SE-0474 [repo: `docs/prior-art-optics.md`]: "Exclusive access …
    extends for the duration of the accessor's execution, including its suspension"; the
    yield-once rule makes the resumption linear.
  - **Async/await.** SE-0296 (McCall & Gregor) [read] defines suspension points as explicit and
    notes that "suspensions interrupt atomicity". The proposal says nothing about the layout of
    async frames. That they are allocated by the task allocator and never moved is [recalled].
  - **Actor state.** SE-0306 [read]: "Actor-isolated stored properties can be passed into
    synchronous functions via `inout` parameters, but it is ill-formed to pass them to
    asynchronous functions via `inout` parameters". The reason given: another task on the same
    actor may access the state during the suspension. **This is the external-versus-shared cut at
    a suspension**, stated for actor state.
  - **Non-escapable types.** SE-0446 (Trick & Kientzle; implemented in Swift 6.2) [read]:
    "Escaping closures cannot capture nonescapable values". The closures given to `Task.init`,
    `Task.detached` and `TaskGroup.addTask` are escaping. So a scoped value may live across an
    `await` in its own frame, but cannot be handed to a task that outlives the scope. This is
    escape, as with capture checking.
- **Vale** (generational references, regions) and **Austral** (linear types; borrows scoped by a
  region block) [recalled]. I found nothing formal about either at suspension points. Austral has
  no coroutines that I know of.

---

## 5. Regions with control, and program logics

### 5.1 Region systems

- **Tofte & Talpin, *Region-Based Memory Management*, Information and Computation 132, 1997**,
  DOI 10.1006/inco.1996.2613 [Crossref]. `letregion` is lexical and strictly LIFO, with no
  control operators. Soundness is by a co-inductive consistency relation [recalled]: not step
  indexed.
- **Crary, Walker & Morrisett, *Typed Memory Management in a Calculus of Capabilities*, POPL
  1999**, DOI 10.1145/292540.292564 [Crossref]. A CPS target language in which every
  continuation takes the region **capabilities** it needs as an argument, and freeing a region
  consumes its capability [recalled].
  - **This is the token view applied to suspension.** In CPS every suspension is a call, so a
    capability live across one is just an argument of the continuation, and no region order is
    built into the semantics.
  - Soundness is syntactic [recalled].
- **Cyclone.** Grossman, Morrisett, Jim, Hicks, Wang & Cheney, PLDI 2002 [repo:
  `docs/prior-art-memory-model.md`]: region-annotated pointers, outlives subtyping, and stack
  frames as regions. Grossman's TLDI 2003 *Type-Safe Multithreading in Cyclone* restricts what a
  spawned thread may reference to sharable regions that outlive it [recalled, unverified].
- **Monadic regions.** Fluet & Morrisett, JFP 2006; Fluet, Morrisett & Ahmed, *Linear Regions
  Are All You Need*, ESOP 2006 [repo]; Kiselyov & Shan, *Lightweight Monadic Regions*, 2008
  [repo]. Regions are nested by rank-2 encapsulation, or carried as linear capabilities. None of
  them treats delimited control together with regions [recalled].
- **Yarrow.** Mathiasen, Timany & Birkedal, *Yarrow: Reconciling Effect Handlers and Region-Based
  Memory Management*, arXiv 2607.15876, 2026 [read, abstract]: "non-local control flow of
  algebraic effects break[s] the stack discipline". The logic supports regions with one-shot and
  multi-shot handlers. It is in Iris on Rocq, hence step-indexed [inference from Iris; the
  abstract does not say]. Repo note: region exit is a resource.

### 5.2 Separation logics and logical relations for handlers

| work | what it handles | technique |
|---|---|---|
| de Vilhena & Pottier, *A Separation Logic for Effect Handlers* (Hazel), PACMPL 5 (POPL), 2021, DOI 10.1145/3434314 [Crossref] | protocols; one-shot continuations owning heap | Iris, step-indexed [recalled] |
| de Vilhena, van Collem, Wright & Krebbers, *A Relational Separation Logic for Effect Handlers* (**blaze**), PACMPL 10 (POPL), 2026, pp. 981–1009, DOI 10.1145/3776676 [Crossref; abstract read] | relational reasoning with effects, state and concurrency; the effects of the two programs need not correspond; case studies on async libraries | Iris, step-indexed |
| van Rooij & Krebbers, *Affect: An Affine Type and Effect System*, PACMPL 9 (POPL), 2025, art. 5, DOI 10.1145/3704841 [read] | one- vs multi-shot continuations, references storing continuations; "restricts affine values from being captured in multi-shot continuations" | semantic typing in Iris; "an abstract form of step-indexing" (§1) [read] |
| Tang, Hillerström, Lindley & Morris, *Soundly Handling Linearity*, PACMPL 8 (POPL), 2024, DOI 10.1145/3632896 [repo, Crossref there; abstract read on arXiv 2307.09383] | control-flow linearity: no linear value discarded or duplicated by a multi-shot continuation; fixes a soundness bug in Links | type soundness of two calculi; syntactic [recalled] |
| Jung, Jourdan, Krebbers & Dreyer, *RustBelt*, PACMPL 2 (POPL), 2018 [repo] | lifetimes as **tokens** `[κ]_q`; full borrows; lifetime inclusion | Iris, step-indexed |

**None of them has borrows in the lifetime sense across a suspension.** Hazel, blaze and Affect
have heap ownership in the continuation. Tang et al. and Affect slice on *multiplicity*: no
linear or affine value (their classes) may be live in a multi-shot continuation. Their slice has the
same shape as ours, indexed by the operation's annotation; the index is multiplicity, not lifetime.

### 5.3 Lifetimes as tokens versus lifetimes as strata

- **RustBelt's lifetime logic** [repo: `docs/prior-art-borrow-splitting.md` §2.2; Jung's thesis
  ch. 11]:
  - a lifetime is a ghost name, allocated fresh;
  - holding a fraction of its token `[κ]_q` keeps it alive;
  - `κ ⊑ κ'` is a persistent fact, not a position in an order;
  - ending a lifetime consumes the whole token and yields `[†κ]`.
- **Does a token view make suspension trivial?** For the *lifetime* side, essentially yes
  [inspection]. A continuation is a closure whose precondition owns the tokens of every lifetime
  it has open, and the borrows' resources. Suspending frames them into the closure; resuming
  frames them back. No lifetime has to be re-placed in an order, because there is no global
  order, only the inclusions the code has proved. Nothing like `refoldKripke` or re-lending at a
  fresh lifetime arises. This is why the Iris handler logics (§5.2) can store arbitrary owned
  state in a continuation without comment.
- **The cost.**
  1. **Step-indexing.** The lifetime logic is built from Iris invariants, and every Iris model of
     a higher-order language with handlers is step-indexed. Total correctness then needs
     Transfinite Iris or later credits [recalled], not BoLo's plain least fixed points.
  2. **Address stability is untouched.** Even in RustBelt, a self-referential type needs the
     `pin` typestate (§1.2). Tokens solve the lifetime side, not the representation side. We have
     no representation side (§1.2), so this cost is Rust's, not ours.
  3. **BoLo's stratification is what makes its relation well-founded without steps.**
     `Res_α`/`Mut_α` are built by well-founded recursion on `Life = ℕᵒᵈ`, and the strict stratum
     is exactly what keeps Landin's knot out (`docs/effects-tr/15-mut-cell.md` L14.9,
     `no_nonstrict_stratum`).
     - Trading strata for tokens gives up that construction. That is the T15 boundary
       (`no_negative_domain`) #269 names.
     - So for us the token view would not make suspension trivial. It would make suspension the
       easy part and well-foundedness the hard part.

---

## 6. Recommendation

### 6.1 The slice to adopt

**Adopt the standard slice: no lend opened inside a suspendable computation is live at a
suspension that reifies the continuation.** Lends of data from outside (lifetimes ⊒ the
continuation's `'c`) may be live at any suspension. An internal lend may span an answering
(in-place) operation or an abortive one, but not a resuming control operation.

- **It is already the kernel's rule.** SPEC §19, *Which operations cross a borrow's scope*, with
  `Row.Unwind`. It is T1 as #172 states it.
- **Its soundness is T14.6's argument.** That is a candidate paper proof, step-index-free, and
  it composes with T14.5 for stored continuations. Mechanising T14.6 and adopting D14.7's `[gen]`
  is what remains on this route (`docs/effects-tr/15-mut-cell.md` §14.4, §14.8).
- **It matches Rust's movable-coroutine rule (E0626)** and the `gen` block default (RFC 3513).
  It is also the scoping discipline of second-class lends (§3.3), and Koka's in-place/capturing
  split (§3.4).
- **Nothing in the literature is both less restrictive and proved.** Rust lifts it with `Pin`,
  with no proof. Iris logics never meet it, because tokens have no order, and they pay with
  step-indexing. Syntactic calculi never meet it, because they have no lifetimes to place.

### 6.2 How to state it in our type system

**Recommended: keep it as the existing side condition on `withbor`'s callback row.** The row may
contain answering and abortive operations only. Do not add a mode, capture sets, or a second-class
judgement for it.

- **A mode** (as OxCaml's *yielding*) would duplicate the row: our rows already say which
  operations a computation may perform, and SPEC §19 classifies each by qualifier.
- **Capture sets** solve escape, which `[]I` and outlives already solve for external lends.
- **`withbor`'s callback is already the second-class form** (Osvald–Rompf 2017).

**Two refinements, both outside the kernel** (sugar into existing core terms, per "sugar never
special-cases the kernel"):

1. **Liveness, by elaboration.** Rust's check is about borrows *live* at the yield [recalled]. A
   surface borrow whose view is dead at a `yield` can be elaborated into two kernel lends:
   `withbor ℓ (λm. A); yield; withbor ℓ (λm'. B)`. The second is fresh, so no kernel lend spans
   the stop. This recovers the index-loop idiom without a rule. It is exactly what GhostEnd does
   *semantically* at each resumption (re-lend at a fresh lifetime). Done syntactically, at points
   where nothing derived from `m` is live, it needs no proof beyond the existing typing.
2. **Owned payloads for suspending I/O.** A suspending operation's payload is owned, and its
   answer returns ownership: `read : Buf ↠ (Buf ⊗ Len)`. This is tokio-uring's discipline
   [recalled], and Boats argues it is the only sound one for completion-based I/O (§1.4).

### 6.3 What it costs in expressible programs

Each item is a program Rust also rejects without `Pin`, and each workaround is Rust's.

| rejected | example | workaround |
|---|---|---|
| a generator iterating a collection it owns through a borrowing iterator | RFC 3513's `for x in xs.iter() { yield x * 2 }` | index loop, lend re-opened per element (§6.2.1); or a consuming iterator (`into_iter`): the iterator owns `xs`; or the caller owns `xs` and the generator borrows it from outside |
| an async task holding a borrow of its own buffer across a suspension | `withbor buf (λm. perform read m)` with a resuming `read` | owned buffer in, owned buffer out (§6.2.2); or `read` as an answering operation of a runner |
| a generator that lends its own data out (lending iterator, `yield &self.x`) | yielding a payload that contains an internal lend | internal iteration: a callback run under the lend (a `for_each` / Hylo subscript shape), which is a call, not a suspension |
| self-referential state | a parser that owns its input and holds a borrow into it across `yield` | own plus index (offsets instead of borrows) |

**Not lost:**

- external borrows across any suspension (T14.6);
- stored continuations holding external borrows (T14.5);
- answering operations, for example a `log` capability, inside any borrow (SPEC §19, acceptance
  (2));
- abortive `raise` inside any borrow;
- generator objects, task queues and handler state for bodies with no spanning lend
  (`docs/effects-tr/15-mut-cell.md` §14.7).

### 6.4 Does it let us drop the ghost-end and rebasing machinery?

- **Ghost-end for internal lends: yes.** Everything in `experiments/GhostEnd` exists to lift the
  slice: freeze, re-lend, `Open`, `RBody*`, the lend table, `vRL`/`cRL`. That includes the three
  unknowns of #268 (`'x` in a payload, `Imm` lends spanning a stop, nested lends spanning a stop)
  and the stack of open lends that #269 asks about. Under the slice, none is on the critical
  path to the kernel lift. In #269's terms, this is verdict **(b)**: a principled cut that makes
  the remaining structure finite. It is the cut the literature uses.
- **Rebasing: no; keep it.** Rebasing (L14.1, L14.2, T14.4–T14.6) is what makes a continuation
  holding *external* borrows, and a `Mut` cell holding a continuation, sound. Every system
  surveyed allows that, and it is what generators and handler state need. It is not ghost-end
  machinery.
- **Bank GhostEnd as a second tier; do not pursue it now.** It has already machine-checked a
  single `Mut` lend spanning resuming yields for typed borrowers, including loops, branches,
  tuples, closures and callees (`withbor_of_rbodyC`, `loop_spans_yields`,
  `closure_spans_yield`, `callee_spans_yields`).
  - That tier is **self-referential suspended state without `Pin`**, which Rust cannot express
    safely. Because our semantics has no addresses to stabilise, it would be a real expressivity
    gain.
  - It is also the one place where the open problems (#268) still live.
  - Reopen it only when a forcing program needs it: plausibly the async-buffer row of §6.3, if
    owned buffers prove too costly in the corpus.

---

## 7. What this survey did not settle

- **The two most load-bearing unverified items.**
  - The OxCaml paper's own treatment of effects and locality: the paper was not readable (403),
    and the documentation gives the *yielding* defaults without a rationale.
  - Whether a mechanised proof of Rust's `Pin` or of coroutine borrowck now exists (Jung's 2018
    post is a sketch; I found nothing later, and the search budget ran out before I could look
    further).
- **Polonius, keyword generics, Vale, Austral, Cyclone's threads, Tang et al.'s proof
  technique**, and rustc's representation of witness regions are all [recalled].
- **No semantic, step-index-free model of a lifetime-indexed borrow live across a resuming
  suspension was found.** That is consistent with GhostEnd being new. It is not a claim of
  priority: the search was cut short.

## Sources

Fetched and read for this survey:

- Rust error index, E0626. https://doc.rust-lang.org/error_codes/E0626.html
- Rust standard library, `std::pin`. https://doc.rust-lang.org/std/pin/index.html
- RFC 3513, *gen blocks*. https://rust-lang.github.io/rfcs/3513-gen-blocks.html
- RFC 3467, *unsafe_pinned*. https://rust-lang.github.io/rfcs/3467-unsafe-pinned.html
- Rust blog, *Generic associated types to be stable in Rust 1.65*, 2022-10-28.
  https://blog.rust-lang.org/2022/10/28/gats-stabilization/
- R. Jung, *A Formal Look at Pinning*, 2018-04-05.
  https://www.ralfj.de/blog/2018/04/05/a-formal-look-at-pinning.html
- Without Boats, *Pinned places*, 2024-07-23. https://without.boats/blog/pinned-places/
- Without Boats, *Notes on io-uring*, 2020-05-06. https://without.boats/blog/io-uring/
- OxCaml documentation, *Modes: intro*; *Stack allocation: reference*.
  https://oxcaml.org/documentation/modes/intro/ ,
  https://oxcaml.org/documentation/stack-allocation/reference/
- Scala 3 reference, *Capture Checking*.
  https://docs.scala-lang.org/scala3/reference/experimental/cc.html
- *Concurrency with Gears* (book). https://blog.nkagami.me/gears-book/
- Swift Evolution SE-0296 (async/await), SE-0306 (actors), SE-0446 (nonescapable types).
  https://github.com/swiftlang/swift-evolution/tree/main/proposals
- van Rooij & Krebbers, *Affect*, POPL 2025. https://iris-project.org/pdfs/2025-popl-affect.pdf
- arXiv abstracts: 2607.15876 (Yarrow), 2407.11816 (Modal Effect Types), 2307.09383 (Soundly
  Handling Linearity).
- Crossref records: 10.1145/3674642, 10.1145/3776676, 10.1145/3704841, 10.1145/3618003,
  10.1145/2983990.2984009, 10.1145/292540.292564, 10.1006/inco.1996.2613, 10.1145/3434314,
  10.1145/3473576.

Cited through other borrow-core documents: `docs/second-class-and-system-c.md`,
`docs/prior-art-effects-coeffects.md`, `docs/prior-art-memory-model.md`,
`docs/prior-art-optics.md`, `docs/prior-art-borrow-splitting.md`, `docs/effects-tr/12-sources.md`.

Our own context: `experiments/GhostEnd/README.md`; `docs/effects-tr/README.md`, §§14–15; SPEC
§19; issues #172, #249–#269.
