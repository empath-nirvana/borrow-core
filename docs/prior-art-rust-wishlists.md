# Prior art: what Rust's designers wish they had done

This note is for the language designer. It collects what well-known Rust designers and developers
have written they wish Rust had done differently, and what some of them are building instead. It
then maps each recurring wish onto borrow-core's design.

Its structure:

- §1: the sources, one entry each;
- §2: the themes across sources, ranked;
- §3: Steve Klabnik's Rue;
- §4: the mapping to borrow-core;
- §5: the lessons.

**Reading depth.** Each source is marked with one of three labels:

- **full**: the whole text was read;
- **part**: a digest of the whole page was read, and every sentence quoted here was checked
  against the page's raw text;
- **digest**: only a digest was read, and nothing from it is quoted.

Quotes are verbatim. Dates are the dates printed on the page. Sources were fetched in September
2026.

**What "count" means in §2.** It is the number of sources in §1 that raise the theme. It measures
this reading, not community consensus.

---

## 1. Sources

### 1.1 withoutboats (Saoirse; blog at without.boats)

withoutboats was on the Rust language team and drove the `async`/`await` and `Pin` designs from
2017 to 2019 ("Why async Rust?").

**The generators essay.** The essay the brief asks about is **"Generators"**, 26 March 2023,
<https://without.boats/blog/generators/>. It is read in **full**. It closes a series that began
with "The registers of Rust" (below). Two earlier posts set the scope: "Generators I: Toward a
minimum viable product" (11 February 2019) and "Generators II: The Question Mark Problem"
(18 February 2019). There was also a 2020 library, `propane`. Its argument, in order:

1. **What it asks for.** The feature to ship is "an imperative syntax for writing functions that
   compile to iterators". Stackless coroutines, "resumable functions" that also receive values
   when resumed, are a separate and lower-priority feature that should get a different syntax.
   The compiler transform already exists: "the core compiler transform to take a generator and
   produce a state machine already exists, because it's exactly how async functions are
   implemented."
2. **Declaration.** A keyword before `fn` or a block, "exactly the way that async works" (`gen`),
   shipped with the 2024 edition rather than behind a raw keyword `k#gen`.
3. **`yield from`.** Punt it. Its desugaring is a `for` loop that yields each item, and unlike
   `?` or `.await`, generators do not need their forwarding operator. This is an instance of his
   recurring point: "treating control-flow effects as a pattern, rather than an abstraction, is
   useful."
4. **Return type.** Show only the inner (yielded) type, as `async fn` does. The outer type would
   be "extremely verbose", would need "a new lifetime sugar that everyone would need to learn or
   … no lifetime elisions", and would carry little information. `Send` bounds belong at the use
   site.
5. **`return` and `?`.** `return` in a generator takes `()`. `?` becomes "a two step operation in
   the error case: first it yields the error, then it returns".
6. **Self-references: "really the big open problem".** "Iterator::next does not take a pinned
   reference to the iterator state, and therefore the iterator state cannot contain
   self-references", whereas `Future::poll` does. There are three options:
   - non-async generators cannot hold self-references, and they implement `Iterator`;
   - generators return some other type, which must be pinned before it is used as an
     `Iterator`;
   - deprecate `Iterator`.

   The third is "not realistic". He favours the first, because "Iterator has been unable to
   support self-references its entire existence, and this rarely appears as a problem", and
   iterators are short-lived, while async iterators live long and own complex state.
7. **The regret.** "If I could go back in time, I would just have `Iterator` take a pinned
   reference to itself. This isn't the only trait I wish could be changed like this - the problem
   with `Drop` not being pinned is even worse in my view."
8. **Conclusion.** Ship generators in the 2024 edition, as "the only approach that's compatible
   with Rust in its current phase of development". He notes the reception: enthusiastic from
   users, "more tepid, even defensive" from contributors.

"Iterator, Generator" (6 May 2023, **part**) costs out the third option: a new pinned `Generator`
trait. It finds diamond coherence problems, unsafe bridge code, and a social cost ("Every
existing documentation about iterators … would be out of date"). "Generators with UnpinCell"
(25 October 2024, **digest**) later proposes a pinned `Generator` trait bridged to `Iterator`
through an `UnpinCell` wrapper.

**Other withoutboats posts.**

- **"The registers of Rust"** (8 March 2023, **part**). A *register* is one of several ways to
  do the same task. For each control-flow effect there are four: the core register (the reified
  type, such as `impl Future`), consuming, combinatoric, and control-flow ("compiler-expanded
  syntactic sugar"). Asynchrony has all four. Iteration and fallibility lack the control-flow
  register: "We do have obvious answers … they just aren't stable yet: generators and try
  blocks." Combinators cannot early-return, because control flow cannot escape their closures.
  He argues against an `AsyncIterator` with `async fn next`, which would lose the core register.
  He stops before keyword generics, "a real can of worms".
- **"The problem of effects in Rust"** (13 April 2020, **part**). "Rust's design failed to
  consider carefully the integration between its control flow effects and its support for higher
  order functions". The result is the `try_`/`async_` adapter zoo. He names two remedies: effect
  abstraction, or closures that preserve Tennent's correspondence principle, so that `?`, `await`
  and `return` escape the closure. He doubts Rust will do either.
- **"Coroutines and effects"** (20 April 2024, **part**). Coroutines and effect handlers are
  isomorphic. Handlers are dynamically scoped: a generalisation of checked exceptions, with no
  mark at the call site. Rust's `Result` and `async`/`await` are statically typed and lexically
  scoped, and "coroutines strike me as the most promising" design.
- **"Let futures be futures"** (3 February 2024, **part**). Intra-task concurrency is "the point
  of async Rust": heterogeneous `select` and `join` inside one state machine, with no
  allocation. He is against `maybe(async)`, because sync and async code differ in exactly the
  cases that matter.
- **"Iterators and traversables"** (13 March 2024, **part**). Only a state machine that yields
  values one by one is an iterator. `ParallelIterator` is a traversable, not an iterator. He
  argues against "effects generics" that treat parallelism as an effect on `Iterator`.
- **"Why async Rust?"** (15 October 2023, **part**). Green threads were removed before 1.0 for
  three reasons: stack management without a GC, FFI cost, and unavoidable virtual calls and
  allocations. Futures are readiness-based state machines, like the 2013 iterator redesign. His
  one real regret: "you need to pin a future trait object to await it. This was an unforced
  error that would now be a breaking change to fix."
- **"Pin"** (19 July 2024, **part**) and **"Three problems of pinning"** (30 November 2023,
  **part**). `?Move` was rejected because a new `?Trait` is not backward compatible with
  associated types, so `Pin` became a library type. The costs:
  - no implicit reborrowing;
  - projections need macros;
  - `Drop` takes `&mut self`;
  - users meet a "complexity cliff".

  The third problem, awaiting a boxed future, comes from "a mistake that we made when we designed
  `Pin`": `Box<T>` is always `Unpin`.
- **"Changing the rules of Rust"** (17 September 2023, **part**). The 2015 decision was that
  every value may leak ("in some haste, because the 1.0 release was scheduled within a few
  months"). It forecloses linear types and causes the scoped-task trilemma. "If I could go back
  in time to 2015, I think I would probably add both Move and Leak to Rust." Adding them now
  breaks generic code, whether as auto traits or as `?Trait`s. "When it comes to Leak and linear
  types, I just despair."
- **"The Scoped Task trilemma"** (8 April 2023, **part**). Of concurrency, parallelisability and
  borrowing, "Any sound API can only provide at most two". The root cause is that "every object
  in Rust can be leaked without running its destructor" (the "leakpocalypse").
- **"Ownership"** (22 June 2024, **part**). A substructural taxonomy. Three wishes:
  - lift E0509, so that a type with a destructor can still be destructured;
  - decouple "normal" (copyable) types from `memcpy`, so that cheap `Rc` clones could be
    implicit;
  - add linear types, which are session types with no default transition.
- **"Asynchronous clean-up"** (24 February 2024, **digest**). There is no async `Drop`. He
  proposes `poll_cancel`, `do … final` blocks, and "undroppable" or "unforgettable" types.
- **"References are like jumps"** (13 May 2024, **part**). Hoare's 1974 warning about aliased
  mutable state, and Rust's answer to it. He points at Hylo as a direction: "ideally new
  languages would allow for imperative programming without any shared mutable state at all."
- **"Notes on a smaller Rust"** (17 July 2019, **digest**) and **"Revisiting a 'smaller
  Rust'"** (30 September 2020, **digest**). A higher-level language would keep ownership,
  borrowing, ADTs and RAII. It would drop low-level control, monomorphization, `Send`/`Sync` and
  macros, and use a GC for "data types", with affine semantics only for resources.

### 1.2 Graydon Hoare

**"The Rust I Wanted Had No Future"**, 4 June 2023, <https://graydon2.dreamwidth.org/307291.html>,
read in **full**. The live page now requires a Dreamwidth login, so it was read from the Wayback
Machine snapshot of 9 January 2025. Related posts by Graydon were not searched.

He first lists "agreeable improvements", early designs that others' input made better: move
semantics were opt-in, and there was a typestate system and an effect system that "mostly didn't
work (no effect-polymorphism)". He then lists the "disagreeable divergences", the things he "literally
didn't want, and/or currently don't like":

- **Cross-crate inlining and monomorphization.** "a big part of Rust's terrible compile times
  and lack of a stable ABI".
- **Library-defined containers, iteration and smart pointers.** He wanted them open-coded by the
  compiler.
- **Exterior iteration.** He wanted "stack / non-escaping coroutines" ("interior" iteration),
  "I wish Rust still had them".
- **Async/await.** He wanted green threads with growable stacks. He has "a grudging respect"
  for heterogeneous selects, but "still don't know that I think the result quite pays for
  itself".
- **First-class `&`.** "I wanted & to be a 'second-class' parameter-passing mode, not a first-class
  type … I didn't think you should be able to return & from a function or put it in a structure."
- **Explicit lifetimes.** Early borrow analysis used "type and path disjointness", with no
  lifetime variables. "They were supposed to all be inferred, and they're not".
- **Environment capture.** He dislikes lambda with capture "especially in a systems language
  with observable mutation", and prefers Sather-style bind expressions.
- **Traits.** "too type-directed, too global … too much coupling between libraries in terms of
  what is or isn't allowed to maintain coherence". He wanted ML-style first-class modules.
- **Underpowered existentials.** `dyn Trait` is discouraged by the ecosystem.
- **Complex inference.** He dislikes "playing type tetris".
- **Nominal types.** "Rust went too far into the Nominal camp".
- **Missing quasiquotes and reflection.**
- **Missing errors.** `?` is "only a half-copy" of Swift's model.
- **Missing auto-bignum and overflow traps.** "Swift at least traps in release by default -- I
  wish Rust had chosen to".
- **Missing decimal floating point.**
- **Complex grammar.** He lost the arguments over LL(1), "the angle brackets for type
  parameters", and the pattern-binding ambiguity.
- **Tail calls.** "I actually wanted them!"

His summary: "I would have traded performance and expressivity away for simplicity". He would
never have pitched zero-cost abstraction ("It's a C++ idea"). He closes: "The Rust I Wanted
probably had no future".

### 1.3 Niko Matsakis (blog: *baby steps*, smallcultfollowing.com/babysteps)

- **"Polonius revisited, part 1"** (22 September 2023, **part**). Origins become sets of loans
  rather than sets of points, and the goal is to accept NLL "problem case #3". He calls it "a
  stepping stone towards an analysis that can support internal references and self borrows".
- **"Must move types"** (16 March 2023, **part**). `?Drop` types must be moved or consumed. They
  would enable async drop, scoped tasks, and completion-style futures, which "must be fully
  polled". They would give "liveness conditions writ large": Rust is good at safety properties
  and "much less useful for liveness properties".
- **"Move, Destruct, Forget, and Rust"** (21 October 2025, **part**). A trait hierarchy
  `Forget` ⊂ `Destruct` ⊂ `Move` ⊂ `Pointee`, with `Forget` as the default bound and weaker
  bounds opt-in. He calls it "controlled destruction", needed "to complete the 'async dream',
  in which async Rust and sync Rust work roughly the same". Its cost is "more 'core splits'
  into Rust's types".
- **"Maximally minimal view types"** (21 March 2026, **part**). The partial-borrow problem:
  a method borrows all of `&mut self` when it touches one field. The proposal is to write
  `&mut self {statistics}` in signatures, auto-applied at method calls. It is purely static,
  limited in its MVP to private helpers, and has no inter-procedural inference. It follows
  "View types for Rust" (5 November 2021, **digest**).
- **Dada** (series of February 2026, **part**: "Hello, Dada!", "Dada: moves and mutation",
  "Sharing in Dada", "How Dada enables internal references"). Niko's own language, developed
  since 2021:
  - Parameters are read-only by default. `!` marks a mutable one, and `given`/`.give` marks
    moves, which are explicit.
  - Reference types name places, not lifetimes: "the resulting type names the *place that the
    data was borrowed from*, not the *lifetime of the reference*". This gives self-referential
    structs such as `items: Vec[ref[self.list] String]`.
  - Sharing is built in. `.share` flips a per-object flag, and heap data carries a ref-count.
    Dada accepts reference counting where Rust makes it a library choice.
  - Strings are one type (no `&'static str` versus `String` split).

### 1.4 Aria Desires (formerly Beingessner; "Gankra"; blog at faultlore.com/blah)

- **"Pre-Pooping Your Pants With Rust"** (27 April 2015, **part**). The leakpocalypse:
  `thread::scoped` assumed "that destructors are guaranteed to run in safe code", and an
  `Rc` cycle breaks that. Libraries must reach a safe state before relying on a destructor
  ("PPYP").
- **"The Pain Of Real Linear Types in Rust"** (8 May 2017, **part**). What people want is mostly
  must-use types. Retrofitting them hits:
  - unwinding: a panic abandons the value;
  - a `?Leave`-style trait, rippling through all generic code;
  - collection APIs that silently drop values;
  - `mem::forget`, "The All User of values".
- **"Rust's Unsafe Pointer Types Need An Overhaul"** (19 March 2022, **part**). Integer/pointer
  casts destroy provenance, and references make "extremely strong validity assertion[s]". The
  fixes proposed: `addr`/`with_addr`, a raw field-offset syntax `ptr~field`, and postfix
  dereference.
- **"The Tower Of Weakenings: Memory Models For Everyone"** (5 April 2022, **part**). There is no
  "One True Memory Model". Instead, a strict, teachable model sits over progressively weaker
  ones, and strict provenance is the top layer.
- **"How Swift Achieved Dynamic Linking Where Rust Couldn't"** (7 November 2019, **digest**).
  Polymorphic compilation and resilient layouts versus Rust's always-monomorphize.
- **"Destroy All Values: Designing Deinitialization in Programming Languages"** (23 January 2022,
  **digest**). The design space of drop flags and deinitialization.

### 1.5 Yoshua (Yosh) Wuyts (blog.yoshuawuyts.com)

- **"Extending Rust's Effect System"** (9 February 2024, a transcript of a RustConf 2023 talk,
  **part**). Rust already has effects: `async`, `const`, `unsafe`, `try` and generators. Without
  effect generics they duplicate APIs combinatorially: the `Fn` family alone would grow from 6
  traits to 96. The proposal is effect generics, in stages.
- **"Linearity and Control"** (23 March 2023, **part**). A `linear` effect on types and
  functions, with `linear Drop`. Linear values must stay live across "control points" (panics,
  `?`), and he distinguishes "must-await" from "must-consume" futures.
- **"Why `Pin` is a part of trait signatures (and why that's a problem)"** (15 October 2024,
  **part**). Return-position `impl Trait` forces `Pin` into `Future::poll`'s signature. So a
  pinned `Iterator` needs a whole new trait family. His answer is a `Move` auto trait.
- **"A Grand Vision for Rust"** (5 March 2026, **part**). Three directions:
  - more effects: no-panic, termination, determinism and no-I/O guarantees;
  - substructural types, with "`!Forget` unlocks linear types, `!Move` unlocks ordered types"
    ("unlike `Pin`");
  - refinement types: pattern types and view types.

  The aim is "the safest darn production-grade language in existence … we're no Ada/SPARK yet."
- **Read by title only**: "The Gen Auto-Trait Problem" (January 2025), "Syntactic Musings on View
  Types" (April 2025), "Tree-Structured Concurrency" (July 2023) and "Tasks Are the Wrong
  Abstraction" (April 2024).

### 1.6 matklad (Alex Kladov; matklad.github.io)

- **"Hard Mode Rust"** (6 October 2022, **part**). No allocation after startup: "For the
  library, all resources must be injected." Structs grow lifetime parameters, as in
  `Parser<'m, 'i, 'a>`. It works with less unsafe than he expected.
- **"Why Not Rust?"** (20 September 2020, **digest**). The costs he lists:
  - complexity: `&`, `&mut`, `Box`, `Rc` and `Arc` are all choices the programmer must make;
  - compile times, with no analog of the pimpl idiom;
  - no memory model for unsafe;
  - FFI friction.
- **"Zig And Rust"** (26 March 2023, **digest**). Zig passes allocators explicitly and has
  comptime. "Rust is about compositional safety … Zig is about perfection."
- **"Non-Send Futures When?"** (10 December 2023, **part**). `Send` is about OS threads, so a
  task that uses a `Cell` cannot move between threads even though it never runs in parallel. He
  proposes spawning a `Send` closure that builds the future, and making thread-locals unsafe.
- **"The Second Great Error Model Convergence"** (29 December 2025, **part**). Go, Rust, Swift
  and Zig converge on the same model:
  - call-site markers for fallible calls;
  - a separate panic path for bugs;
  - errors as values.

  This model is sensitive only to "0 to 1" transitions, where Java's checked exceptions are
  sensitive to "N to N + 1".

### 1.7 Others

- **BoxyUwU, "An Incoherent Rust"** (23 March 2026, **part**). Boxy is a contributor to the
  compiler's type system. Coherence and orphan rules lock in the crates that "got there first"
  (serde), and none of the relaxation proposals fixes that. The proposal is named impls passed
  as parameters, i.e. dictionary passing.
- **Matt Kline, "Async Rust Is A Bad Language"** (bitbashing.io, 8 September 2023, **part**;
  the author is identified by the page's contact line and handle, `mrkline`). `Send + 'static`
  pushes code towards `Arc`, and "Used pervasively, Arc gives you the world's worst garbage
  collector." He recommends threads and channels for most programs.
- **fasterthanlime (Amos Wenger), "Pin and suffering"** (28 March 2021). Title and date only; not
  read.
- **Hillel Wayne and Jon Gjengset.** No post by either that fits "what I wish Rust had done" was
  found in this search. That does not mean none exists.

### 1.8 Steve Klabnik

- **"Thirteen years of Rust and the birth of Rue"** (21 December 2025, **full**). It announces
  Rue. It lists no grievances with Rust: "I don't have a ton of thoughts about Rust to share
  today … I have my beefs and my regrets, like any real project, but for the most part, I am
  pretty happy these days." The motivation is to test whether a language can be built "without
  financial backing and a team" using an LLM (Claude).
- **"Rust 1.0, ten years later"** (15 May 2025, **digest**). A retrospective with no specific
  wishes.
- Rue's own design documents are in §3.

---

## 2. Themes across sources

Ranked by the number of sources in §1 that raise the theme. The abbreviations are:

| abbreviation | source |
|---|---|
| B | withoutboats |
| G | Graydon Hoare |
| N | Niko Matsakis, including Dada |
| A | Aria Desires |
| Y | Yosh Wuyts |
| M | matklad |
| R | Rue and Klabnik |
| X | BoxyUwU |
| K | Matt Kline |

| # | theme | count | sources | the wish, in brief |
|---|---|---|---|---|
| 1 | Leaks and linear types (`mem::forget`, `?Leak`/`Forget`, must-move) | 5 | B, N, A, Y, R | values that must be consumed; destructors that are guaranteed to run; scoped tasks and async drop depend on it |
| 2 | Simplicity over performance and expressivity (a "smaller Rust") | 5 | G, B, N, R, M | trade constant-factor speed for lower cognitive load |
| 3 | Explicit lifetimes and first-class `&` | 4 | G, R, N, M | second-class references (G, R), place-named references (N), lifetime proliferation (M) |
| 4 | Async design (colouring, `Send + 'static`, green threads) | 4 | B, G, M, K | B defends it, G has "grudging respect", M and K want non-`Send` or thread-based models |
| 5 | Error handling | 4 | G, B, M, R | a fuller `throws` model (G), `try fn` and Ok-wrapping (B), errors as values and bugs as traps (M, R) |
| 6 | Generators, coroutines and the missing control-flow register of iteration | 3 | B, G, Y | `gen` blocks (B), interior iteration by non-escaping coroutines (G), `gen` as an effect (Y) |
| 7 | `Pin` and self-referential types | 3 | B, Y, N | `Move` instead of `Pin`, a pinned `Iterator` and `Drop` (B), place-based internal references (N) |
| 8 | Effect polymorphism and keyword generics | 3 | Y, B, G | Y for it; B against `maybe(async)` and for effects as a pattern; G's early effect system "mostly didn't work" |
| 9 | Compile times, monomorphization and ABI | 3 | G, A, M | stable cross-crate entry points; polymorphic compilation |
| 10 | Traits, coherence and nominal typing | 3 | G, X, R | modules or named impls instead of global coherence; R has no interfaces yet |
| 11 | Structured concurrency and scoped tasks | 3 | B, N, R | borrowing, concurrency and parallelism all at once; R's ADR 0098 |
| 12 | Partial borrows and view types | 2 | N, Y | borrow a subset of `self` across a call |
| 13 | Unsafe pointers and provenance | 2 | A, M | pointers distinct from integers; a defined memory model |
| 14 | Integer overflow should trap | 2 | G, R | trap in release builds |
| 15 | Environment capture and closures | 2 | G, R | bind expressions (G); second-class callbacks with no closures (R) |
| 16 | Shared ownership and `Arc`/`Rc` as a GC | 2 | K, N | K: `Arc` is "the world's worst garbage collector"; N builds RC into Dada |
| 17 | Library-defined containers, strings and `&`/`Box` overloading | 2 | G, N | compiler-known containers (G); one string type (N) |
| 18 | Tail calls | 1 | G | |
| 19 | Grammar (LL(1), angle brackets) | 1 | G | |
| 20 | Explicit allocation and injected resources | 1 | M | "all resources must be injected" |

`RefCell` and interior mutability in general appear only indirectly. They come up in matklad's
`Cell`-in-futures example and in Kline's and Dada's shared-ownership points. None of the sources
read asks for a Rust without `RefCell`.

---

## 3. Rue

**Primary sources:**

- the website <https://rue-lang.dev/>;
- the tutorial, chapters 1 "Why Rue" (**part**), 8 "Ownership and Access Modes" (**part**),
  9, 11 and 16 (**digest**);
- the blog posts "Hello, World!" (21 December 2025, Steve Klabnik and Claude) and "The Story of
  Rue So Far" (22 December 2025, Klabnik), both **digest**;
- the repository <https://github.com/rue-language/rue>, at commit `815b9b7` of 27 September 2026:
  its README, and the Summary sections of ADRs 0008, 0013, 0037, 0062, 0088, 0096, 0097 and
  0098, all **part**.

Rue exists and is under active development. A first attempt was abandoned ("I overly vibed it",
"The Story of Rue So Far"), and the current repository is a restart. Its GitHub description
reads "A programming language that is higher level than Rust but lower level than Go. Someday,
anyways." Press coverage quotes a longer positioning sentence ("What if Rust wasn't trying to
compete with C and C++ …"), which was not found in the primary sources and is not relied on
here.

**What it is.** "an experimental systems programming language exploring memory safety without
garbage collection and higher-level ergonomics than Rust or Zig" (README). The website's
question is "Rust proved memory safety without garbage collection is possible. *Can it also be
easy?*" The compiler is written in Rust, emits x86-64 and AArch64 machine code directly with no
LLVM, and builds with Buck2. Most of the code is written by LLM agents, first Claude and later
also Codex, under Klabnik's direction. The project describes itself as partly "an experiment in
agent-assisted compiler engineering".

**Design choices, and how they differ from Rust:**

- **Second-class loans instead of lifetimes.** This follows Swift and Hylo, in the style of
  mutable value semantics (ADR 0008). There are three parameter modes:
  - move, the default;
  - `borrow`, for reading;
  - `inout`, for writing.

  Each mode is marked at the call site as well: `sort(inout scores)`. "loans are second-class: a
  borrow lives only for the call it is passed to. You cannot store one in a struct, return one
  from a function, or keep one in a variable." So there are no lifetime annotations, and slices
  `[T]` are argument-only views. Exclusivity is checked "fully statically" by access points
  rather than regions (ADR 0037). Rue names what this gives up: "You cannot build a linked list
  of borrowed nodes, or return an iterator that borrows a collection. Rue's bet is that most
  programs do not need to, and that the ones that do are better served by indices, owned values,
  and explicit copies than by a lifetime system." A later ADR (0062, July 2026) adds
  place-returning accessors (`v.get_ref(i)`). Dogfooding had shown that without them every
  tree-shaped program was forced "into flat-arena/ECS form".
- **Affine by default, linear on request.** Values are affine, and `@copy` is opt-in. `linear
  struct` values "must be consumed" on every non-diverging path (ADR 0008, implemented July
  2026). User destructors are `drop fn`, run in reverse declaration order.
- **Errors are values, bugs are traps.** `Option`, `Result` and `?` handle recoverable failures.
  Overflow, out-of-bounds and division by zero trap. "A trap runs no user code on the way out: no
  destructors, no handlers" (ADR 0088: no unwinding, no recovery). Exceptions are ruled out
  "Never, by design."
- **No macros, overloading or implicit conversions.** Each is an ADR (0086, 0087, 0090). The
  principle is "Locality of reasoning": "everything you need to understand a line of code should
  be visible on that line, or in the signature of what it calls."
- **Generics by comptime.** Zig-style, with types as the results of compile-time functions:
  `std.arraybuf.ArrayBuf(i32)`. There are no traits or interfaces yet ("Interfaces are the next
  major language feature under design").
- **Second-class callbacks and no closures.** A callback "cannot be stored in a local, a field,
  or a collection, returned, or captured, and there are no closures" (tutorial ch. 16; ADR 0096).
- **Structured concurrency only.** ADR 0098 (accepted September 2026, not yet implemented):
  "The operation cannot return until every child has finished". The first operation is
  `join_inout` on OS threads. The tutorial still says "Concurrency. None. Rue programs are
  single-threaded." There is no async.
- **No mutable globals** (ADR 0089).
- **A mechanized formal core.** ADR 0097 (September 2026) adopts a Lean 4 mechanization of a
  fragment of the core calculus as a "fourth view" of the language, "experimental and
  non-blocking". It has no CI gate until a safety proof covers the full core dynamics.

**Against Graydon's list.** Rue is close to what Graydon describes wanting:

- `&` as a second-class parameter mode, with no lifetime variables;
- no environment capture;
- overflow traps;
- simplicity over expressivity.

It differs in using comptime rather than ML modules, and in having no coroutines.

---

## 4. Mapping to borrow-core

Each theme gets one of four labels:

- **(a) addressed**: the design already answers it, and the citation says where;
- **(b) planned**: a named issue covers it;
- **(c) tension**: our design pulls against the wish;
- **(d) not addressed**.

"Proved" means a theorem in `Core/`. A **hypothesis** is labelled as one.

| # | theme | label | where, and how |
|---|---|---|---|
| 1 | Leaks and linear types | **(a)** | Types are linear. Implicit destructors are inserted by the checker, so the elaborated program stays linear (decision 23, SPEC §12). A must-consume type is a linear type with no derived drop: a declared type whose payload carries a token the checker cannot drop (#746). Leak freedom is proved: every run of a closed well-typed program can finish with all memory freed, under every allocator (`adequacyD`, SPEC §13). No rule forgets a codata thunk: `close` is mandatory (SPEC §7). There is no `Rc`, so the leakpocalypse's cycle cannot be built. Still open: destructors with effects that can fail (SPEC §12 Open). |
| 2 | Simplicity over performance | **(c)** | Our target is the other way: zero-cost, measured by allocation and indirect-call counts in the corpus gate, with monomorphization (decision 8). We share the explicitness of Graydon, Rue and Dada (capabilities, `box` at allocation sites), but not the "trade performance for simplicity" stance. |
| 3 | Explicit lifetimes and first-class `&` | **(c)** | Borrows are first-class types at lifetimes, `Imm 'a A` and `Mut 'a A`: the paper's calculus. Lends are scoped by callbacks (`withbor`), so no borrow outlives its scope, which is close to Rue's second-class loans in effect. The lifetimes are in the types, and `fn f<'a, 'b>` declares them (`corpus/fn-lifetime.bc`); a call infers each from its argument. Graydon, Rue and Dada each found a way not to write lifetimes, and we have not yet found ours (#54). |
| 4 | Async design | **(b)** | #52: cooperative, single-threaded first. A future is delay codata: poll is one observation, cancel is `close`. It lowers to stackless state machines with a portable LLVM counterpart (decision 25). There is no function colouring: divergence and, later, control effects are served by specialization at the callback's computation type (decision 35). Colour-free async is therefore planned, not built. |
| 5 | Error handling | **(a)** for partial operations; **(b)** for the error effect | Partial integer operations return `A ⊕ 1` where Wasm traps, "because a trap would abandon linear resources" (SPEC §8). Errors as an effect is #18 (`corpus/pending/raise-in-fold.bc`). The strings design asks whether text functions wait for it (`docs/strings-slices-design.md` §10 Q7). |
| 6 | Generators and coroutines | **(a)** core register; **(b)** control-flow register | Codata `νX. C` is the core register: `Iter`, `Stream` and `Loop` are abbreviations (SPEC §7, decision 28). `for` is the consuming register (decision 33). Adapters are library code over `Iter`. Direct-style generators elaborated into an `unfold` state machine are pending (#18, `corpus/pending/generator-handler.bc`). We have folds (interior iteration, as Graydon wanted) as well as codata (exterior). |
| 7 | `Pin` and self-referential state | **(a)** today, by exclusion; **(b)** for the claim that we need no `Pin` | Today no value can hold a borrow of itself: lends are scoped, and "a borrow cannot make a value self-referential" (`docs/strings-slices-design.md` §3.2). That is boats' option 1 ("generators … cannot contain self-references") by construction. That async needs no `Pin`-like mechanism is a **hypothesis** in #52 phase 3 ("only cells are borrowable; owned cells have stable addresses"). It is untested. The related limit is real: `corpus/pending/borrow-across-loop.bc`, where a borrow block's body is one `F` computation, so no loop can run inside a borrow. A generator that holds a borrow across `yield` is that program. |
| 8 | Effect polymorphism and keyword generics | **(a)** whole-program; **(c)** separate compilation | Decision 35: specialization at the callback's computation type, with no polymorphism over computation types in the kernel. Two limits are recorded as pending: a div callback inside a fold's algebra (`map-div-fold.bc`), and callbacks stored in data (`callbacks-in-data.bc`). Separate compilation needs effect polymorphism (`corpus/axes/README.md`, #63). The CBPV core makes boats' registers explicit: the core register is a type (`F`, `ν`), and the control-flow register is elaboration. |
| 9 | Compile times, monomorphization and ABI | **(c)** | Decision 8, monomorphization with no type `∀` in the core, is Graydon's and Aria's complaint as a design rule. Specialization copies functions (`h__k`, decision 36). How monomorphized generics cross module boundaries is open in #63. No stable ABI is planned. |
| 10 | Traits and coherence | **(a)** for coherence, trivially; **(d)** for ad hoc polymorphism | There are no traits (`docs/strings-slices-design.md` §3.2), so no orphan rule. The core is structural (decision 9), which is Graydon's preference. Abstraction is planned through opaque types in the module system (#63), closer to ML modules than to traits. There is no answer yet for `Hash`, `Ord` or `Display` over user types (#64 hash maps will meet it). |
| 11 | Structured concurrency and scoped tasks | **(a)** root cause; **(b)** the API | The trilemma's cause, leakable destructors, is absent (row 1). #52 records "Scoped tasks that borrow from the spawning scope are sound (futures cannot be forgotten)" as decided. That is not built or proved. Fork-join is #22. `borrow-across-loop.bc` is a limit for scoped spawning. |
| 12 | Partial borrows and view types | **(a)** within a function; **(d)** across an abstraction boundary | Places by disjointness, and family borrows at one lifetime (decision 5, SPEC §5, `experiments/Places`, `LeafPlaces`). There are no methods, so a function takes the field borrows it needs. There is nothing yet like Niko's `&mut self {field}` that names a subset of an opaque type's fields: that needs #63's visibility. |
| 13 | Unsafe pointers and provenance | **(a)** | Decision 27: `unsafe` is an extern whose body we compile. There are no unsafe blocks inside safe code, "so raw pointers never flow into safe code and provenance tracking is unnecessary". The trusted base is enumerable (`bcc trusted`, #79). |
| 14 | Integer overflow should trap | **(c)** | Arithmetic is Wasm's: `add` wraps (SPEC §8). Traps are avoided because they abandon linear resources. So overflow is silent: the opposite of Graydon's and Rue's wish, and for a reason they do not face (Rue's traps run no destructors because it has no leak-freedom theorem to keep). Checked operations returning sums, like `div_s`, would fit the model. Not planned. |
| 15 | Environment capture and closures | **(a)**, with a known cost | Closures are `!T` and capture only persistent values (decision 3, SPEC §2). Borrow and fold callbacks are second-class blocks (`docs/surface-cbpv.md`). This is close to Graydon and Rue. The cost is that a `!` closure cannot capture an `i32` (`closure-captures-int.bc`, #9). |
| 16 | Shared ownership and `Arc`/`Rc` | **(a)** by exclusion; **(b)** for the replacement | No GC, no RC (the standing constraint). Graphs and shared strings go through arenas and indices (#94; `docs/strings-slices-design.md` §2.3). Dada chose the opposite (built-in RC), and Rue chose the same as us (indices). |
| 17 | Containers, strings and `&`/`Box` overloading | **(b)** | `docs/strings-slices-design.md` (merged in #104) splits Rust's `&` and `Box` jobs and derives the string types from independent axes (§2, §3). It is a design; K0–K5 are not built. |
| 18 | Tail calls | **(a)** | Explicit tail calls lower to `return_call` (LLVM `musttail`) (decisions 14 and 25). Loops run in constant stack (decision 24). |
| 19 | Grammar | **(c)**, minor | `>` inside `< … , … >` closes the pair, so `if i > n` in an observation is a parse error (`corpus/axes/README.md`, "Smaller things"). This is Graydon's angle-bracket complaint, met already. |
| 20 | Explicit allocation and injected resources | **(a)** for I/O; **(b)** for allocation | Capabilities with no ambient authority: a function given no capability performs no effect, which is proved (`wpTSD_frame_own`, decision 30). This is matklad's "all resources must be injected" as a theorem. Allocation is visible at `box`, but it is not a capability: `noalloc.bc` is pending, and implicit growth in `push` is open (`docs/strings-slices-design.md` §10 Q2). |
| — | Interior mutability (`RefCell`) | **(a)**, with a tension in #52 | None: `Imm` is deeply immutable in the model, and the frame results depend on it (`experiments/InteriorMutability`). Its survey recommends arenas, then handlers. But #52 phase 6 plans "a minimal interior-mutability primitive (a ready flag)" for wakers. That is exactly the place matklad's non-`Send` future post shows interior mutability entering async Rust. |

**Summary of the labels.**

| label | themes |
|---|---|
| (a) addressed | 1 leaks and linear types; 13 unsafe and provenance; 15 closures (with a known cost); 18 tail calls; `RefCell`; 20 injected I/O |
| partly (a) | 5 errors (partial operations); 6 generators (core register); 7 `Pin` (by exclusion); 8 effect polymorphism (whole program); 10 coherence (no traits); 11 scoped tasks (root cause); 12 partial borrows (within a function); 16 shared ownership (by exclusion) |
| (b) planned | 4 async (#52); 5 the error effect (#18); 6 generators (#18); 11 scoped tasks (#52, #22); 16 arenas (#94); 17 strings (design doc); 20 allocation (`noalloc`) |
| (c) tension | 2 simplicity versus zero cost; 3 explicit lifetimes; 8 separate compilation; 9 monomorphization and compile times; 14 overflow wraps silently; 19 grammar |
| (d) not addressed | 10 ad hoc polymorphism over user types; 12 view types across an abstraction boundary |

---

## 5. Lessons for borrow-core

These are the mistakes the sources say they wish they had avoided and that we are positioned to
repeat, or the choices they wish they had made that we must not give back.

1. **Settle self-reference before the iteration interface freezes.** boats' deepest regret is an
   unpinned `Iterator::next`. Our `borrow-across-loop.bc` is the same question: can a generator
   or future hold a borrow across a suspension? The #52 hypothesis should be tested before `Iter`
   and the generator elaboration (#18) are fixed.
2. **Never trade away leak freedom for convenience.** Rust's 2015 "any value can leak" decision
   is the one boats, Niko, Aria and Yosh each spend posts trying to undo. Any future opt-in to
   shared ownership, or a `forget` at resourceful types, would reopen it. Keep `adequacyD` as
   the invariant the design protects.
3. **Ship the control-flow register with the core one.** Rust has futures with `await`, but
   iterators with no generators and `Result` with no `try`. We have codata and `for`, but no
   generators or errors in direct style. #18 is where iteration and fallibility get their
   control-flow register, and they should arrive together.
4. **Linear types meet non-local exits; design the error effect for that first.** The pain Aria,
   Yosh and Niko describe is linear values meeting panics and `?`. `raise-in-fold.bc` already
   shows ours: unwinding the abandoned rest and the order of errors. Decide how `raise`
   releases linear state before the error effect lands.
5. **Decide separate compilation before the module system hardens.** Graydon's top complaint is
   monomorphization's cost to compile time and ABI. Decision 8 and specialization (decision 35)
   are the same bet, and #63 must say what crosses a module boundary.
6. **Lifetimes on the surface are the most-cited cognitive cost.** Graydon, Rue and Dada each
   avoid them by a different mechanism: second-class `&`, second-class loans, and place-named
   references. Our lends are already scoped. `fn-lifetime.bc` should get elision or place-based
   defaults, not only syntax for `'a`.
7. **Make overflow a decision, not an inheritance.** Wrapping comes from Wasm, not from a
   choice. Graydon and Rue both want traps. We cannot trap without abandoning linear
   resources, so checked operations returning sums (as `div_s` already does), or an abort
   effect, need to be weighed and recorded.
8. **Keep wakers out of `Cell`.** #52's "ready flag" is where interior mutability would enter,
   as matklad's `Cell`-across-`.await` example shows it did in Rust. Model readiness as a
   capability or a handler (#18) rather than as a shared mutable cell.

---

## What could not be found or verified

- **Graydon's other posts.** They were not searched. His main post is now behind a Dreamwidth
  login, and it was read from the Wayback Machine snapshot of 9 January 2025.
- **Posts read by title only:**
  - withoutboats: "Coroutines, asynchronous and iterative", "Pinned places", "UnpinCell" and
    "Generators II" (the `?` problem);
  - Yosh: "The Gen Auto-Trait Problem", "Syntactic Musings on View Types" and
    "Tree-Structured Concurrency";
  - Niko: "View types for Rust" (2021), later Polonius posts, and his coherence posts;
  - Klabnik: "When should I use String vs &str?" and "Arguing about arguments" (21 September
    2026).
- **"Pin and suffering".** Title and date only.
- **Hillel Wayne and Jon Gjengset.** No wishlist-style post about Rust was found.
- **Rue's positioning sentence.** The sentence quoted in press coverage ("What if Rust wasn't
  trying to compete with C and C++…") was not found in Rue's repository, website or Klabnik's
  announcement, and is not used here.
- **Rue's other ADRs.** Only their Summary sections were read. `unsafe` and raw pointers
  (ADR 0028), FFI (ADR 0064) and the Lean mechanization's content were not examined.
