# Design decisions

Each entry: the decision, and why. Newest last.

1. **Start from the paper's calculus, not a new one.** Its semantic model already proves safety,
   leak freedom and termination without step-indexing; extensions are measured against it.
2. **Spec first.** The library implements `SPEC.md`; experiments live in `experiments/` and land
   only through a spec entry.
3. **Closures through `!T`, not a closure former.** A closure former's borrowed image is not
   determined by its type (refuted in `experiments/BorrowedClosures`); `!T` holds no resource.
4. **A call-by-push-value core.** Values and computations kept apart make codata, thunks and
   reification explicit, so the cost model can live in the types.
5. **Places by disjointness, not witness splitting.** Same-lifetime views through a pointer are
   excluded by the model (`experiments/FrameEnd`); borrowing disjoint places at one lifetime is
   derivable with no model change (`experiments/Places`, `LeafPlaces`). `split_at_mut` is a
   stretch goal.
6. **`Box<struct>` is a block.** A struct's handle is the family of its leaves, so field borrows
   and the fold rules apply directly.
7. **Recursion without step-indexing.** Inductive types by least fixed points, codata by greatest
   fixed points with a mandatory `close`, loops by `fixD` over explicit state; divergence shows in
   the type.
8. **Monomorphization, no type `∀` in the core.** Generics are definitions re-checked at each use.
9. **A structural core.** Names are abbreviations; nominal types and abstraction are a surface or
   module concern, via opaque types.
10. **Integers as term constants with a parametric host.** Nothing about arithmetic is proved:
    every theorem holds for every host, and compiler correctness will use the target's own
    operations.
11. **Persistent values are reused implicitly.** Types holding no resource may be copied and
    dropped by context splitting.
12. **The checker is derived from `CDerives`.** Every step applies one rule; incompleteness is
    listed once, never fixed by changing the judgment.
13. **Core syntax first, sugar from measured pain.** Sugar is syntactic, desugars before
    checking, and is not in the trusted base.
14. **A compiler MVP that keeps options open.** Uniform representation with exact memory
    accounting, explicit tail calls, per-stage interpreters, a backend-neutral flat IR, and
    wasmtime as the engine. Talos is deferred until its interfaces settle.
15. **Shallow handlers are primitive; deep handlers are derived.** A suspended computation is
    codata; one observation is a shallow handler, and a deep handler is a fold or a loop.
16. **Monads stay in the core.** The surface is direct style.
17. **A feature is done when it compiles.** Spec, core proofs, checker, lowering and a running
    corpus program, together.
18. **The LLVM path proves contract satisfaction, not LLVM's optimizations.** Deferred until
    there is an LLVM backend.
19. **No judgment index "for later".** A new coordinate (grades, temporal order) goes in a type
    former or in the model, never as a defaulted index on `CDerives`: every index is a tax on every
    rule, even when nothing reads it ([l_lang kernel](https://github.com/empath-nirvana/borrow-core/blob/main/docs/l-lang-kernel-and-lit.md), lesson L1).
20. **A generalization lands with the deletion of its instances.** When a general former replaces
    fixed ones (general `ν` for `delay` and `stream`), the fixed ones become abbreviations in the
    same change; building the general form alongside them only adds proof (lesson L5).
21. **Inverting `CDerives` is paid for deliberately.** The Fundamental Property never inverts the
    judgment, which is why each rule costs one compatibility lemma. Inversion lemmas, syntactic
    substitution over derivations, checker completeness and lowering proofs that invert typing
    bring per-rule pairwise burden back; take them on only with the cost stated (lessons L2, L3).
22. **Optics are a parallel to borrowing, not its abstraction.** Lenses, prisms and traversals
    share a borrow's shape (a focus and a residual, put back later) and derive from existing rules
    (`experiments/Optics`), but they do not explain why borrows are safe: every law that matters
    needs a frame fact that comes from lifetimes and typing. The search for the underlying
    abstraction continues at the frame guarantee (lifetime parametricity).
23. **Implicit destructors, not affine types.** An owned value that goes unused is consumed by its
    derived destructor, which the checker inserts (SPEC §12), so the elaborated program stays
    linear and leak freedom is `adequacyC` on it. Only the forgettable types, whose destructor
    does nothing, are affine. A destructor that frees or closes is an action whose placement can
    be observed. It goes at the end of each path, never earlier than an effect, and the opt-out is
    a `linear` binder rather than a grade on types. Types without a destructor stay linear.
24. **Recursion is always structured; users are expected to know map and fold.** There is no
    general direct recursion on the surface: it is a source of stack overflows, accidental
    non-termination and invisible cost. Finite data is folded, iteration is a loop over explicit
    state, streams are codata. The one concession is `for x in it { … }`, sugar for a
    `for_each` consumer. Stack safety is a compiler property of each structured form, established
    once: loops run in constant stack, owned right folds can use pointer reversal (sound because
    linearity gives exclusive ownership), borrowed folds use an explicit stack.
25. **Every lowering has a plain LLVM counterpart.** Wasm is the verified target, but no
    semantics may depend on a Wasm-only feature: stack switching (WasmFX), `resume_throw`, Wasm
    exceptions and Wasm GC may appear only as optimizations with a portable fallback. Async,
    generators and effect handlers therefore lower to stackless state machines (as Rust `async` and
    LLVM's `llvm.coro` do), and cancellation is the explicit `close` observation. Today's backend
    emits only portable features: integer operations, loads and stores, `br_table` (a switch),
    `call_indirect` (function pointers), `return_call`/`return_call_indirect` (LLVM `musttail`,
    which needs matching signatures — the uniform word representation provides them) and
    `memory.grow` (the allocator's host call).
26. **Sugar may be type-directed.** This revises decision 13's "sugar is syntactic": elaboration
    may use types (filling type holes `_`, choosing `fold_imm`/`fold_own` from a type, inserting
    copies or drops). It stays outside the trusted base anyway, because its output is a core program
    that the checker must derive, returning a `CDerives` proof. What sugar may not do is hide a
    surviving polarity shift (`docs/surface-cbpv.md`).
27. **`unsafe` is an extern whose body we compile.** Safe code meets unchecked code only at a
    trusted boundary with a semantic-type contract (the logical relation at the declared type). The
    body may be host code (FFI) or low-level code of our own that the compiler compiles; the
    contract may be assumed (then it is a hypothesis of the end-to-end theorem) or proved in Lean
    (then it drops off the trusted base). There are no unsafe blocks inside safe code, so raw
    pointers never flow into safe code and provenance tracking is unnecessary; the set of unproved
    boundaries is the program's enumerable trusted base. A boundary can migrate — host extern,
    compiled unsafe body, proved body — without its type or callers changing.
28. **Codata is one former, `νX. C`, and its variable is a value type.** `X` occurs only as `U X`,
    which is the value-type variable `0` of `C`'s observations, so `ν` reuses `μ`'s substitution
    and environment machinery and `cC` takes no environment of its own. The body is a `&` of
    observation trees ending in `F A` with `U X` only under `⊗`/`⊕` (SPEC §7): that is where
    coiteration can map a state to the rest, and it keeps `X` out of `Mut` payloads, where the
    relation would not be monotone. A `ν` outside that class holds everywhere, like `⊤`, and has
    no eliminator. Delay, stream and finite iterators are abbreviations; iterator adapters are
    library code over `Iter`, never formers or rules (rule 20).
29. **Arrays are primitive: the run-time-sized family of places.** Places come in a square:
    statically sized values (records), run-time-sized values (`μ`), statically sized families of
    places (blocks, §5), and run-time-sized families of places, which only a primitive gives.
    `[L]` (SPEC §9) is the type-level `⊛_{i<n} L`: `Array A = [Ref A]`. An array is a value, so it
    is borrowed in a cell, `Imm 'a (Array A)`, and `withload` turns that borrow into the family of
    leaf views `[Imm 'x A]` at a shorter `'x`; a leaf view is taken at the family's lifetime. A
    leaf view at `'a` itself would be a view through the pointer, excluded (decision 5). Records
    are not arrays: l_lang tried arrays as indexed records, and labels have no arithmetic,
    lengths are static, and heterogeneous fields block run-time indexing. One `VTy` former is
    paid for (the growth rule's cost, accepted here); `Vec`, `Str` and sized types are later,
    over it.
30. **No ambient authority: one capability per effect.** Every I/O operation takes a
    capability value, and there is one capability type per effect, not a monolithic `IO` or
    `World`: `stdin`, `stdout` and `stderr` now (SPEC §11), and `Args`, `Env`, `Fs`, `Net`,
    `Clock`, `Random` later by the same pattern. A capability is a cell with opaque content and
    its operations take a `Mut` borrow, so a function's type shows exactly which effects it can
    perform, and `main` hands each callee only what it needs. That a function given no
    capability performs no effect is a theorem (the frame result, `wpTSD_frame_own`), not a
    convention. `main` uses its bundle implicitly, as sugar elaborated to explicit capability
    passing (SPEC §11); no other function may. Operations are externs rather than rules, so a
    capability can later be served by a user-defined handler (#18) instead of the host.
31. **Host resources are opaque types with a model.** One leaf former, `VTy.opq k`, whose
    relation is a predicate `k.Holds` on values and whose `Imm̲` is `Unk`: not persistent, no
    destructor, no rule. Its values can only be moved and handed to externs, so a handle is never
    copied (l_lang's L-199) and the model and the host can represent it differently (a byte list,
    a file descriptor). A new host resource is a new `k`, not a new former.
32. **Provisional (SPEC §11, to be confirmed by the user).**
    - The surface names `input` and `output` for the opaque types, and the extern names
      `stdin`, `stdout`, `stderr`, `read_byte`, `write_byte`, `mk_input`, `mk_output`,
      `take_input`, `take_output`.
    - `stdout` and `stderr` share the type `Output`; a writer is given an output stream.
    - Two primitives, `read_byte` and `write_byte`, on `Mut` borrows; lines, chunks and numbers
      are library loops.
    - A `main` with capability externs has type `F (Caps ⊗ A)`, handing its capabilities back
      in declaration order.
    - The byte list is `μX. 1 ⊕ (I32 ⊗ X)` with bytes as `I32`; there is no `u8` yet.
    - A `def` may use the persistent externs declared before it (the operations), never a
      capability, so helpers can call `read_byte`/`write_byte` without taking them as
      arguments while every capability still has to be passed.
    - `bcc interp` runs the model, which reads all of standard input before the program runs;
      `bcc run` is interactive and unbuffered.
33. **Sugar is elaboration, and a program may run until its input ends.** Ambient capabilities
    in `main`, `&c` and `for` are elaborated by the frontend (`Frontend/Sugar.lean`) into core
    that the unchanged checker checks; nothing in the kernel, the checker's rules or the proofs
    knows them, and `corpus/sugar/` pairs each with its core form. What is not sugar is running a
    loop at the top level: `main` may return `U (Loop (Caps ⊗ A) (Caps ⊗ B))`, which the runtime
    drives, covered one prefix at a time by `driveE` (SPEC §7, §11). It needs no kernel change
    and has its own spec entry and theorem.
34. **Provisional (SPEC §11, second pass, to be confirmed by the user).**
    - `&c` lends an owned capability to one call that hands it back first. This differs from
      draft 0's `&mut x` (`docs/surface-cbpv.md`), which borrows a `let mut` cell: `&c` moves the
      cell and rebinds it. The spelling may change when #54 step 2 settles the surface.
    - `for x in e { M }; N` is draft 0's form, but only at the end of a `main` with ambient
      capabilities and only over `bytes c`; the threaded locals are typed by their bindings,
      since the elaborator sees no types. There is no early exit.
    - The ambient trigger: a program that declares no externs and whose `main` names `stdin`,
      `stdout` or `stderr`. Such a program gets the I/O library (`lib/io.bc`).
    - The library's names (`getb`, `putb`, `put_dec`, `bytes`, `In`, `Out`, `Bytes`) and its
      convention that a helper hands its capability back first.
    - `loop A B` as a type keyword; `D A = loop A 1`.
    - No line reader: an observation must terminate, so a line of unbounded length is a loop of
      its own.
    - I/O errors stay unmodeled.
