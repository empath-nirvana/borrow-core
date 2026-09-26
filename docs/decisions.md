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
    rule, even when nothing reads it ([l_lang kernel](l-lang-kernel-and-lit.md), lesson L1).
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
