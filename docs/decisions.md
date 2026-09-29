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
    emits only portable features: integer operations, loads and stores, `br_table` (a switch; LLVM
    `switch`, which also dispatches defunctionalized closures), `return_call` (LLVM `musttail`) and
    `memory.grow` (the allocator's host call). No function table or `call_indirect` is emitted.
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
    - `for x in e { M }; N` is draft 0's form, only over `bytes c`; the threaded locals are
      typed by their bindings, since the elaborator sees no types (withdrawn by decision 36:
      they are inferred). There is no early exit. Its
      restriction to the end of an ambient `main` is withdrawn by decision 35.
    - The ambient trigger: a program that declares no externs and whose `main` names `stdin`,
      `stdout` or `stderr`. Such a program gets the I/O library (`lib/io.bc`).
    - The library's names (`getb`, `putb`, `put_dec`, `bytes`, `In`, `Out`, `Bytes`) and its
      convention that a helper hands its capability back first.
    - `loop A B` as a type keyword; `D A = loop A 1`.
    - No line reader: an observation must terminate, so a line of unbounded length is a loop of
      its own.
    - I/O errors stay unmodeled.
35. **Divergence is an effect** (SPEC §14, #81). Any function may loop without bound if its type
    says so; it is not a privilege of `main`, and code without it is total (a theorem,
    `total_no_infinite_run`). A div function returns a loop, `A ⇒ U(Loop B R)`; sequencing loops
    is the delay bind, library code over `unfold`, and running a loop is handling the effect: the
    runtime drives `main` forever, and `div_fuel` runs `n` steps, which turns div code into
    total code. Divergence is inferred in declaration order, so no annotation is needed;
    `total def` is the annotation that matters, a promise the elaborator checks. Everything is
    elaboration: the checker, the kernel and the proofs see only core. A higher-order function
    serves total and div callbacks alike by specialization at the callback's computation type,
    the mechanism later control effects (async, #52; handlers, #18) reuse, so there is no
    function coloring and no kernel polymorphism over computation types.
36. **Provisional (SPEC §14, to be confirmed by the user).**
    - The markers are `total def` and `div def`, written before `def`; `div` never needs to be
      written. In draft 0's surface they would be `total fn` and `div fn` (or `-> div T`).
    - *Withdrawn* (typed elaboration, stage 2): the residual was recognized by the names `In`,
      `Out`, `ref input` and `ref output`. It is now read off the result type: the components
      with no destructor (SPEC §12), paired with `()`, or `1` (SPEC §14).
    - *Withdrawn* (stage 4): a `main` that looped but used no capability was given `stdout`
      ambiently, so the runtime could drive it. The runtime now drives a loop with no
      capabilities (SPEC §11).
    - The library names `div_bind` and `div_fuel` (`lib/div.bc`), with the fuel an `i32`.
    - *Withdrawn* (stage 2): a direct-style div call was only the head `return (f V)` of a bind
      or a terminal. It is now any application whose type is a loop where that loop is not the
      type expected, at any depth; checked against its loop type, it is the loop as a value.
    - *Withdrawn* (stage 2, with decision 34): the variables a `for` threads were typed by
      their bindings `y : T <- …`, and an injection needed an ascription. Both types are now
      inferred (`docs/typed-elaboration.md`).
    - *Withdrawn* (stage 3): specialization covered only a named div function passed by name.
      It now covers any callback whose type inference knows: locals, returned callbacks, and
      closures (elaborated as div bodies when they loop), at parameter types only.
    - A copy made by specialization is named `h__k`.
37. **Draft 0's surface is the core's grammar, extended** (typed elaboration, stage 5; the user's
    decisions 1–7 in `docs/typed-elaboration.md` §8). One grammar and one `.bc` file type:
    the surface forms and the core forms mix freely. A surface form that needs no type is
    desugared by the parser into core at its own spans (`let` with patterns, `match`, `e;`, a
    tail expression, forces, the rebinding of a borrowed place, `fn`); one that needs types is a
    `Val.sugar` node that the elaborator turns into core with every bracket argument written
    (literals, operators, `alloc(e)`/`free(e)`/`swap(c, e)`, blocks and closures, borrow blocks).
    The checker sees only core. Draft 0 is followed except:
    - a call `f(e)` of a persistent function has `unbang` inserted by type, so `f(e)` is also
      the core application `f e`, parenthesized; a call of a constant is `alloc(e)`, with its
      brackets filled, only for `alloc`, `free` and `swap`;
    - `(V₁, …, Vₙ)` is the right-nested tuple, for n-ary calls; bare sequencing `M; N` and a
      value as a computation, which draft 1 of the core syntax rejected, are statements;
    - a borrow block on a named place rebinds the place, as `&c` does (§5.1 of the note);
    - unit elision is at `modify`'s body and at the result of a block used as a statement;
    - `x <- e` with `e` a value is allowed (`<-` is required for forces, not reserved to them);
    - not yet provided: lifetime parameters of `fn` (`fn f<'a>`, written as a core `def`),
      `reborrow`, `load` and `*v`, the family borrow `imm`, codata construction and observation
      (`loop f from e`, `.next`, `.close`), fold blocks, `|>`, `if`, `let mut`, `&mut`, and the
      operators `& | ^ << >>` and unsigned comparisons (a host operation is called like a
      function: `host[lt_u32] (a, b)`).
38. **Places and conditions of the surface** (typed elaboration, stages 6–7).
    - **One lend, by type** (the user's decision 3). `&mut x` lends `x` exclusively and `&x`
      shared; after the call `x` is the place handed back. The mechanism is the parameter's type:
      a borrow `mut 'a A`/`imm 'a A` under the function's lifetime binder is a `withbor2`/
      `withbor1` of the cell `x : ref A`, or of a cell scoped to the call when `x : A` is a
      value; a parameter of `x`'s own type takes `x` and hands it back first (a capability). The
      lent place stays the borrow's place, so every mechanism rebinds `x` through the one lend
      rebinding of SPEC §11. `&c` for the exclusive lend is retired; the corpus says `&mut c`.
    - **`let mut`** is rebinding: `x = e` binds `x` again, and is allowed only for a `let mut`
      variable. A `match` or `if` whose arms assign `let mut` variables hands them on after it
      (each arm returns them, in declaration order; the join), and a `for` threads them as it
      threads any variable its body reads. A `let mut` value lent with `&mut x` or `&x` is in a
      cell scoped to that one call; there is no cell for its whole life.
    - **`*e`** reads a persistent content: of an `imm` borrow through `withload`, or of a cell
      `x : ref A` borrowed `imm` around the read. A `mut` borrow is read by `modify`.
    - **`bool` is `1 + 1` with `inr ()` true**, as the host's comparisons return it. `bool` is
      written by the parser as `1 + 1`; `true`, `false` and `not` are the prelude's.
    - **The prelude and `include`** (#59). `lib/prelude.bc` is in scope in every program, and a
      declaration of it is emitted only when the program names it, as the I/O and divergence
      libraries are. `include m` puts the declarations of the embedded module `lib/m.bc` at that
      point, at most once; the modules are a table in `Frontend/Sugar.lean` (`libModules`), so a
      new library module (arena and array helpers, the standard library) is a file of `lib/` and
      a line there. Include of a user's own file, and namespaces, are the module system (#63).
    - `&&` and `||` are `case`s that do not evaluate their right operand when the left decides;
      `if c { … } else { … }` has braces, and `else if` nests.
    - Not yet provided: a reborrow `&mut m` of a `mut` borrow, a lend inside a nested
      computation of a call's argument, `*m` of a `mut` borrow, and assignment inside a closure
      or a borrow block of a variable outside it.
39. **Deep copies are written (#108; confirmed by the user).** Revises
    decision 11 at the surface; the core rule is unchanged.
    - A use of a persistent variable that the compiled program copies deep (the variable is used
      again later, and its type holds recursive data: a `μ`, also under `⊗`, `⊕`, `[@a]`, `!`)
      is written `clone(x)`; without it the program is rejected at that use, with the later use
      named (`Frontend/Elab/Copies.lean`). `clone(x)` is `x` in core. Rust's split: trivial
      types (`i32`, `bool`, their products) copy implicitly, like `Copy`; recursive data is
      copied only where written, like `Clone`.
    - Which uses copy follows closure conversion's ownership plan on the elaborated core: the
      earlier of two sequential parts gets the copy, and the two arms of a `case` (or the two
      components of `<M, N>`) are one part.
    - The rule is by type, so that it can be read off the program: the backend's layout types
      are sharper (a list whose tail no code reads is not recursive at its layout, and copies as
      words), and there a written `clone` copies nothing.
    - Generated code does not make copies the program did not ask for: a generator's loop hands
      on at a `break` only the threaded variables that what follows reads (and the linear ones),
      so `match unroll l { inl u -> break | … }` does not copy `l` (`corpus/gen-close.bc`, 4
      allocations, where handing `l` on copied it at every step). Generated code that does copy
      is rejected like written code, and the error names the sugar.
    - `copy` is taken (the core constant `copy[a, A]` of an `imm` borrow); `clone` is a new
      keyword. `clone` of a value that is not persistent is an error.
    - Not checked: a persistent closure's copy, which copies what it captures (its type does not
      say what); `bcc-counts` reports every deep copy a run makes (`copies`), and
      `corpus/counts.expected` bounds it per program.
    - Alternative not taken: the backend proving the later use dead and eliding the copy. The
      reported case was a use generated by the sugar, which is now not generated; the one written
      case in the corpus (`corpus/axes/free-monad.bc`) needs the copy.
40. **Provisional (SPEC §14, borrow scopes over loops, per observation; O1 step 1; to be confirmed
    by the user).**
    - **Per observation, not spanning.** A borrow scope around a loop lends its owner again at
      each observation (`experiments/LoopBorrow`); no rule lends across observations. The
      elaboration is `Frontend/Elab/LoopLend.lean`, with two hooks in `Sugar.lean` (a binding
      whose head is such a block, and a `def` over a borrow before it is elaborated).
    - **The library's names**: module `lend` (`include lend`); `loop_lend_imm`, `loop_lend_mut`,
      `gen_lend_imm`, `gen_lend_mut` (the codata kind first, as `div_bind` and `gen_bind`), and
      `array_each_imm` for the push-form lending loop over an array. Each takes `(steps, (owner,
      state))` and returns the codata; steps return plain values, which the combinator boxes.
      The experiment's `lend_loop_imm`, `lend_gen_mut`, `lend_each` and `zip2` are these.
    - **Inline, not the combinator.** A borrow block over a `for` elaborates to the combinator's
      form written inline (the `for`'s own `unfold`, with a `withbor` around each step), so that
      each step is known code: `corpus/lend-pipeline.bc` makes no dispatched call.
    - **Stretches.** Only the stretches of the block's body that use the borrow are in blocks;
      a stretch hands on the names later code reads. A name the block binds again that is read
      after the block is an error, not a shadowing: the block's loop is in the enclosing body.
    - **`let r = &x`** lends `x` for the rest of the block, with no end at the last use; `x` is not
      named in the rest. Its lifetime has no name, so the calls in the rest take their lifetime
      from `r`'s type.
    - **A call `f(W)` of a function with a lifetime parameter** is applied to the lifetime its
      argument's type gives the parameter (the first match in the parameter type). This is in
      advance of `fn f<'a>` (`corpus/pending/fn-lifetime.bc`), whose declarations it does not
      provide.
    - **A div function over a borrow takes the owner.** Its type changes from
      `!(all 'a < b. P => Q)` to `!(P' => ref A * Q)`, with the owner handed back first, as a
      capability is. There is one form of it: a call with a borrow that is not lent from a place
      is not provided. Only one component of `P` may be borrowed at `'a`.
    - **Pipelines over a borrowed source are not rewritten.** Moving the owner into the source
      needs the pipeline to hand it back: adapters generic in the source's finishing value and
      residual, a `for` that binds the finishing value (#109), and a residual that hands back an
      owner with a destructor. A pipeline over owned sources, with a body that uses the borrow,
      is covered.
    - `|>` is not provided: draft 0 puts the piped value last (#17), and #109's adapters take the
      source first; the two are to be reconciled with it.
41. **Provisional (SPEC §14 Generators, #109, to be confirmed by the user).**
    - **`return e` is a generator's.** In the body of a `gen fn`, a statement `return e` that is
      not the head of a bind (`x <- return V; N` stays the core's) finishes the generator with
      `e` from any depth of its loops. In `fn` and `main` bodies, closures, blocks and borrow
      blocks, `return` is the core's `return`, as before: giving it Rust's meaning there would
      change what existing core-style bodies mean. It is printed `return return e`.
    - **`break` anywhere in a loop's body**, in a generator and in a `for` of a div body; after
      it, the iterator is closed and what follows the loop runs.
    - A `return` inside a `for` over an iterator made from a capability is rejected rather than
      closing the iterator to get the capability back: the returned value is computed inside
      the loop, where the capability is not in scope.
    - **`let r = for x in V { M }; N`** keeps a loop's value: what the iterator finishes with, or
      `e` after `break e`. `break e` is allowed only in such a loop, and a bare `break` there
      only when the value is `1`: Rust's `break e` is only in `loop`, whose value is always
      bound; here every `for` over a generator has a finishing value to keep. A loop over an
      iterator made from a capability keeps none (it hands the capability back). `while` has no
      value.
