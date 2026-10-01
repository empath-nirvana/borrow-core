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
24. **Recursion is an effect (revised; the original read "recursion is always structured, no
    general direct recursion").** A recursive function is written as ordinary self-calls, and the
    elaborator turns each self-reference into the `rec` operation, one `rec` per mutually recursive
    group. A driver runs it: `fix` (div, the default), fuel from a source's bound or `fuel(n)`
    (total), `deep` (pending frames on its own stack) or tabulation. Layers (`memo`, `fuel`)
    intercept `rec` and never drive it, and compose with `|>` (decision 50). Loops are the
    tail-position case of the same mechanism. Stack behaviour is a choice of driver, and deep
    non-tail recursion is a lowering matter (#123), not a reason to forbid recursion. Design:
    `docs/rec-effect/` (#133), effects stage S3b.
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
    surviving polarity shift (`docs/surface-cbpv.md`); decision 49 amends how the shift is made
    visible.
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
41. **Provisional (SPEC §15 Generators, #109, to be confirmed by the user).**
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
    - **A div call in a generator is a run of skips.** A call of a div function in direct style
      in a generator's body runs its loop inside the generator, one turn per observation, each a
      skip (`gen_bind_loop`); the alternative of running the loop to its end inside one
      observation would make that observation div, and a generator's observations total is what
      lets a consumer bound its work.
    - **`yield from g`** is Python's spelling (`from` is not a keyword: it is read after `yield`
      only). It delegates to a generator of the same element type, and its value is what the
      delegate finishes with. A lent capability `&mut c` comes back as the delegate's result
      (`c`, or `(c, x)`), as for a `for`.
    - **`gen { S }`** writes a generator in place (Rust's unstable `gen { }` blocks, Python's
      generator expressions). Its element type is inferred from its first `yield`; there is no
      annotation on the block, and one that yields nothing is rejected.
    - **A callback that yields yields to whoever runs the function it is passed to.** The
      function is specialized into a generator, and its call is a `yield from`: so `for_each(xs,
      { x -> yield f(x) })` inside a generator yields each `f(x)` from that generator. Outside a
      generator's body or a `gen { }` block such a call is rejected rather than made a generator
      value silently.
    - **`let c = for …` where `c` is a capability** the body hands back binds it as the
      capability the iterator hands back (at its end or when closed), so a generator stored in a
      variable can hand `stdin` back: `let stdin = for b in g { … }`.
    - **Generic generators, `gen fn f[A, …](…)`** (item 6): type parameters in brackets, as a
      core `def`'s, instantiated per call at the types of the arguments (read off them, or
      written `f[T, …](…)`), each instance a copy named `f__gN`. Only generators are generic,
      and an instance's types have no lifetimes. Alternative not taken: kernel polymorphism over
      value types, which §1's baseline does not have.
    - **A generator's residual is what it holds, `K`**, not a div body's `K ⊗ 1`: a generator
      that finishes with `stdin` hands back `stdin` when closed, so `stdout <- (nu_out (force
      g)).2` in place of `let (stdout, _) = …` (`corpus/gen-lazy.bc`), and `gen A K K` is a
      source that can be stopped.
    - **The adapter library** (`include adapters`, `lib/adapters.bc`): the names `map`, `filter`,
      `take`, `skip`, `enumerate`, `chain`, `flat_map`, `take_until`, `scan`, `zip`, `chunks`,
      `lines`, `batch`, `from_iter` (Rust's, with `take_until` for Rust's negated `take_while`
      and `batch` for a grouping by a function); argument order source first, then numbers,
      then functions. `chain`'s second source, `flat_map`'s inner ones and `zip`'s second are
      pure (`gen B 1 1`), so the whole finishes with the first source's value. `chunks` and
      `lines` build lists last element first.
    - **Stopping takes `U (gen A K K)`**: `take`, `take_until` and `zip` close their source, so
      its residual must be what it finishes with. A failing source (`gen A (1 + E) 1`) is
      rejected there rather than given a result type `K + R` (which the residual by name cannot
      hand back when `K = R = In`) or a function `R ⇒ K` argument (which the same rule defeats
      when the source holds a capability).
    - **A borrow block that yields is a delegation** (item 7): `borrow … { 'x, b -> S }` with a
      `yield` in `S`, in a generator's body, is `yield from borrow … { 'x, b -> gen { S } }`, and
      the existing typing rejects it (the block's result is boxed at `'x`, and a thunk has no
      outlives rule). The error is the checker's on the generated `boxed['x]`, in place of the
      elaborator's "off the spine".
42. **Provisional (SPEC §15, one state machine per body; #109 item 8; to be confirmed by the
    user).**
    - **One `unfold` per body, generators and div bodies alike.** The state's summands are the
      resumption points (the start of a generator, each `yield`'s continuation, each loop head,
      each `yield from`, each call of a div function in direct style); a loop's join (what
      follows it, reached from its end and its `break`s) is a function, not a summand.
    - **Calls or skips.** A move to a point calls its function when a later point is reached,
      or when the move is from a `yield`'s continuation; a move back to a loop's head from inside
      the loop is a skip. In a div body every move to a state is a skip, so each observation is
      one iteration or one observation of a callee, as with the delay bind, and `div_fuel`
      counts the same observations. The alternative of calling forward in a div body too (fewer
      observations) was not taken for that reason.
    - **When the code runs.** A div body runs its code up to its first state when called and
      returns the machine there (§14's "a call runs the function's code up to its first loop");
      a generator runs nothing, its first state holding the parameters. A `gen { }` block is
      `run` of its machine, whose first state holds what it captures.
    - **The nested binds stay as the fallback.** `gen_bind`, `gen_bind_loop` and `div_bind`
      elaborate a body the machine does not cover (a variable of undetermined type live at a
      point, a delegate's residual that is neither `()`, a lent capability nor the body's, a
      capability-less extern with no destructor used across a point) and report the errors of a
      body the elaboration rejects. The alternative, deleting them, would need every such error
      rebuilt in the machine; no accepted program of the corpus takes the fallback.
    - **The divergence library is emitted only when the elaborated program names it**, as the
      generator library already was: a program whose div bodies are machines has no `div_bind`.
    - **The I/O adapter tests are one file again**, `corpus/gen-adapters-io.bc` with six loops in
      `main`: it compiles in about a second (it took about 90 s with nested binds).
    - **Sugar pairs.** The core forms of `corpus/sugar/gen-from.bc` and `for-value.bc` are
      written by hand as machines; the other pairs whose elaboration changed have as core form
      the elaboration as `bcc desugar` prints it.

43. **Provisional (strings S1–S2, SPEC §8–§9, to be confirmed by the user).**
    - **`array_mut @a A`** is the core spelling of `[Mut @a A]`, beside `array_imm @a A`; the
      design's `slice 'a A` / `slice mut 'a A` are the surface names to come with the view
      library (S3–S4), as abbreviations.
    - **`slice_borrow_mut['x, @b, A, B]` / `slice_borrow_imm['x, @b, A, B]`** take one lifetime
      `@b` that both `A` and `B` must outlive; **`slice_get_mut[@a, A]`**,
      **`slice_len_mut[@a, A]`** are the `mut` counterparts of `array_get`/`array_size`.
    - **`u8`** is the byte type; **`b'c'`** the byte literal, read by the lexer as `u8[n]`;
      **`to_i32(b)`** and **`to_u8(i)`** (the prelude) the conversions, `extend8_u` and `wrap8`.
      An operator at `u8` works at `i32` on the widened operands and narrows an arithmetic
      result back, so `c - 32` at `u8` is `to_u8(to_i32(c) - 32)`. Alternatives not taken:
      `i32(b)`/`u8(i)` (the type keywords as functions), and no operators at `u8`.
    - **`count_fold[S] (f, n, i, s)`** is called directly for now; the total `for` over a count
      (`for i in range(n)`) that elaborates to it is typed elaboration's stage 9.
    - **`borrow imm a { 'x, v -> S }` and `borrow mut a { 'x, v -> S }` on an array** lend it as
      a family, with no cell, rather than rejecting a place that is not a cell. Alternative not
      taken: a new keyword (`borrow slice`), since the place's type already says which lend is
      meant, as `&x` does (typed elaboration §5.1).

44. **Provisional (strings S3, SPEC §9, to be confirmed by the user).**
    - **K3 is a machine step**, `split`, as K0 is (`count`): the design's term over the host's
      `le_u` and `sub` would be sound only at hosts whose subtraction subtracts. The
      alternative, a term over `idx` alone, cannot compute the length of the right part.
    - **`slice_split_imm[@a, A]`/`slice_split_mut[@a, A]`**, **`slice_empty_imm[@a, A]`/
      `slice_empty_mut[@a, A]`**, **`slice_replace_mut[@a, A]`**, **`slice_swap_mut[@a, A]`**
      are the core constants. The empty family is typed `[L]`, not the design's `![L]`: a
      constant at a dead context is already used at will.
    - **`array_mut @a A` has a destructor**, derived (`slice_get_mut` past every length, then
      `forget`), so it needs no new constant; the alternative, a `slice_forget_mut` constant, is
      a kernel change for the same effect.
    - **The library `lib/slice.bc`** (`include slice`) is generic in the element type, called
      with it written: `reverse[u8](v)`, `sort[i32](v, cmp_i32, 0)`. Its names:
      `len`/`len_mut`, `get`/`get_mut`, `at` (a copy through an `imm` view), `peek` (a copy
      through a `mut` view, by replace-and-restore), `set`, `replace`, `swap_at`, `discard_mut`,
      `empty`/`empty_mut`, `split_at`/`split_at_mut`, `split_first`/`split_first_mut`,
      `split_last`/`split_last_mut`, `read`, `reverse`, `fill`, `copy_from`, `find` (Rust's
      `position`), `contains`, `binary_search` (`inl` found, `inr` the insertion point), `eq`,
      `cmp`, `starts_with`, `ends_with`, `sort` (insertion, stable), `iter_imm`, `iter_mut`.
      `swap`, `iter` and `forget_mut` are keywords, hence `swap_at`, `iter_imm` and
      `discard_mut`.
    - **A comparison is an argument**: `find[u8](v, x, eq_u8)`, `sort[i32](v, cmp_i32, 0)`, with
      `eq_u8`, `cmp_u8`, `eq_i32`, `cmp_i32` in the library. There are no traits; the element
      functions are called directly in the loops (0-CFA finds one code), so this costs no
      dispatched call. An order answers `-1`, `0` or `1`.
    - **`sort` and `peek` take a filler** of the element type, held in a slot while its element
      is read through the `mut` view; K2′ (an `imm` reborrow of a `mut` family) would remove it.

45. **Provisional (surface generics, #130; to be confirmed by the user).**
    - **`fn f[A, …]<'a, …>(…)`**: type parameters in brackets, then lifetime parameters in
      angle brackets (draft 0 §2.5's order), each lifetime `top`-bounded unless written
      `'b < @`. Lifetimes are `all 'a < @.` around the function, outermost first. A `fn` with
      type parameters is a template (`Mark.template`, printed `fn def f[A] : … = …`).
    - **Monomorphization at the surface, not an opaque body.** A generic `fn`'s body is
      elaborated per instance, at the instance's types, as generic generators are (decision 41);
      the call's inference treats each type parameter as a placeholder to be matched. Alternative
      not taken: inferring the body once with `A` opaque and emitting a core `def f[A]` that the
      checker instantiates at each use. The elaborator's types have no opaque type: a free
      type variable standing for `A` is rejected inside a `μ` (`elabV` requires a `μ` closed),
      and what a body may do with an `A` (`*g`, which needs `A` persistent; an operator)
      is decided by its type, which there are no traits to state. A consequence: an error in a
      generic body is reported at the first use that instantiates it, and a generic `fn` never
      called is not elaborated (as a core `def f[A]` is checked only at its uses).
    - **Type arguments are inferred** by first-order matching of each parameter's type against
      its argument's, left to right, then of the result against the expected type; a closure
      whose parameter's type is a hole, and an injection, go last. A core `def f[A]` is covered
      too (`f(W)` becomes `f[T](W)`). A type argument that is not determined is an error at the
      call naming the parameter. Explicit `f[T, …](…)` stays.
    - **Lifetime arguments** are read off each parameter's own argument; written, they follow
      the type arguments, `f[T]['x](…)`. Two arguments that give one lifetime different
      lifetimes meet, and a borrow argument is shortened with `:>`; an argument that is not a
      borrow (a family `array_imm`) cannot be, and the call is rejected with a request to write
      the lifetime. A lend `&x` is at a function with one lifetime parameter only, as before.
    - **`unbang` is never written at a call**: a call of a `!` function with lifetime
      parameters is `(unbang f) ['x] …`, and `f['x]` of a `!` function inserts `unbang`.
    - **Loop steps are closures.** `lib/slice.bc`'s `count_fold` steps are `!{ … }` closures
      that capture nothing, in place of the generic `!(all 'a. !(…))` step `def`s: a `fn` with a
      lifetime parameter has type `!(all 'a. P => Q)`, and its instance at `'a` is not `!`. The
      closures erase to the same code, and the corpus counts are unchanged.
    - Not provided: bracket arguments of core constants (`array_get['a, A]`, `count_fold[S]`)
      are still written; inference of a type parameter from the arms of a `match` (a `let` with
      no expected type whose first arm determines it) is not done; instances are at types
      without lifetimes (decision 41).


46. **Provisional (strings S5, buffers and text, SPEC §11 and §17; to be confirmed by the user).**
    - **Bytes at `u8` in I/O.** `read_byte` answers `u8 + 1` and `write_byte` takes a `u8`; the
      byte list is `μX. 1 ⊕ (U8 ⊗ X)`. This withdraws decision 32's bytes as `I32`. A program
      that computes on a byte widens it (`to_i32(b)`); a literal operand takes the other
      operand's width, so `b == 10` and `47 < b` compare at `u8`.
    - **Two bulk externs**, `write_all` (an `imm` byte view to an output) and `read_into` (a
      `mut` byte view filled from an input, answering the count, short only at the end), each
      with two lifetime parameters (the capability's and the view's). The library lends a
      capability to them: `write_bytes(&mut stdout, v)`, `read_bytes(&mut stdin, v)`.
      Alternative not taken: calling the externs with `&mut stdout` directly, which a lend at a
      function with two lifetime parameters does not provide (decision 45).
    - **Type spellings**, abbreviations the parser expands: `buf A` is `array A * i32`,
      `string` is `buf u8`, `text 'a` and `text_mut 'a` are `array_imm 'a u8` and
      `array_mut 'a u8`, and `lit` is `i32 * !(i32 => u8)`. The design's `str 'a` is not used:
      `str` is already the stream former's short spelling (syntax-core §4). They are names
      only in type positions, so `text`, `string` and `buf` remain usable as variables.
    - **Literals.** `"…"` is a `lit`, UTF-8 for the characters written, with the escapes
      `\n`, `\t`, `\r`, `\0`, `\\`, `\"` and `\xNN`; `'c'` is a character, the `i32` scalar value
      (read as `i32[n]`, as `b'c'` is `u8[n]`). A lifetime `'x` is never followed by `'`, which
      tells them apart.
    - **Allocation**: `box buf[A](cap)`, `box string(cap)` and `box array(n, f)` are
      `buf_new[A](cap)`, `string_new(cap)` and `array_tab(n, f)`, read by the parser. Growth
      inside `push` allocates without a `box` (the design's Q2, left as Rust has it).
    - **The filler** of a buffer's unused slots is chosen by type: `filler[A]` elaborates to
      `0`, the empty view, an empty array (which allocates nothing), or componentwise at `*`
      and `+`. A type with none (a cell, a capability) cannot be buffered, as the design says of
      stage A.
    - **Borrow blocks** on a buffer lend its initialised prefix (the array lent as a family, cut
      at the length); on a literal, its bytes. A borrow block hands back, beside its result, the
      enclosing `let mut` variables it assigns, the places it lends that it does not bind, and
      the standard capabilities it uses, as `for` does: `borrow imm line { v ->
      write_str(&mut stdout, v) }` needs no `(stdout, …)` in its result. Programs that returned
      the capability themselves are rewritten (`lend-mut`, `borrow-across-loop`,
      `scope-data-effects`, two rejects).
    - **Library names** (`lib/buf.bc`, `lib/text.bc`, `lib/textio.bc`): `buf_new`, `push`,
      `pop`, `take`, `reserve`, `truncate`, `clear`, `len_of`, `cap_of`, `grow`,
      `buf_of_array`, `array_tab`; `string_new`, `clear_str` (length 0 without dropping bytes),
      `push_str`, `push_lit`, `push_byte`, `push_char`, `push_dec`, `to_string`,
      `string_of_lit`, `lit_len`, `eq_lit`, `str_from_utf8`, `from_utf8`, `utf8_error`,
      `seq_len`, `char_at`, `count_chars`, `split_char`, `chars`, `split_once`, `next_line`,
      `lines`, `fold_lines`, `is_space`, `skip_while`, `rskip_while`, `trim`, `find_str`,
      `add_checked`, `mul_checked`, `parse_i32`, `view_at`, `swap_views`, `sort_views`,
      `make_ascii_uppercase`, `make_ascii_lowercase`; `write_str`, `write_string`, `write_lit`,
      `read_all`. `lib/textio.bc` is its own module because it names `Out` and `In`, which are
      in scope only with the I/O library. A module includes the modules it uses.
    - **Errors are sums** (provisional until the error effect, #18): `parse_i32` answers
      `i32 + (1 + (u8 + 1))` (no digits, a byte that is not a digit, overflow); the decoders and
      validators answer the index of the first bad byte.
    - **Total loops over text are `count_fold`s**, bounded by the view's length (plus one);
      `fold_lines` folds a state over the lines, each a sub-view. `lines` and `chars` are codata
      over the rest of the view, for S4's total `for`. No mechanism infers finiteness from a
      name.
    - **A template is instantiated at a type with lifetimes** (a buffer of views): the instance
      takes a lifetime parameter of its own for each, `!(all 'io_q0 < top. …)`, and a call
      passes the call's lifetimes. This revises decision 45's "instances are at types without
      lifetimes".
    - **Literal lowering.** A literal's tabulator is recognised by its shape and becomes one
      shared code over the address and length of its bytes in read-only data; a literal view is
      recognised by its erased shape (the array lent to a callback that first copies the family,
      then dropped) and points into the data. The recognition is of the terms the elaborator
      emits; it is tested on the corpus, not proved (design §5.7).

47. **The `for` loop (strings stage S4, revised; SPEC §16). The user's decisions, and the
    spellings, which are provisional.**
    - **Desugaring: Rust's, pull.** `for x in y { M }` turns `y` into an iterator by `y`'s
      type (Rust's `IntoIterator`) and calls its `next` at each step, with `break`,
      `continue` and `return`. Push stays library functions (`count_fold`, the folds) with no
      syntax. Not taken: PR #132's table of library names with a bound each (a finite source
      recognised by its name, and a loop run for a bound nothing proved), and the push
      recommendation of `docs/iteration-design.md` §10.
    - **Totality from data.** A source whose type holds the data it came from is sized, and the
      loop is K0′, `count_try`, over the length of that data, computed when the loop starts: a
      count `a..b` (`b − a`), a view (`array_imm`, `array_mut`: its length), `&a`/`&mut a` of an
      owned array (lent as its view around the loop), an owned array of a persistent element
      (copied), and a sized iterator `sized D S A` (`len(D)`). No bound is a number the program
      gives: a free number would truncate the loop silently. Any other source (a generator, an
      iterator, the input) is a drain, and div. `total` rejects a drain (`corpus/reject/
      for-free-bound.bc`: `take(g, 10)` of a generator is a generator).
    - **K0′ sits beside K0.** `count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)`
      is a machine step, as `count` is (every theorem holds at every host); `count_fold`
      stays. Replacing `count_fold` by it (decision 20) is not done: a loop that never stops
      would test an exit it does not have.
    - **Exits live in the step's result**, not in handlers: the end of the body and `continue`
      go on (`inl`), `break e` and `return e` leave (`inr`) with the threaded variables and
      the way out. `return e` in a loop's body returns from the function (in a surface `fn` or
      `main ->`; a core `def`'s `return V` is the core's), through every counted loop around
      it; the body's loop is moved onto the function's spine first. Effects in a body are the
      function's: a capability the body uses is threaded through the loop and handed back.
    - **The loop's value.** A source that can end: `for … { … break v … } else { d }`, the
      value `v` or `d` (Zig's `else`; `break v` without `else` is rejected over a sized
      source). A source that cannot end (a generator finishing with `0`, whose body is a
      `loop { … }`): the loop's value is `break`'s alone, and with no `break` its type is `0`
      and `bcc check` reports the code after it as unreachable. A `for` with no value is `()`.
      A drain keeps its value (what the source finishes with, or `break e`); `else` is
      allowed on it too.
    - **No syntax at the loop for a drain.** Precision is in types and reports: `bcc check`
      prints, per loop, `total, bounded by len(…)` or `div: its source … is unbounded (a
      drain)`, and unreachable code after a loop that never ends.
    - **Sized iterators** are values of `sized D S A = D * (S * !(D * S => (D * S) * (A + (1 +
      1))))` (`lib/iters.bc`, `include iters`): the data, the iterator's own state, and a step
      answering an element, a skip or the end. `elems`, `elems_mut`, `copied`, `map`,
      `filter`, `take`, `enumerate`, `zip`. Each step takes at most one element of the data,
      so `len(D)` steps see every element; `zip`'s data is the pair and its bound the sum
      (a step may pull only one side, when the other skipped; its elements are at most the
      shorter side's). Names shared with the pull adapters (`map`, …) are chosen by the
      argument's type.
    - **Spellings (provisional):** `a..b`; `continue`; `for … else { d }`; `loop { … }` (a
      `while` that never fails); `sized D S A`; `elems`/`elems_mut`/`copied`; the module
      `iters` (`iter` and `sized` are keywords).
    - **Out of scope:** `for` over `μ` data (lists); handlers and layers (#18); push lowering.
48. **Effects: the scoping of #18 (`docs/effects-scoping.md`, #151). The user's decisions.**
    - **Handlers are defined by elaboration** into existing core terms: a capability lent by
      `withbor`, a handler as state plus `!` clauses, resume-once as a call, abort as a sum exit,
      suspension as `ν` codata, finalisation as the §12 destructors. Effect rows never enter the
      core, and effect safety follows from the Fundamental Property.
    - **Acceptance** is per-class handler laws on the elaboration schemas, cost-parity counts and
      per-handler lowering reports (#126), in place of "an erasure theorem", which elaboration
      makes true by definition.
    - **Staging:**
      - S1: answering operations and `Fail`, erased, rows inferred;
      - S2: named capabilities and platform bundles;
      - S3: `rec`, drivers, layers and `|>`;
      - S4: `Yield`, projections and stored callbacks;
      - S5: with #52, suspension with input and cancellation (K1–K3).
    - **Syntax (provisional):** Effekt's semantics with a `with` clause. Capabilities are implicit
      and lexical, and a name is required only when two instances are in scope. The cost
      vocabulary is Koka's (`fun`, `ctl`, `final ctl`), plus `finally`.
49. **The governing rule's visible shift, amended (revises decision 26 and `docs/surface-cbpv.md`
    §1).** There is no `perform` or `suspend` token at a call site. A suspending operation is made
    visible by the function's inferred effect row and by `bcc check`'s report per call site
    (#126). The continuation stays visible in the handler, as an explicit linear `k`. Sugar still
    may not hide a surviving shift from the types or the reports.
50. **`|>` (one-way door).** `e |> f(a, …)` is `f(e, a, …)`: the piped value goes FIRST. When
    `f`'s first parameter is a computation, `e` is suspended (thunked), which is type-directed as
    decision 26 allows. A chain is applied innermost first, and its order is semantics. This
    settles #17 and #59; draft 0's piped-last rule is withdrawn.
51. **Provisional (effects S1a, SPEC §18, #152; to be confirmed by the user).**
    - **Spellings**: `effect E { fn op(x: A) -> B; … }`; `handler h(s: S) for E { op(x) -> e;
      op(x) -> { M }; … }`, the state a `let mut` variable of each clause and the clause's value
      the answer; `with h(e) { M }` for a state made at the block and dropped after it, and
      `with h(&mut c) { M }` for a state lent from a cell, which holds the final state. An
      operation is called as a function; its name is its own.
    - **A clause is a function over the lent state**, `h__op(c: mut 'l S, x) -> mut 'l S * B`,
      whose body is `modify` (`withswap`) of the state; a `with` is a `borrow mut` of the
      state's cell. So a handled program is the capability-passing program a user would write
      by hand, and its counts are that program's (`corpus/effects-map.bc`,
      `effects-map-hand.bc`).
    - **A function with a row is copied per handler** (`f__h`), as a generic function is per
      instance: no dispatch, and a function never called under a handler is not elaborated.
      The copy takes the capabilities first and hands them back first.
    - **One instance per effect** in scope; the innermost `with` of an effect handles it. Names
      are S2 (#155). Effects take no type parameters yet; `Fail[E]` (S1b) is the first that
      needs one.
    - **Not in S1a**: written rows; effectful callbacks (#161); an operation inside a clause;
      a lend in the arguments of an effectful call; effectful functions whose result is a loop
      or a generator.
52. **Provisional (effects S1b, SPEC §18, #153; to be confirmed by the user).**
    - **Spellings**: `raise(e)`; `try { M }` answering `inl v` or `inr e`; `catch { M } { e -> N }`
      answering `N` on an error; `map_err { M } { e -> N }` raising `N`. `try` is the primary form
      (the handler to a sum); `catch` and `map_err` are a branch on it. There is no `?`: a call of
      a function that raises propagates by itself.
    - **Written rows**: `fn f(…) -> T with E₁, Fail[X] = …`, a promise checked against the inferred
      row. `Fail[X]` gives the error type; a function that raises directly writes it, and one that
      only calls raising functions gets it from them. Rows stay otherwise unwritten.
    - **`Fail` is a computation type, not a capability**: a function that raises answers `T + X`,
      a call of it is a branch, and an abort in a loop's body is the loop's exit. `try` of a call
      in tail position is the call's own sum. So a fallible program is the sum program a user
      would write by hand (`corpus/effects-fold.bc`, `effects-fold-sum.bc`).
    - **An abort cannot abandon a value with no destructor**; the checker's error names the
      abort (SPEC §12's class 3). The residual form, handing it to the handler, is later (E9).
    - **Errors are raised** in the library: decision 46's "errors are sums (provisional until the
      error effect)" is withdrawn for errors; a search that finds nothing still answers a sum.
    - **K4 is open**: a `raise` in a kernel fold's algebra is rejected where the algebra is passed.
53. **Provisional (effects S1c, SPEC §18, #154; to be confirmed by the user).**
    - **Acceptance of #18** is the per-class laws on the elaborated terms (`op_tail`, `op_answer`,
      `handle_fold` for answering handlers; `abort_passes`, `return_resumes`, `loop_abort` for
      `Fail`), the counts against the programs written by hand, and the reports; no erasure
      theorem.
    - **Report lines** (`bcc check`, #126): `effect`, `row`, `lowering`, `call`, each with its
      position. A lowering shape is named by #18's table (call, branch; state machine and
      dispatch later) with Koka's class in brackets (`fun`, `final ctl`). The spelling of the
      lines is provisional; `corpus/reports/` pins them.
54. **Tentative: no traits (the user's working decision, open to change; revisit when a concrete case breaks or a better design appears).**
    - **Iteration** (generators, coroutines, async) is one mechanism: `Yield`/`await`-style operations with continuation qualifiers, handled lexically (§19, #186). There is no iterator interface; `for` handles `Yield`; an implicit `for x in &v` is optional later sugar.
    - **What type classes would do otherwise:**
      - structural defaults (`eq`, `hash`, `cmp`, `display`, `clone`, `encode`) as polytypic functions over a type's structure (derive);
      - explicit function arguments for custom semantics (the `lib/slice.bc` convention);
      - lexical handlers for scoped choices;
      - invariant-bearing structures (hash maps, sorted sets) that capture their provider at construction, so no global coherence rule is needed.
    - **Operators** perform a `Num[T]` effect. The ambient, outermost platform handler provides the primitive widths and erases to the machine instruction; this is the host parameter `∀ ℍ, [HostIs ℍ]` made explicit. User numeric types bring a handler into scope.
    - **Receiverless functions** (`default`, `parse`) are plain named functions.
    - **Watch-point:** row inference choosing `Num[T]` from operand types (untyped integer literals). The interfaces research (`docs/prior-art-interfaces.md`, #169) stays as background.
55. **Provisional (surface effects on the kernel, #188 stage 1, SPEC §18–§19; the user's spelling guidance of 2026-10-01, to be settled after rewriting a sample of the corpus).**
    - **An effect is a signature; a handler is a value implementing it.** `effect E[T, …] { fn op(x: A) -> B; ctl op(x: A) -> B; … }`: `fn` is answering, `ctl` control. An effect has one kind of operation. `never` is the empty type `0`; a `ctl` operation answering `never` is abortive.
    - **The qualifier is on the operation**: `ctl` is affine, `linear ctl` linear, `multi ctl` unrestricted. Open: whether `ctl` is inferred from a clause's `k`, and whether the qualifier belongs on the handler.
    - **Handlers**: `handler h(mut s: S): E = { op(x) = e; … }` for an answering effect (its state a `mut` parameter); `handler h[T, …](p: A, …): E[…], A -> R with E₂[…] = { return(x) = M; op(x, …, k) = N; … }` for a control effect, naming the type `A` of the body it handles and its answer `R`, with the row its clauses perform after `with`. An abortive operation's clause takes no `k`. Open: the form of the handler's type annotation.
    - **A clause is `!` code** (§19's `[handle]`), so a control handler's parameters are `!` values: `default` takes `!(1 => A)`, written `with default(!{ u -> 0 }) { … }`. Alternative not taken: a state-passing answer type for a non-`!` parameter (§19 *Open*).
    - **`with h[A, …](e, …) { M }`** installs a handler; its type arguments are written only when the body does not determine them. A control `with` answers the handler's answer alone; an answering `with h(&mut c)` rebinds `c`.
    - **Errors are `Fail[E]` in `lib/fail.bc`**, `ctl raise(e: E) -> never`, with `to_result`, `default` and `map_err` (`include fail`). `retry` waits for functions over computations (#161). An error holds nothing owned (§19's `[raise]`): `from_utf8` raises the index and drops the buffer.
    - **Static names are per `with` site**, numbered from 1 in the order the elaboration meets them; a function performing a control effect is copied per site, `f__n3`.
    - **The textual core**: `F[n.i q A ~> B, …] T`, `perform[n.i] V`, `abort[n.i] V`, `handle_with[n](hr, hc) M`, `x <- M unwind (D); N`, and `withbor1u`, `withbor2u`, `withbor3u`, `withloadu`, `slice_borrow_mut_u`, `slice_borrow_imm_u` with the callback's row as a bracket argument (`handle` is a name in the corpus).
    - **Drop glue is the checker's**, as §12's destructors are: a binding whose head may abort gets a `[then]` finaliser of the destructors of what the rest uses.
    - Not taken from the guidance yet: `run() |> to_result |> stderr_log` (`|>` at a computation parameter waits for #161) and named instances `with a: Kube = …` (#155).
