# Functions over effectful computations: effect polymorphism and higher-order effects (#161)

Design for #161, after §19 (kernel effects) and stages 1–2 of #188 (surface effects). Nothing here
is built. Each claim is marked as one of:

- **established**: a Lean declaration on `main`, named after it was found by `grep`;
- **by inspection**: read off a definition, with no theorem behind it;
- **hypothesis**: argued here, not machine-checked.

## 0. Summary

- **Mechanism.** Effect polymorphism stays at the surface. A function that takes a computation is
  copied per call, as functions with a row already are (`f__n3`, SPEC §18) and as generic functions
  are (decision 45). The kernel stays first-order in rows: no row variables, no new `CTy` former,
  no relation change, no new `CDerives` rule. Of the three options in §4, this is Option 2.
- **Who serves an effect.** A computation parameter's row is split in two (Effekt's reading, and
  Zhang & Myers' tunneling):
  - the **provided** row is written in the parameter's type. The callee serves it: an operation
    of a provided effect goes to the site in scope at the call of the parameter inside the
    callee;
  - the **tunneled** row is everything else the argument performs. It is never written, and it is
    resolved where the argument was written.
- **No new dispatch.** A callback that is passed and not stored is known at every call once the
  program is specialised. Its body goes into the callee's copy, and its captures become
  parameters of the copy, threaded as capabilities already are. This adds no allocation and no
  dispatched call (§10).
- **Accidental handling.** Static per-site names already prevent it in every program whose copy
  graph is acyclic, which is every program today. It needs one added check, **site freshness**: a
  site's name occurs free in no type outside the site. This is Zhang & Myers' `[t-down]` side
  condition, strengthened to the site's context because our names are static, not generative.
  Where it fails is shown precisely in §6: recursion through a site whose callback tunnels that
  same site. That case is rejected, and is Open behind generative names (T2, #173).
- **Stored callbacks** are first class. Their rules:
  - a stored callback is a `!` thunk, boxed at the lifetime of the borrows it captures,
    `[@c] !U(A ⊸ F_Σ B)`;
  - it never captures a stateful capability (`not_sharedCapture`);
  - the stateful capabilities it uses are passed to it by whoever calls it;
  - its control effects are **ports**: static names fixed by the stored type, served by the site
    that the call of the stored callback lies under.
- **Higher-order effects** (`catch`, `local`, `timeout(d, M)`) are not needed as a kernel
  construct for targets 1–5. Each is a function over a passed computation that installs ordinary
  handlers. This is the elaboration of Bach Poulsen & van der Rest's hefty algebras, fixed per
  call site.
- **Proof cost.**
  - The kernel needs nothing for targets 1–3 and 5.
  - Target 4 needs promotion widened (#9, T6), and is a box of a `!` thunk, which `boxI` already
    types.
  - The obligations are a uniqueness lemma for resolution by name (§9.2, small), and optionally
    the freshness side condition on `[handle]`. Restricting the rule leaves `handle_compatC`
    unchanged.
- **Open, needing the user's decision:** §11.

## 1. The problem, in the kernel's terms

### 1.1 Vocabulary

| term | meaning |
|---|---|
| **computation parameter** | a parameter whose argument is code to run, not a value: an argument of computation type `A ⊸ F_Σ B` in CBPV, passed as a thunk `U(A ⊸ F_Σ B)` |
| **provided row** `P` | the effects the callee serves for the argument; written in the parameter's type |
| **tunneled row** `T` | the effects the argument performs that the callee does not serve; resolved where the argument was written; never written |
| **second-class callback** | a computation argument that is called or passed on, and never stored, returned or captured by a stored closure |
| **stored callback** | a computation kept in data, a cell or a returned value, and run later |
| **site** | a control `with`: the kernel's `hnd (n, H) e` with a static name `n` (SPEC §19) |

Throughout, `n`, `m` and `p` are static names, as in SPEC §19. `F_{n:E} A` abbreviates the row of
`E`'s operations at the name `n` (`Row.ofEff`).

### 1.2 The five targets

Each target is given as the kernel term the design must produce, and then as a surface sketch.
**The sketches are provisional spellings (decisions 51, 55 and 56) and are not the design.**
`(…) -> B with E` stands for a computation parameter whose provided row is `E`; the spelling is
not proposed here.

**Target 1: `retry`.** Run a computation, and run it again if it raises.

- **Kernel.** For a call site whose argument `c` captures a lend of `conn` and performs `Fail[E]`,
  `retry`'s copy is a counted loop (§16's `count_try`). Each turn is an unwinding reborrow of the
  capture, around a site of retry's own:

      retry__k : !U(I32 ⊗ Mut 'l Conn ⊸ F_{m:Fail[E]} (Mut 'l Conn ⊗ A))
      turn     = withbor3U conn (Λ'x. λc. hnd (n, H_to_result) (c_body__n c))     n fresh

  - The body `c_body__n` is `c`'s code, with its `raise` at the name `n`.
  - The last attempt runs outside any site of retry's own, so its `raise` is at `m`, the
    caller's name.
  - The kernel can already express this. `withbor3U_compatX` gives the unwind of the lend, and
    the attempt is `reborrowRaise`'s shape (`Core/EffPrograms.lean`) in a loop.
  - The kernel's own route takes the computation as `!U(1 ⊸ F_{n:Fail} A)`. That requires
    persistent captures, which a lend of `conn` is not. The copy instead lends the capture anew
    on each attempt, and an abort ends the lend.
- **Surface sketch:**

      fn retry[A, E](tries: i32, body: () -> A with Fail[E]) -> A with Fail[E] =
        for _ in 1..tries { match body() |> to_result { inl a -> return a | inr _ -> () } };
        body()

**Target 2: `run() |> to_result`.** A handler applied to a computation.

- **Kernel:** `hnd (n, H_to_result) (run__n ())`.
- **Surface sketch:** `M |> h(args)` is `with h(args) { M }`. Decision 50 puts the piped value
  first and thunks it when the parameter is a computation. A handler's first parameter is its
  body, by definition. As a function over a passed computation:

      fn report[A, E](body: () -> A with Fail[E]) -> A + E = body() |> to_result

**Target 3: callbacks that yield** (`corpus/pending/yield-callback.bc`).

- **Kernel.** `for_each`'s copy for `tens`'s closure is a div body at `tens`'s row, which observes
  the stored generator `it`. The closure's `yield` is at `tens`'s site name `n_t`, because
  `Yield` is tunneled: `for_each` does not provide it. The copy is the term the hand-written
  `for x in it { yield(x * 10) }` elaborates to (`Loop_{n_t:Yield}`, SPEC §15, *A generator's
  body*).
- **Surface sketch.** The pending program with the `!` dropped from `f`'s type:
  `fn for_each(it: U (pull i32 1 1), f: (i32) -> 1) -> 1`.

**Target 4: stored callbacks.** An event registry, and a manager holding several controllers'
reconcile functions.

- **Kernel.** A list whose element type is

      H = [@c] !U(∀'l. Mut 'l S_log ⊗ Event ⊸ F_{p:Fail[Err]} (Mut 'l S_log ⊗ 1))

  - `p` is a **port**: a static name fixed by the type `H`.
  - The dispatcher calls each element under a site named `p`: `hnd (p, H_to_result) (force h [] (c, ev))`.
  - It lends its own `Log` capability `c` to each call.
- **Surface sketch:**

      type Handler = (Event) -> 1 with Log, Fail[Err]      -- stored: a port for Fail, Log passed in
      fn dispatch(hs: &List[Handler], ev: Event) -> 1 with Log =
        for h in hs { match h(ev) |> to_result { inl _ -> () | inr e -> log_err(e) } }

**Target 5: the north-star chain.**

    controller(Foo, reconcile) |> timeout(30.s) |> retry(5) |> log(json(&mut stderr)) |> kube(&mut client)

- **Reading the chain.**
  - Innermost first (decision 50): `kube(log(retry(timeout(controller))))`.
  - `kube` and `log` are answering handlers: borrow blocks lending their state (SPEC §18).
  - `retry` provides `Fail` to its body.
  - `timeout` provides the suspension effect (`Wait`, #52) to its body. At each `wait` it
    compares the clock with its deadline, and either forwards the `wait` outward and resumes, or
    cancels the continuation and raises `Timeout`.
  - `reconcile`'s `Kube` and `Log` tunnel through `timeout` and `retry`, as capabilities threaded
    through their copies. Its `Fail` goes to `retry`. Its `wait` goes to `timeout`, which forwards
    it to the scheduler outside.
- **Kernel.**

      withbor (kube state) (Λ'k. λck. withbor (log state) (Λ'g. λcg.
        retry__k5 (ck, cg) …                      -- count_try; each turn: withbor3U of ck, cg
          hnd (n_r, H_to_result)                  -- retry's site, Fail
            (timeout__k (ck, cg) …                -- hnd (n_t, H_timeout): Wait, forwarding to m_w
               controller__k (ck, cg) …)))        -- reconcile's body inlined, Kube/Log calls on ck/cg

- **Status.**
  - Nothing in this term is special to any effect.
  - Each layer is a copy, made by the same rule (§5).
  - **Hypothesis:** the term types with today's rules, given `Wait` (#52) and a counted loop whose
    body performs a resuming operation (deferred in #220 to stage 3).

## 2. What exists

**Established (kernel, SPEC §19):**

- `CTy.eff n i q A B C` stacks one operation of a static name over a computation type, and
  `CTy.effOf Σ R` is `F_Σ R`. Names are `UInt32` literals in types.
- `effHandle` asks `n ≠ 0` and `∀ o ∈ S, o.n ≠ n`: the site's name is absent from the outer row.
  It does not ask anything of `n` in the types of the context, the result or the outer row.
- `Head.hop` handles `perform (n, …)` at the nearest `hnd (n, …)`, with `K.HasHnd n = false` for
  the frames between.
- `effSub` (`RowLe`) is row subsumption. `effLet`, `effThen` and `effPerform`/`effRaise` are as in
  SPEC §19.
- Their compatibility lemmas: `sub_compatC`, `perform_compatC`, `raise_compatC`, `let_compatC`,
  `then_compatC` and `handle_compatC` (from `ewp_handle`).
- `fundamentalC` and `adequacyD` cover all of them.
- The relation at `F_Σ A` is `ewpTS` at the table `Row.tab Σ δ` (`cC_effOf`). An `OpTab` is a
  semantic object, `UInt32 → UInt32 → Option OpEnt`.
- The unwinding borrows, `withbor1U`…`withbor3U` (`withbor2U_compatX`, `withbor3U_compatX`), take a
  callback whose row is `Row.Unwind`: abortive operations only.
- `boxI` boxes any value, a thunk included, whose context outlives the box's lifetime
  (`boxI_compatC`). `bangThunkV` promotes over `Persistent Γ`, which is `!` slots only.

**Established (experiments):**

- **`not_sharedCapture`**: two closures capturing one stateful capability are refused
  (`twoBlocks_refused`). Several blocks that receive the capability at each call are typed and
  safe (`x_sharedUnit`, `sharedUnit_safe`).
- **`lam_bang_persistent`, `multiShot_ref_refused`**: a `!` continuation captures only persistent
  values.
- **`box_lolli_outlives_iff`, `crossProg`**: a closure boxed at `@c` outlives `@a` exactly when
  `@c ⊐ @a`. A boxed continuation that captures a borrow crosses an inner scope.
- **`escape_refused`**: a handler's own capability cannot leave its `['x]`.

**Established (surface, SPEC §18 and §15):**

- `freshSite` numbers a site each time a `with` is elaborated, and `copyOf` elaborates the body
  once per copy. So **two copies of one function have distinct site names** (by inspection of
  `Frontend/Elab/Effects.lean`).
- `copyFor` keys a copy by the handlers and sites serving its row (`copyName`).
- §14's specialisation copies a function at a callback's computation type. It covers divergence
  only, and only parameter types.
- An operation inside a closure that is not run in place is rejected, citing #161.
- `|>` is not parsed yet (decision 50 settles its meaning).

## 3. Survey

| system | polymorphism | who handles a callback's effect | stored effectful functions | compiles to | read |
|---|---|---|---|---|---|
| **Koka** | row variables, inferred (`(a) -> e b`) | dynamic: the nearest handler of the operation's effect; `mask` and named handlers to choose | first class, the row in the type | evidence passing: a vector of handlers passed to each call, searched by constant offset; tail-resumptive operations in place (Xie et al. ICFP '20; Xie & Leijen ICFP '21) | effects-scoping §4.1; the ICFP '20 abstract |
| **Effekt / System C** | none written: "polymorphism implicitly arises from the calling context" | lexical: capabilities passed; a block parameter's effects are provided by the callee, the rest captured | blocks second class; `box` makes a first-class value whose type records its capture set (OOPSLA '22) | capability-passing style, iterated CPS, zero-cost when handlers are statically known (Schuster et al. ICFP '20); regions (OOPSLA '23) | effects-scoping §4.2; `experiments/HandlersAsBorrows` §5 |
| **Frank** | an ambient ability propagated inwards, no variables in source | positional instances (the rightmost); **adaptors** rewire them (Convent et al. JFP '20) | first class | interpreter | effects-scoping §4.4; JFP '20 abstract |
| **Links** | row polymorphism with presence types | dynamic, by operation name | first class | CEK machine, generalised continuations (Hillerström et al. JFP '20) | effects-scoping §4.5 |
| **Zhang & Myers** (POPL '19) | explicit effect variables, handler polymorphism | **tunneling**: "Algebraic effects can be handled only by handlers that are statically aware of them; otherwise, effects tunnel through handlers" | first class (effect-polymorphic data structures) | not studied ("passing (static) capability labels") | the paper, §§1, 3, 4 |
| **Biernacki et al.** (POPL '20) | effect variables bound by lexically scoped handlers | lexical by day, run-time labels by night | first class | not studied | the abstract |
| **Tang et al.**, *Soundly Handling Linearity* (POPL '24) | rows with control-flow linearity kinds | dynamic | first class | — | `experiments/HandlersControl` §3 |
| **Affect** (POPL '25) | — | dynamic | one-shot continuations affine, stored in cells | — | `experiments/HandlersControl` §3 |
| **Modal effect types** (Tang et al. OOPSLA '25) | effects tracked by modalities, decoupled from functions; rows and capabilities encoded into it | either | either | — | the abstract |
| **Scoped / higher-order effects** (Wu, Schrijvers & Hinze, Haskell '14; Bach Poulsen & van der Rest POPL '23; Lindley et al. ESOP '24) | — | operations that take computations (`catch`, `local`); hefty algebras *elaborate* them into algebraic operations and handlers | — | — | §7 |

**What we take.**

- **Effekt's split.** A parameter's written effects are served by the callee; the rest are served
  where the argument was written. It is Zhang & Myers' tunneling, and the only reading under which
  `retry` cannot catch an unrelated `Fail`.
- **Effekt's premise for zero cost.** Handlers are statically known after specialisation. That is
  our whole-program assumption (decision 45).
- **Zhang & Myers' escape condition** on the binder of a handler's label: "the label ℓ must not
  occur free in the result type T and effects e". It is strengthened in §5.3, because our names
  are static.
- **Frank's adaptors**, as the general form of a port relabelling (§5.6, Open).
- **Hefty algebras' elaboration**, as the reading of `timeout` and `catch` (§7).

**What we do not take, and why.**

- **Koka's dynamic resolution.** Accidental handling (Zhang & Myers §2).
- **Koka's run-time evidence vector.** A run-time search or index, against decision 25 and the
  zero-cost target.
- **Row variables in the kernel.** §4.
- **Generative labels** (Biernacki et al., Zhang & Myers). A label must never meet a stale copy of
  itself, which needs a continuation confined to its handler's scope (SPEC §19, *Why not
  generative names*). That is T2 (#173).

## 4. The polymorphism mechanism: three options

### Option 1: row variables in kernel types

`retry : ∀ε#{n}. !U(I32 ⊗ U(1 ⊸ F_{n:Fail[E] | ε} A) ⊸ F_{m:Fail[E] | ε} A)`

**What changes.**

- **`CTy` gains two formers**: a row-variable tail, and a binder `∀ε#N. C` with a lacks set `N`.
  - The lacks set is not optional. `effHandle`'s `∀ o ∈ S, o.n ≠ n` becomes `n ∉ N`, since an
    instantiation of `ε` containing `n` would put `n` in the outer row.
  - Lacks constraints are Rémy's and Links' presence types.
  - Each `CTy` former costs about 20 match arms across `Core/` (CLAUDE.md, *Growth discipline*):
    substitution, free lifetimes, `EffFree`, `EffLeaf`, positivity for `ν`, `Drop`, `Persistent`.
- **The relation gains a row environment** `η : Nat → OpTab`. `cC (∀ε#N. C) δ η e ≜ ∀ T, T.Mono →
  (∀ n ∈ N, T n = none) → cC C δ (η[ε ↦ T]) e`.
  - The `ewp` lemmas are already generic in the table (`ewp_mono`, `ewp_sub`, `ewp_handle`), so the
    semantics accommodates this.
  - The cost is the signature: every `cC`/`vC`/`SemV` statement in `Core/` gains `η`.
- **`CDerives` gains a context of row variables.** Decision 19 forbids this ("No new index on
  `CDerives`"). The alternative, putting row variables in `LifeCtx`, touches every use of `Δ`.
- **New lemmas:**
  - compatibility of `∀ε`-I and `∀ε`-E;
  - a **semantic substitution lemma**, `cC (C[Σ/ε]) δ η ↔ cC C δ (η[ε ↦ Row.tab Σ δ])`, by
    induction over every `VTy` and `CTy` former;
  - positivity of `Loop_ε` at an abstract row (`loopEffBody_nuOk` today assumes closed operation
    types).
- **The backend.** One body would serve callers whose names differ. Either names become run-time
  values (evidence; Option 3 at run time), or the backend monomorphises anyway, and Option 1 then
  buys only checking a function once.

**Cost.** Proof burden: the largest, two formers plus the relation's signature, and it breaks
decision 19. Run-time: a dispatch or search unless monomorphised. Compile time: one body per
function. It buys separate compilation, which nothing in the project asks for yet.

### Option 2: monomorphisation over static names (recommended)

- **The kernel stays first-order in rows.** A function over a computation is a template, copied
  per call.
- **The copy key:**
  - the function;
  - for each computation argument, its code and what serves its tunneled row at the call;
  - what serves the function's own row (as `copyFor` does now).
- **The argument's code goes into the copy** (§5.2).

**Cost.**

- *Proof burden:* none in the kernel. Every copy is ordinary core, checked by the unchanged
  checker. The obligations are the two lemmas of §9.2, and the laws of §9.3 if wanted.
- *Run-time:* none added. A known callback is inlined code, and its captures are parameters.
- *Compile time and code size:* one copy per (function, callback, assignment), the cost of Rust's
  generics over closures (`impl Fn` monomorphises per closure type). It is the same cost and
  measurement as effects-scoping §7.9 (a code-size column in the counts).
- *Limits:*
  - separate compilation and code chosen at run time (none planned);
  - polymorphic recursion over names, rejected (§6.3);
  - heterogeneous stored callbacks, which take one type by `effSub` (§5.6).

### Option 3: evidence passing

- **Answering effects** already are evidence passing. The capability is the handler's state lent
  as `Mut 'l S`, beside its clause, which the copy knows statically (SPEC §18).
  - To pass evidence *without* knowing the handler, the evidence must be an object
    `Mut 'l S ⊗ !U(S ⊗ A ⊸ F(S ⊗ B))` with `S` hidden.
  - That needs an existential over value types: a `VTy` former, about 100 match arms.
  - The run-time cost is an indirect call per operation (`dyn`).
- **Control effects** have no evidence to pass: a static name is not a value. Evidence for a
  control operation is a run-time label, which is generative names (T2, #173).

**Cost.** Proof burden: a `VTy` former for answering effects, and T2 for control effects.
Run-time: an indirect call per operation, and a label comparison at each handler for control
effects. Compile time: smallest.

### Recommendation

**Option 2.**

- It is the only option with no kernel change and no added run-time cost.
- It extends the two copying mechanisms that exist: per row (`copyFor`) and per type
  (decision 45).
- Option 3's answering half remains the route for separate compilation, should a target ever
  need it: an object with a hidden state, `dyn` cost. Recorded as Open.
- Option 1 is not needed by any of the five targets.

## 5. The recommended mechanism, as elaboration rules

All of this is elaboration into the core the checker already derives, in `Frontend/Elab/Effects.lean`
and `Frontend/Sugar.lean`. The rules are numbered for the spec entry.

### 5.1 Computation parameters (R1)

- A parameter whose type is a function type with a row is a **computation parameter**. The type
  is written `(A…) -> B with P` in the sketch; `P` is its provided row and may be empty.
- A function with a computation parameter is a **template** in it (decision 45). It is not
  elaborated as written.
- Its own row is inferred per copy, as `P`'s and its body's effects less what it handles, plus the
  argument's tunneled row `T`.
- The report (`row` line, #126) prints the tunneled part as `..f`. This is the `..` of effects
  scoping's operator N1, "specialise here".

### 5.2 Calls and copies (R2)

At a call `h(…, c, …)`, where `c` is at a computation parameter `f : (A) -> B with P`:

1. **`c` is a known code.** It is a closure literal, a named function, or a computation parameter
   of the enclosing copy, which is itself known by induction on the copy's construction. Anything
   else is a stored callback (§5.6).
2. **Split `c`'s row.** `T = row(c) \ P`. Each instance in `T` is resolved **at the call of `h`**,
   lexically, to what serves it there: a capability, or a site name. This is the tunneled
   assignment.
3. **The key.** Copy `h` with key `(h, c's code, T's assignment, h's own assignment)`. The copy
   has fresh site names (`freshSite`, as now).
4. **Inside the copy**, each call `f(v)` is `c`'s code at `v`.
   - `P`'s instances are resolved at the point of `f(v)`, to what serves them there: a site of
     the copy, or the copy's own row.
   - `T`'s instances are as fixed in step 2.
   - `c`'s code is copied per such point, by `copyFor`, as any function with a row.
5. **`c`'s captures become parameters of the copy**, taken first and handed back first, threaded
   as capabilities are (SPEC §18). A capture used by `f` under a site with an abortive operation
   is **lent per entry** to that site, by the unwinding reborrow (`withbor3U`). This is the rule
   SPEC §18 states for capabilities in a control `with`'s body. So an abort ends the lend, and the
   next attempt has the capture again (target 1).

**What this gives** (by inspection of the rules):

- the copy is the program a user would write with the callback inlined;
- linearity of the captures is checked by the unchanged checker. A callback that consumes an
  owned capture and is called twice is rejected, at the second call;
- capabilities are threaded through the copy, not captured by the callback. So two callbacks may
  use one stateful capability: `sharedUnit_safe`'s shape, not `twoBlocks_refused`'s.

### 5.3 Site freshness (R3), the escape check

At each control site `hnd (n, H) e` with context `Γ₂`, result `F_Σ R`, and the handled effect's
operation types `E`, the name `n` must not occur free in:

- the type of any slot of `Γ₂` the body uses;
- `R`;
- the operation types of `Σ`;
- `E`.

`n` occurs free in a type when some row inside it has an operation of name `n` not handled
inside. This is a structural function over `VTy`/`CTy`.

- **Its origin.** Zhang & Myers, `[t-down]`: "the label ℓ must not occur free in the result type T
  and effects e. Otherwise, ℓ could outlive its binding scope."
- **Why we add `Γ₂`.** Their labels are bound by the term, so the context cannot mention them. Our
  names are static literals, in scope everywhere. Asking `n ∉ Γ₂` is what makes the site a
  binder.
- **What it costs.** It is checked by the elaborator. With fresh names per copy, it can fail only
  when a value whose type mentions `n` is made inside the site and would leave it, or would be
  passed into another instance of it (§6).
- **Optional: the same condition as a side condition of `effHandle`.** Restricting a rule leaves
  its compatibility lemma (`handle_compatC`) as it is. The function is about 40 match arms.

### 5.4 `|>` at a computation parameter (R4)

- `e |> g(a, …)` is `g(e, a, …)` (decision 50).
- When `g` is a handler, it is `with g(a, …) { e }`.
- When `g`'s first parameter is a computation parameter, `e` is that argument: a known code, the
  thunk of `e`.
- Nothing else is new. A chain is nested `with`s and copies, innermost first.

### 5.5 Second-class callbacks (R5)

**The rule:**

- A computation parameter may be **called**, or **passed** at a computation parameter.
- It may not be stored in data or a cell, returned, captured by a closure that is stored, or
  bound by `let` to a value.
- A closure literal that captures it and is itself passed at a computation parameter is still
  second class.

**Its reading: a second-class callback is a borrowed thunk.**

- The callee holds a borrow of the callback's environment for the duration of the call. The
  captures are owned by the creator's frame, which is below the callee on the stack.
- Within the call, the callee may run the callback any number of times. Its captures are lent at
  each run (R2, step 5).
- This is how `HandlersAsBorrows` encodes Ξ's blocks: "a block receives the environment at each
  call instead of capturing it" (`x_sharedUnit`).
- **Second class here means borrowed, not unstorable by fiat.** The storable form is §5.6.

**Effekt.** A second-class block in Effekt is exactly this: passed, not returned, its
capabilities lexical. We obtain the restriction from what a copy can see, not from a separate
kind of type.

### 5.6 Stored callbacks (R6)

A **stored callback** is a computation that reaches a position where it is not a known code:

- a field of data;
- the contents of a cell;
- a returned value;
- an element of a collection.

**Its type**, in the kernel:

    [@c] !U(∀'l₁ … 'l_k. Mut 'l₁ S₁ ⊗ … ⊗ A ⊸ F_{p₁:E₁, …} (Mut 'l₁ S₁ ⊗ … ⊗ B))     (many uses)
    [@c]  U(∀'l₁ … 'l_k. …)                                                            (one use)

The type rules, in order:

1. **Captures.**
   - A many-use stored callback captures only persistent values (`bangThunkV`'s `Persistent Γ`):
     `!` values today, and data and `Imm` borrows once promotion is widened (#9, T6, proved sound
     in `experiments/Grades`, `bangThunkF_compatG`; #58).
   - A one-use stored callback (`U`, a completion callback) captures anything.
2. **Lifetime-bounded capture.**
   - A stored callback that captures borrows is boxed at a lifetime `@c` that each captured
     borrow outlives: `boxI`, with its `CtxOutlives` premise.
   - It may be kept wherever `[@c] …` may (`box_lolli_outlives_iff` at the paper level;
     `crossProg`).
   - So storage is bounded by lifetimes, where System C bounds it by capture sets
     (effects-scoping §7.1). No new rule is needed: `boxI` boxes any value, a thunk included.
   - T2 (#173) is needed only for a thunk that is not boxed.
3. **No stateful capability is captured.**
   - A stateful answering capability is a `Mut` borrow. A `!` thunk cannot capture it
     (promotion), and two closures cannot share it (`not_sharedCapture`).
   - So a stored callback's answering effects are **passed to it at each call**, as `Mut`
     parameters under a `∀'l` bound by the thunk. The caller of the stored callback lends its
     own capability. The handler, and so `S`, is fixed by the stored type: decision 45's
     instances, keyed by the handler.
   - A stored callback whose caller's handler is not known statically needs the object of Option
     3, with a hidden `S`: Open, at `dyn` cost.
4. **Control effects are ports.**
   - The stored type fixes a static name `p_E` (a **port**) for each control effect `E` of its
     row: one name per type declaration (per instance of a generic one).
   - A closure stored at that type is elaborated with `E`'s operations at `p_E`. They are provided
     by its eventual caller, not tunneled.
   - A row instance carries its port: `Fail[Err]@p`.
5. **Serving a port.**
   - The site serving a port instance is **named by the port**: the `with` of `E` that a call of a
     stored callback lies under (directly, or through the rows of the calls between) takes the
     name `p_E` instead of a fresh one.
   - Rows are inferred before sites are named (`rowC`), so the `with` knows its body's ports
     before it is named.
   - Two ports of one effect under one site are rejected with a message. The general fix is a
     relabelling (Open, below).
   - The kernel already types nested sites of one name: an inner `hnd p`'s result row lacks `p`,
     and `effSub` adds it back for the outer body.
6. **Freshness for ports.** A port is bound by the stored type: the callback is generic in which
   instance serves it. So R3 does not count a port as free in `Γ₂`. Tunneled names in a stored
   callback stay free, and R3 confines the callback to the extent of their sites.
7. **Collections of differently-effectful callbacks** take the union of their rows, by `effSub`
   on each element's body (an η-expansion that erases). A `Loop` among them is §14's own question
   (`corpus/pending/callbacks-in-data.bc`), not this one.

**The general relabelling (Open).**

- A stored callback with port `p`, called where `E` is served by an existing site `m`, could be
  wrapped as `hnd (p, relabel_{p→m})`.
  - An abortive clause is `λv. raise_m v`: typable today.
  - A resuming clause is `λ(v, κ). y ← perform_m v; (force κ).1 y`.
- **The resuming clause is not typable today.** It holds an affine `κ` across a control operation,
  and `κ` has no destructor (SPEC §15, *A body that performs a control operation*).
- **The fix is a kernel primitive** `rename (p, m) e`, Frank's adaptor:
  - its step: `rename(p,m) K[perform (p, v)] ↦ y ← perform (m, v); rename(p,m) K[y]`;
  - its rule: `e : F_{p:E, Σ} A ⊢ rename (p, m) e : F_{m:E, Σ} A`;
  - its proof: one compatibility lemma, by induction on `ewpTS` as in `handle_compatC`'s
    forwarding case, plus the unique-decomposition and determinism cases of a new frame.
- **Recommendation: do not build it** until a program needs two ports of one effect under one
  site.

### 5.7 Named instances (#155)

- A named instance in a computation parameter's provided row (`body: () -> A with a: Kube, b:
  Kube`) is two provided instances. Each resolves at the call of `f` to the site or capability of
  its name.
- Tunneled named instances are resolved where the argument was written, as any tunneled instance.
- Nothing is added: names are part of the copy key. SPEC §19, *Names*, already makes two
  instances two row entries.

## 6. Accidental handling

### 6.1 The claim

> `retry`'s own `Fail` handler does not catch a `Fail` that the callback performs for its
> creator.

With R2:

- the callback's `Fail` is provided (`retry`'s parameter type says so), and it *should* reach
  retry's site;
- an unrelated `Fail` is tunneled, at the creator's site name `m`.

So the question is whether `perform`/`raise` at `m` can be caught by a site of the copy. The
general form, for any higher-order function `h` with an internal site and a callback that tunnels
`E`, is Zhang & Myers' `map` with an internal `NoSuchElement` handler (their §1).

### 6.2 Where static names already suffice (hypothesis, with the argument)

`Head.hop` catches `perform (m, …)` at the **nearest** `hnd (m, …)`. So a tunneled operation at
`m` is mis-caught only if some `hnd (m, …)` other than its creator's instance lies between it and
that instance. Name that configuration **N(m)**: one dynamic instance of a site of name `m`
nested inside another.

1. **Distinct copies have distinct names.** A site of `h`'s copy has a name made during that
   copy's elaboration (`freshSite`, a global counter). The tunneled name `m` existed before the
   copy was keyed, so it is not a name of the copy's own sites. **By inspection.**
2. **N(m) needs a cycle in the copy graph.** An instance of `m` is entered by running the copy
   that owns it. To enter it again while it is live, that copy must be reached from code running
   inside it. That is an edge path from the copy back to itself: copies call copies, an inlined
   callback's code belongs to the copy it is inlined in, and a stored callback's possible codes
   are every closure stored at its type.
   - A suspended instance inside a reified `κ` is not on the stack, so it does not count.
   - Resuming `κ` reinstalls its own `hnd`, which is then the nearest for the resumed region
     (`kappa`).
3. **Today's surface has no cycle.** Functions are in declaration order, and recursion is
   structured (SPEC §14; decision 24's `rec` is not built). A callback's code is a literal at a
   call site, so `h(c)` with `c` calling `h` makes a new copy, keyed by `c`, with fresh names
   (step 1).
4. **R3 removes the remaining route: a value that outlives its instance.** Without it, a closure
   resolved to `m` could be stored in a `let mut` outside the site, or returned. It would then be
   run under a later instance of the same site: the next turn of a loop, or the next call of the
   same copy. That is not N(m), but it is the same mis-catch. With R3 such a value's type mentions
   `m` and lies in `Γ₂` or `R`, and is rejected.

**So, by this argument:** in a program whose copy graph is acyclic and whose sites satisfy R3,
every operation is handled by the instance its code was resolved to, which is lexical scoping.
The provable core is §9.2's uniqueness lemma: under "no N(m)", the instance `Head.hop` picks is
the unique live instance of `m`. It is a statement about `Kont` and the machine, with no
relation and no inversion of `CDerives`.

### 6.3 Where it fails

- **Recursion through a site** (decision 24's `rec`, S3).
  - `fn walk(t, f: () -> 1) = with to_result { f(); for c in children(t) { walk(c, { raise(e) }) } }`
    has a closure resolved to `walk`'s site at instance `I₁`, tunneled into the recursive call,
    whose instance `I₂` of the same site would catch it.
  - **Monomorphisation cannot separate the instances.** Each copy's call needs a new copy keyed by
    the previous copy's fresh name: polymorphic recursion over names, which does not terminate.
    The elaborator's fuel catches it; the message should say so.
  - **With `rec` as an operation, R3 rejects it.** The operation's argument type is `walk`'s
    parameter type, which then mentions the site's name, inside the site's outer row.
  - **To accept it needs generative labels.** Biernacki et al.'s labels by night: a fresh label per
    dynamic instance, with a continuation confined to its handler's scope (T2, #173). Open.
- **A port served twice under one site** (§5.6): rejected. It is not a mis-catch.
- **I have not built any of these configurations in Lean**, and have not verified that the rejected
  programs are the only ones affected.

### 6.4 Comparison

| system | how `map`'s internal handler is kept from catching the callback's effect |
|---|---|
| Koka | it is not: `mask` by hand, or named handlers |
| Effekt / System C | capabilities: the callback holds the creator's capability |
| Zhang & Myers | generative labels at run time; a label must not escape its binder |
| Biernacki et al. | effect variables bound by the handler; labels at run time |
| **here** | static names, fresh per copy; copies per callback; R3, a label's escape condition at our static names; generative labels only behind T2 |

## 7. Higher-order effects

**The question.** Should operations take computations, as in `catch(M, h)`, `local(f, M)` or
`timeout(d, M)`? This is Wu, Schrijvers & Hinze's scoped effects, Bach Poulsen & van der Rest's
higher-order effects, and Lindley et al.'s parameterized theories.

**Answer, for targets 1–5: no.** Each scoping construct is a **function over a passed
computation** that installs ordinary handlers (R2 and R4):

| construct | as a function over a computation |
|---|---|
| `catch(M, h)` | `M |> to_result`, then a branch; or `with handler_of(h) { M }` |
| `local(f, M)` (Reader) | a function whose body installs a `Reader` handler at `f(ask())` around `M`, which forwards nothing else |
| `retry(n, M)` | §1.2 target 1 |
| `timeout(d, M)` | a handler of `M`'s `Wait` (provided) that forwards each `wait` outward and cancels `κ` at the deadline; it raises `Timeout`. Clock reads are an answering effect, tunneled |
| `finally(M, D)` | `M then x. return x unwind D`, the kernel's `[then]` |

- **The literature's concern is handler order.** In Wu et al.'s example, `catch` interacts with a
  state handler, and the result depends on which handler is outermost. Deep handlers with explicit
  order give both answers: SPEC §19's program 1 shows `Log` inside and outside `Fail`.
- **What a function cannot do.** An outer handler cannot choose the meaning of the scoping
  construct itself, as an elaboration handler does in hefty algebras. For example, a test harness
  making every `timeout` succeed without editing the callers.
- **The way to get that is to make the construct's primitives effects.** `timeout` reads time
  through `Clock` and suspends through `Wait`. A test harness serves `Clock` with a fixed time,
  and so changes what `timeout` does, without `timeout` being an operation.
- **An operation that genuinely takes a computation.** For example `fn timeout[A](d, body: () -> A)
  -> A` in an *answering* effect, so that the meaning is chosen by the provider.
  - It needs a clause polymorphic in `A` and in the body's row: rank-2 polymorphism over rows,
    which is Option 1.
  - **Open, and not recommended** unless a target needs it.

## 8. Interactions

- **#172, lending a callback across a borrow scope (T1).**
  - A second-class callback that performs a **non-abortive** control operation, called inside a
    `borrow` block whose handler is outside the block, is T1. It is rejected as today:
    `Row.Unwind` admits only abortive operations in a borrow's callback.
  - Abortive and answering operations cross, unchanged. So
    `borrow mut buf { for_each(it, { x -> push(buf, x); yield(x) }) }` stays rejected until #172.
    The same program with `raise` is accepted.
  - R2's lending of captures per site entry uses the unwinding borrows, so it is subject to the
    same rule.
- **#215, linear payloads.**
  - `retry` discards the error of a failed attempt. With linear payloads it would receive an
    owned value and must drop it: an ordinary destructor in its loop.
  - The last attempt's error propagates, so `retry` needs nothing more.
  - A `Fail[E]` provided to a callback whose `E` is linear is #215's case, unchanged by this
    design.
- **#216, clause captures by multiplicity.**
  - The retry above needs none: its clause is `to_result`'s.
  - A `default`-style handler over a passed computation, `M |> default(owned_fallback)`, needs
    #216, as `default` does today.
- **Multi-shot.**
  - An unrestricted operation's `[let]` asks `!Γ₂` (`effLet`'s `hU`). An inlined callback whose
    threaded captures are live across a multi-shot operation is therefore rejected, at the copy.
  - A callback under a multi-shot handler must capture only persistent values. That is
    `lam_bang_persistent`'s rule, now read on the copy. #9 widens it to data.
  - A stored many-use callback is `!` anyway.
- **Divergence and generators.**
  - A callback whose code loops makes the copy a div body at its row (§14's specialisation,
    subsumed by R2: the copy's inference is the copy's).
  - **Stored generators over a row** (SPEC §15 Open) are untouched. A stored generator's
    observations are pure today; a port in its observation's row would be the same rule R6
    applied to `pull`'s observations. Not designed here.
- **Answering effects inside clauses** (SPEC §18 *Not provided*) are unchanged.

## 9. What the proofs need

### 9.1 Kernel

**Targets 1–3 and 5: no new rule, no relation change, no FP change.** Every elaborated program
is checked by today's checker. The following carry over unchanged:

- `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD`;
- every compatibility lemma, including `handle_compatC`, `let_compatC`, `then_compatC`,
  `withbor3U_compatX` and `boxI_compatC`.

**Target 4:**

- **#9 (T6)**, widened promotion, so that a stored many-use callback may capture an `i32` or an
  `Imm` borrow. This is `bangThunkF_compatG` promoted from `experiments/Grades` (its soundness is
  established there) into `Core/`, with `Persistent` widened.
- Without #9, stored callbacks capture `!` values only. That covers the registry and the manager
  when their callbacks capture nothing but code.

**Optional:**

- **R3 as a side condition of `effHandle`.** No new lemma: a restriction of a rule's premises
  keeps its compatibility lemma. Cost: the free-name function, about 40 arms.
- **`rename`** (§5.6). Its cost is stated there; not recommended now.

### 9.2 New lemmas (statements, not proved)

1. **Uniqueness of resolution** (§6.2), on `Paper/`'s machine. Let `NoNest m K` say no frame
   `hnd (m, _)` of `K` lies under another frame `hnd (m, _)` of `K`. If
   `K = K₁[hnd (m, H) K₂]` with `K₂.HasHnd m = false`, and `NoNest m K`, then `K₁.HasHnd m =
   false`.
   - So the instance `Head.hop` uses is the only live instance of `m`.
   - Proof: induction on `Kont`.
   - Its use is with an invariant that `NoNest` holds of every reachable configuration of a
     program whose copy graph is acyclic. That invariant is about the elaborator's output, so it
     is stated on the copy graph and tested, not proved over all core programs.
2. **Freshness confines a name** (R3), hypothesis. If every site satisfies R3, then in every
   reachable configuration, each free occurrence of `perform (m, _)`/`raise (m, _)` in a value
   lies inside a frame `hnd (m, _)`, or in code that runs inside one before the value can leave.
   - Two routes:
     - a syntactic one needs subject reduction, which inverts `CDerives`: its cost must be stated
       (CLAUDE.md, *Do not invert `CDerives` casually*);
     - a semantic one is a second, name-indexed relation.
   - **Recommendation:** state (1), build it, and keep (2) as the design's hypothesis. Its failure
     would show up as a corpus program whose operation reaches the wrong instance, which the
     reports (`call` lines) make visible.

### 9.3 Laws (optional, as SPEC §18's `op_tail`, `handle_fold`)

**Inlining is calling.** For a known `c` at a computation parameter, the copy's run equals the run
of `h` applied to `thunk c`, at every host, when `c`'s captures are `!`.

- This is a β-law over `ewpTS`, which `ewp_bind_pure_frame` and the `[let]` frame suggest.
- It states that R2 changes cost, not meaning.
- Not needed for safety.

## 10. Lowering

| piece | lowering | cost against hand-written |
|---|---|---|
| a second-class callback | its code in the copy (R2): calls are direct, captures are parameters | 0 allocations, 0 dispatches: Rust's monomorphised closures |
| a provided abortive operation (`retry`) | branch per call (SPEC §19 *Lowering*), the site a `catch` | the `Result` program's |
| a provided resuming operation | state machine. With the handler known per copy, a tail-resumptive clause is a direct call (SPEC §19, *A tail-resumptive operation is a direct call*) | as today |
| a tunneled operation | as if written at the creator | as today |
| `|>` at a handler | `with` | none |
| a stored callback | a closure: code pointer and environment, one allocation at creation; each call is an indirect call; a call that may suspend uses the outcome convention of SPEC §19 (*A call that may reach several codes that suspend dispatches*) | Rust's `Box<dyn Fn>`, and `Box<dyn Future>` when it suspends |
| a port's site | an ordinary site with a fixed name | none |
| copies | one per key | code size: measured, as effects-scoping §7.9 proposes |

**Where it cannot be zero-cost, and why that is the target's own cost:**

- **A stored callback** pays an allocation and an indirect call, because its code is chosen at
  run time. A hand-written program storing heterogeneous callbacks pays the same in C (a function
  pointer and an environment) and in Rust (`dyn`).
- **Recursion through a resumption point** costs one object per level (SPEC §19 *Lowering*).
  Unchanged.

**No run-time handler search is added.**

- Names stay static.
- Copies are monomorphic, so the closure flow that finds which codes suspend still resolves per
  code.
- Ports are static names.

## 11. Open questions for the user

1. **Option 2.** Confirm monomorphisation over static names, with no row variables in the
   kernel. This is a one-way door for what a function type may say about effects:
   - a parameter writes what the callee provides;
   - nothing else is written.
2. **Provided vs tunneled (R1/R2).** Confirm Effekt's split, with the provided row written on the
   parameter. A one-way door: it decides which handler catches what.
3. **R3 (site freshness).**
   - Elaborator only, or also a kernel side condition of `effHandle`?
   - The latter costs one free-name function, and puts abstraction safety in the trusted checker.
4. **Recursion through a site** (§6.3). Rejected until generative labels (T2, #173). Confirm this
   is acceptable for S3 (`rec`), or raise T2's priority.
5. **Stored callbacks (R6).**
   - (a) Ports as static names fixed by the stored type, served by the `with` around the call.
   - (b) Stateful answering effects passed in by the caller, with the handler fixed by the type.
   - (c) The object of Option 3 (hidden state, `dyn`) left Open.
   - Confirm (a) and (b), or ask for (c).
6. **Higher-order operations** (an operation that takes a computation, chosen by a provider).
   Confirm they are out of scope (§7).
7. **The spelling of a computation parameter's type and of a stored callback type.** Provisional,
   per *Mechanism before syntax*. Not asked here, beyond noting that the provided row must be
   writable on a parameter.

## 12. Proposed rewrite of #161's body

> **Effects S4c: functions over effectful computations (effect polymorphism, stored callbacks)**
>
> Design: `docs/effect-polymorphism.md`. Kernel effects (SPEC §19) and the surface (SPEC §15, §18)
> are on `main`; this issue is the surface's functions over computations, with no kernel change for
> targets 1–3 and 5.
>
> **Mechanism (Option 2 of the design):**
> - **Monomorphisation over static names.** A function with a computation parameter is a template,
>   copied per (function, callback code, assignment of the callback's tunneled effects, assignment
>   of its own row); the callback's code is inlined, its captures threaded as capabilities are,
>   and lent per entry to a site with abortive operations.
> - **A parameter's row is what the callee provides.** Every other effect of the argument tunnels
>   to the handlers where it was written.
> - **Site freshness (R3)**: a site's static name occurs free in no type of its context, result or
>   outer row (Zhang & Myers' escape condition, at static names).
> - **`|>` at a computation parameter or a handler** (decision 50).
> - **Stored callbacks**:
>   - `[@c] !U(∀'l. Mut 'l S ⊗ A ⊸ F_{ports} (…))`;
>   - persistent captures (with #9), boxed at the lifetime of their borrows;
>   - stateful capabilities passed in by the caller (`not_sharedCapture`);
>   - control effects at ports, static names fixed by the stored type, served by the `with`
>     around the call.
>
> **Acceptance:**
> 1. `retry` over a computation that captures a lend, re-run after an abort (`lib/fail.bc`).
> 2. `run() |> to_result`, and `report(body)` returning `A + E`.
> 3. `corpus/pending/yield-callback.bc` runs, with 0 allocations and 0 dispatched calls.
> 4. An event registry and a manager of reconcile functions, stored, dispatched with the caller's
>    `Log` capability and a `Fail` port.
> 5. `controller(…) |> timeout(…) |> retry(…) |> log(…) |> kube(…)`, once `Wait` (#52) and resuming
>    operations in a counted loop's body (stage 3 of #188) exist; until then with `timeout`
>    omitted.
> - Accidental handling: a higher-order function with an internal `Fail` site, given a callback
>   that raises to its creator's `to_result`, does not catch it (a corpus program and its `call`
>   report).
> - Rejects, each with a message:
>   - recursion through a site with a tunneled callback;
>   - a site name escaping;
>   - a second-class callback stored;
>   - two ports of one effect under one site;
>   - a non-abortive operation of a callback across a borrow (#172).
> - Counts at parity with the hand-written programs; a code-size column for copies.
> - Proof: the uniqueness lemma of the design §9.2(1); #9 promoted for stored captures; no other
>   kernel change.
>
> **Open:**
> - generative labels for recursion through a site (T2, #173);
> - a `rename` primitive for two ports of one effect (Frank's adaptors);
> - a capability object with hidden state for stored callbacks whose handler is not known
>   statically (`dyn`);
> - operations that take computations (higher-order effects);
> - stored generators over a row.
>
> Depends on #9 (stored captures), #52 (`Wait`, for `timeout`), #188 stage 3. Related: #155,
> #172, #215, #216. Part of #18.

## Sources

- Zhang & Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019,
  https://cs.uwaterloo.ca/~yizhou/papers/abseff-popl2019.pdf (read: abstract, §§1, 3, 4.2–4.3).
- Biernacki, Piróg, Polesiuk & Sieczkowski, *Binders by Day, Labels by Night: Effect Instances via
  Lexically Scoped Handlers*, POPL 2020, https://dl.acm.org/doi/10.1145/3371116 (abstract only).
- Xie, Brachthäuser, Hillerström, Schuster & Leijen, *Effect Handlers, Evidently*, ICFP 2020,
  https://www.microsoft.com/en-us/research/publication/effect-handlers-evidently/ (abstract).
- Xie & Leijen, *Generalized Evidence Passing for Effect Handlers*, ICFP 2021,
  https://dl.acm.org/doi/10.1145/3473576 (effects-scoping §4.1).
- Brachthäuser, Schuster & Ostermann, *Effects as Capabilities*, OOPSLA 2020; Brachthäuser,
  Schuster, Lee & Boruch-Gruszecki, *Effects, Capabilities, and Boxes*, OOPSLA 2022,
  https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects/ (abstract;
  `experiments/HandlersAsBorrows` §5 for the body).
- Schuster, Brachthäuser & Ostermann, *Compiling Effect Handlers in Capability-Passing Style*, ICFP
  2020, https://dx.doi.org/10.1145/3408975 (abstract); *From Capabilities to Regions*, OOPSLA 2023,
  https://dl.acm.org/doi/10.1145/3622831 (title only).
- Convent, Lindley, McBride & McLaughlin, *Doo Bee Doo Bee Doo*, JFP 2020,
  https://www.cambridge.org/core/journals/journal-of-functional-programming/article/doo-bee-doo-bee-doo/DEC5F8FDABF7DE3088270E07392320DD
  (abstract: adaptors).
- Hillerström & Lindley (Links): effects-scoping §4.5.
- Tang, Hillerström, Lindley & Morris, *Soundly Handling Linearity*, POPL 2024; van Rooij &
  Krebbers, *Affect*, POPL 2025: `experiments/HandlersControl` §3.
- Tang, White, Dolan, Hillerström, Lindley & Lorenzen, *Modal Effect Types*, OOPSLA 2025,
  https://dl.acm.org/doi/10.1145/3720476 (abstract).
- Wu, Schrijvers & Hinze, *Effect Handlers in Scope*, Haskell 2014,
  https://people.cs.kuleuven.be/~tom.schrijvers/portfolio/haskell2014.html (abstract).
- Bach Poulsen & van der Rest, *Hefty Algebras*, POPL 2023, https://dl.acm.org/doi/abs/10.1145/3571255
  (abstract).
- Lindley, Matache, Moss, Staton, Wu & Yang, *Scoped Effects as Parameterized Algebraic Theories*,
  ESOP 2024, https://arxiv.org/pdf/2402.03103 (abstract).
