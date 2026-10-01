# Functions over effectful computations: effect polymorphism and higher-order effects (#161)

Design for #161, after §19 (kernel effects) and stages 1–2 of #188 (surface effects). Nothing here
is built. Each claim is marked as one of:

- **established**: a Lean declaration on `main`, named after it was found by `grep`;
- **by inspection**: read off a definition, with no theorem behind it;
- **hypothesis**: argued here, not machine-checked.

The user's decisions on §11 are recorded there and in `docs/decisions.md` entry 57.

## 0. Summary

- **Mechanism.** Effect polymorphism stays at the surface; this is Option 2 of §4. The kernel stays
  first-order in rows: no row variables, no new `CTy` former, no relation change, no new
  `CDerives` rule.
- **Who serves an effect.** A computation parameter's row is split in two (Effekt's reading, and
  Zhang & Myers' tunneling):
  - the **provided** row is written in the parameter's type. The callee serves it: an operation of
    a provided effect is at a **port**, a static name fixed by the parameter's declaration. The
    callee serves it by a site of that name;
  - the **tunneled** row is everything else the argument performs. It is never written, and it is
    resolved where the argument was written.
- **What is copied, and what is not** (§5.8). This version separates three things the first
  version conflated:
  1. **Instances per assignment of effect names are typing artefacts.**
     - Two instances that differ only by names have the same code up to name literals.
     - A **renaming lemma** (`CDerives` is equivariant under an injective renaming of operation
       names fixing `0`) would let the checker derive a function once and instantiate it by
       renaming. Hypothesis, not built.
  2. **Copies per callback are an optimisation.**
     - The default is **one body** of the higher-order function. The callback is passed as a
       closure value: the backend's defunctionalised closure, a tag and its environment,
       dispatched by a `switch`.
     - Inlining a known callback is optional, chosen by a heuristic, as Rust's inliner chooses.
     - No rule requires it for correctness, with one exception (§5.2, R2c): a provided resuming
       operation that the callee does not serve itself. That case needs either inlining or a
       `rename` primitive.
  3. **Answering effects add no code copies.**
     - A capability is an argument: a `Mut` location and the clause as a closure value.
     - They do add typing instances, one per handler state type, because the kernel has no
       existential type.
- **Code size** is that of one body per (higher-order function, **profile** of the callback's
  tunneled row). A profile is which of abort, suspension and multi-shot the row contains, because
  those change drop glue and the state machine. Inlined copies are added where the heuristic
  chooses them. Effects add no copies of their own beyond the profile. **Hypothesis:** this is
  Rust's size or less.
- **Accidental handling.** Static names already prevent it, given one added check and one rule:
  - **site freshness (R3)**: a site's or port's name occurs free in no type outside it. This is
    Zhang & Myers' `[t-down]` condition at static names, checked by the elaborator only (decision
    57);
  - **a renamed instance** when a callback's tunneled row mentions a name of the callee itself.

  Recursion through a site whose callback tunnels that same site needs unboundedly many renamed
  instances. It is rejected (decision 57).
- **Stored callbacks** use the same closure value, with these rules:
  - it is boxed at the lifetime of its borrows, `[@c] !U(…)`;
  - it captures persistent values only (#9 to widen);
  - stateful capabilities are passed in by the caller (`not_sharedCapture`);
  - control effects use the same ports.
- **Higher-order effects** (operations that take computations) are out of scope (decision 57).
  `catch`, `local`, `retry` and `timeout` are functions over a passed computation that install
  ordinary handlers.
- **Proof cost.**
  - The kernel needs nothing.
  - Two lemmas are proposed, the renaming lemma and the uniqueness of resolution (§9.2).
  - #9 is needed for stored callbacks that capture data.

## 1. The problem, in the kernel's terms

### 1.1 Vocabulary

| term | meaning |
|---|---|
| **computation parameter** | a parameter whose argument is code to run: an argument of computation type `A ⊸ F_Σ B` in CBPV |
| **provided row** `P` | the effects the callee serves for the argument; written in the parameter's type |
| **port** `p_E` | the static name at which a closure passed or stored at a given parameter or type performs its provided effect `E`; fixed by that declaration (per instance of a generic one) |
| **tunneled row** `T` | the effects the argument performs that the callee does not serve; resolved where the argument was written; never written |
| **profile** of a row | which of abortive, resuming (linear or affine) and unrestricted operations it has |
| **closure value** | the representation of a passed callback: code `!U(∀'x. Mut 'x Env ⊗ A ⊸ F_Σ (Mut 'x Env ⊗ B))` and an environment lent as `Mut 'l Env` (SPEC §2's `FnMut` row, `(env, !code)`); the backend's defunctionalised closure |
| **second-class callback** | a computation argument that is called or passed on, and never stored, returned or captured by a stored closure |
| **stored callback** | a computation kept in data, a cell or a returned value, and run later |
| **site** | a control `with`: the kernel's `hnd (n, H) e` with a static name `n` (SPEC §19) |

Throughout, `n`, `m` and `p` are static names, as in SPEC §19. `F_{n:E} A` abbreviates the row of
`E`'s operations at the name `n` (`Row.ofEff`).

### 1.2 The five targets

Each target is given as the kernel term the design must produce, and then as a surface sketch.
**The sketches are provisional spellings (decisions 51, 55, 56 and 57) and are not the design.**
`(…) -> B with E` stands for a computation parameter whose provided row is `E`.

**Target 1: `retry`.** Run a computation, and run it again if it raises.

- **Kernel: one body for every callback.** It takes the callback as a closure value. `p` is the
  port of `body`'s `Fail`, and `m` is the caller's name for `retry`'s own `Fail`:

      retry : !U(I32 ⊗ !U(∀'x. Mut 'x Env ⊗ 1 ⊸ F_{p:Fail[E]} (Mut 'x Env ⊗ A)) ⊗ Mut 'l Env
                 ⊸ F_{m:Fail[E]} (Mut 'l Env ⊗ A))
      attempt = withbor3U env (Λ'x. λc. hnd (p, H_to_result) (force code [] (c, ())))
      last    = hnd (p, (return, λv. raise_m v)) (force code [] (env, ()))

  - `attempt` is a turn of a counted loop (§16's `count_try`).
  - `withbor3U` lends the environment anew to each attempt. An abort ends the lend, and the next
    attempt has the environment again (`withbor3U_compatX`; `reborrowRaise`'s shape in a loop).
  - The last attempt runs outside retry's own site. Its `Fail` at `p` is relabelled to `m` by a
    site whose clause raises again: an abortive clause, which today's `[handle]` types.
  - The `Env` in the type is a type parameter: one typing instance per environment type (§5.8),
    and one code.
- **Kernel: the inlined alternative** (optional, R2b). A copy with `code` substituted:
  `withbor3U conn (Λ'x. λc. hnd (p, H_to_result) (c_body c))`. The environment is the captured
  borrows themselves, with no cell (§10).
- **Surface sketch:**

      fn retry[A, E](tries: i32, body: () -> A with Fail[E]) -> A with Fail[E] =
        for _ in 1..tries { match body() |> to_result { inl a -> return a | inr _ -> () } };
        body()

**Target 2: `run() |> to_result`.** A handler applied to a computation.

- **Kernel:** `hnd (n, H_to_result) (run ())`, with `run`'s `Fail` at `n`.
- **Surface sketch:** `M |> h(args)` is `with h(args) { M }` (decision 50). As a function over a
  passed computation:

      fn report[A, E](body: () -> A with Fail[E]) -> A + E = body() |> to_result

**Target 3: callbacks that yield** (`corpus/pending/yield-callback.bc`).

- **Kernel.** `for_each` provides nothing, so the closure's `yield` is tunneled, at `tens`'s site
  name `n_t`.
  - `for_each`'s body is one div body at a row of the **suspending profile**. It observes `it` and
    calls the closure value at each element.
  - With the closure inlined (R2b), it is the term the hand-written `for x in it { yield(x * 10) }`
    elaborates to (`Loop_{n_t:Yield}`, SPEC §15).
- **Surface sketch.** The pending program with the `!` dropped from `f`'s type:
  `fn for_each(it: U (pull i32 1 1), f: (i32) -> 1) -> 1`.

**Target 4: stored callbacks.** An event registry, and a manager holding several controllers'
reconcile functions.

- **Kernel.**

      H = [@c] !U(∀'l. Mut 'l S_log ⊗ Event ⊸ F_{p:Fail[Err]} (Mut 'l S_log ⊗ 1))

  - `p` is the port of `Fail` fixed by the type `H`.
  - The dispatcher calls each element under a site named `p`, and lends its own `Log`
    capability: `hnd (p, H_to_result) (force h [] (c, ev))`.
- **Surface sketch:**

      type Handler = (Event) -> 1 with Log, Fail[Err]
      fn dispatch(hs: &List[Handler], ev: Event) -> 1 with Log =
        for h in hs { match h(ev) |> to_result { inl _ -> () | inr e -> log_err(e) } }

**Target 5: the north-star chain.**

    controller(Foo, reconcile) |> timeout(30.s) |> retry(5) |> log(json(&mut stderr)) |> kube(&mut client)

- **Reading the chain.**
  - Innermost first (decision 50): `kube(log(retry(timeout(controller))))`.
  - `kube` and `log` are answering handlers: borrow blocks lending their state (SPEC §18).
  - `retry` provides `Fail`.
  - `timeout` provides `Wait` (#52): it forwards each `wait` outward and resumes, or cancels the
    continuation at the deadline and raises `Timeout`.
  - `reconcile`'s `Kube` and `Log` are tunneled. They are captured in the closure's environment,
    as borrows of the capabilities that `kube` and `log` lend.
- **Kernel (default, no inlining).**

      withbor (kube state) (Λ'k. λck. withbor (log state) (Λ'g. λcg.
        let env = (ck, cg, …) in                      -- the chain's closure environment, in a cell
        retry (5, code_t, &mut env)                   -- retry's one body; each attempt a withbor3U of env
          where code_t = timeout's closure: hnd (p_wait, H_timeout) (controller's closure …)))

- **Status.**
  - Nothing in this term is special to any effect.
  - **Hypothesis:** it types with today's rules, given `Wait` (#52) and a counted loop whose body
    performs a resuming operation (stage 3 of #188).

## 2. What exists

**Established (kernel, SPEC §19):**

- `CTy.eff n i q A B C` stacks one operation of a static name over a computation type, and
  `CTy.effOf Σ R` is `F_Σ R`. Names are `UInt32` literals in types and terms (`opArgE`, `hndTerm`).
- `effHandle` asks `n ≠ 0` and `∀ o ∈ S, o.n ≠ n`. It asks nothing of `n` in the types of the
  context, the result or the outer row.
- `Head.hop` handles `perform (n, …)` at the nearest `hnd (n, …)`, with `K.HasHnd n = false` for
  the frames between.
- **The rules and their compatibility lemmas:**
  - `effSub` (`RowLe`) is row subsumption;
  - `effLet`, `effThen`, `effPerform` and `effRaise` are as in SPEC §19;
  - the lemmas are `sub_compatC`, `perform_compatC`, `raise_compatC`, `let_compatC`,
    `then_compatC` and `handle_compatC` (from `ewp_handle`);
  - `fundamentalC` and `adequacyD` cover all of them.
- The relation at `F_Σ A` is `ewpTS` at `Row.tab Σ δ` (`cC_effOf`). An `OpTab` is a semantic
  object, `UInt32 → UInt32 → Option OpEnt`.
- `withbor1U`…`withbor3U` (`withbor2U_compatX`, `withbor3U_compatX`) take a callback whose row is
  `Row.Unwind`: abortive operations only.
- `boxI` boxes any value, a thunk included, whose context outlives the box's lifetime
  (`boxI_compatC`). `bangThunkV` promotes over `Persistent Γ`, which is `!` slots only.
- `CDerives` has 88 rules. `CDerives.append_dead` (`Core/Weaken.lean`) is a structural induction
  over all of them, and is the precedent for the renaming lemma's shape.

**Established (experiments):**

- **`not_sharedCapture` / `twoBlocks_refused`**: two closures capturing one stateful capability are
  refused. Blocks that receive the capability at each call are typed and safe (`x_sharedUnit`,
  `sharedUnit_safe`).
- **`lam_bang_persistent`, `multiShot_ref_refused`**: a `!` continuation captures only persistent
  values.
- **`box_lolli_outlives_iff`, `crossProg`**: a boxed closure outlives `@a` exactly when its box
  lifetime does.
- **`escape_refused`**: a handler's capability cannot leave its `['x]`.

**By inspection (backend, `Backend/README.md`, `Backend/Clos/Unwind.lean`):**

- **Closures are defunctionalised.** A closure is a stack value: a tag in its type's union, and
  its captured words. A known call is direct; any other goes through the type's dispatcher, one
  `switch`.
- **Cells are heap allocations.**
- **An abortive operation is branch-per-call.** A raising code answers `inl v` or `inr p`. `p`
  carries the key `(n, i)` as literals. A `catch n` compares the name only when its body may raise
  more than one name.
- **A suspended code's outcome** carries the payload as a variant per operation of the program.

**By inspection (surface, SPEC §18 and §15):**

- `freshSite` numbers a site each time a `with` is elaborated. `copyOf` elaborates a body once
  per copy, keyed by `copyName` over the handlers and sites serving its row. So copies are made
  **per assignment** today, and each has its own site names.
- §14's specialisation copies a function at a div callback's type.
- An operation inside a closure not run in place is rejected, citing #161.
- `|>` is not parsed yet.

## 3. Survey

| system | polymorphism | who handles a callback's effect | stored effectful functions | compiles to | read |
|---|---|---|---|---|---|
| **Koka** | row variables, inferred | dynamic: the nearest handler of the effect; `mask`, named handlers | first class | evidence passing: handlers passed to each call, found by constant offset; tail-resumptive operations in place (Xie et al. ICFP '20; Xie & Leijen ICFP '21) | effects-scoping §4.1; the ICFP '20 abstract |
| **Effekt / System C** | none written: "polymorphism implicitly arises from the calling context" | lexical: capabilities; a block parameter's effects are provided by the callee | blocks second class; `box` with a capture set (OOPSLA '22) | capability-passing style, iterated CPS, zero-cost when handlers are statically known (Schuster et al. ICFP '20); regions (OOPSLA '23) | effects-scoping §4.2; `experiments/HandlersAsBorrows` §5 |
| **Frank** | an ambient ability, no variables in source | positional instances; **adaptors** rewire them (Convent et al. JFP '20) | first class | interpreter | effects-scoping §4.4 |
| **Links** | row polymorphism with presence types | dynamic, by operation name | first class | generalised continuations | effects-scoping §4.5 |
| **Zhang & Myers** (POPL '19) | effect variables, handler polymorphism | **tunneling**: "Algebraic effects can be handled only by handlers that are statically aware of them; otherwise, effects tunnel through handlers" | first class | not studied | the paper, §§1, 3, 4 |
| **Biernacki et al.** (POPL '20) | effect variables bound by lexically scoped handlers | lexical by day, run-time labels by night | first class | not studied | abstract |
| **Tang et al.** POPL '24; **Affect** POPL '25 | rows with linearity kinds | dynamic | first class / affine cells | — | `experiments/HandlersControl` §3 |
| **Modal effect types** (OOPSLA '25) | modalities decoupled from functions; rows and capabilities encoded | either | either | — | abstract |
| **Scoped / higher-order effects** (Wu, Schrijvers & Hinze '14; Bach Poulsen & van der Rest POPL '23; Lindley et al. ESOP '24) | — | operations that take computations; hefty algebras *elaborate* them into algebraic ones | — | — | §7 |

**What we take.**

- **Effekt's split.** A parameter's written effects are served by the callee, the rest where the
  argument was written. It is Zhang & Myers' tunneling.
- **Effekt's premise.** Handlers are statically known after specialisation (decision 45). Here
  specialisation is optional (§5.2).
- **Zhang & Myers' escape condition**: "the label ℓ must not occur free in the result type T and
  effects e". It is strengthened in §5.3.
- **Frank's adaptors**, as the general relabelling of a port (Open, §5.6).
- **Hefty algebras' elaboration**, as the reading of `timeout` and `catch` (§7).

**What we do not take.**

- **Koka's dynamic resolution**: accidental handling.
- **Koka's run-time evidence vector**: a run-time lookup, against decision 25 and the zero-cost
  target.
- **Row variables in the kernel**: §4.
- **Generative labels**: T2 (#173) (SPEC §19, *Why not generative names*).

## 4. The polymorphism mechanism: three options

### Option 1: row variables in kernel types

`retry : ∀ε#{p}. !U(I32 ⊗ U(1 ⊸ F_{p:Fail[E] | ε} A) ⊸ F_{m:Fail[E] | ε} A)`

- **`CTy` gains two formers**: a row-variable tail, and a binder `∀ε#N. C` with a lacks set.
  - The lacks set is needed: `effHandle`'s `n ∉ Σ` becomes `n ∉ N`.
  - Each former costs about 20 match arms (CLAUDE.md, *Growth discipline*).
- **The relation gains a row environment** `η : Nat → OpTab`. Every `cC`/`vC`/`SemV` statement in
  `Core/` changes signature. The `ewp` lemmas are already generic in the table (`ewp_mono`,
  `ewp_sub`, `ewp_handle`), so the semantics accommodates it.
- **`CDerives` gains a context of row variables**, which decision 19 forbids. Putting them in
  `LifeCtx` instead touches every use of `Δ`.
- **New lemmas:**
  - `∀ε`-I and `∀ε`-E;
  - a semantic substitution lemma over every former;
  - `Loop_ε`'s positivity at an abstract row (`loopEffBody_nuOk` assumes closed operation types).
- **The backend.** Either names become run-time values, or it monomorphises anyway.

### Option 2: no row variables; polymorphism at the surface (recommended, and decided)

- **The kernel stays first-order in rows.** A function over a computation is checked at concrete
  rows. §5.8 separates what this costs:
  - typing instances, removable by the renaming lemma for instances that differ in names only;
  - code copies, one per profile, with inlining optional;
  - nothing for answering effects.

### Option 3: evidence passing

- **Answering effects** are capability passing already. To pass evidence for a handler not known
  statically, the evidence must be an object whose state type is hidden: an existential over
  value types, a `VTy` former (about 100 arms). Its run-time cost is an indirect call.
- **Control effects** have no evidence: a static name is not a value. Evidence would be a run-time
  label, which is T2.

### Costs

| | proof burden | run-time | typing instances | code |
|---|---|---|---|---|
| **1. Row variables** | two `CTy` formers; the relation's signature; a `CDerives` index (against decision 19); a substitution lemma | dispatch or search, unless the backend monomorphises | one per function | one per function, plus name dispatch |
| **2. Surface (recommended)** | none in the kernel; the renaming lemma (optional, hypothesis: a structural induction like `CDerives.append_dead`, its cost dominated by type functions); the uniqueness lemma (small) | none added on the normal path; an un-inlined callback is a `switch` dispatch; re-lending its environment for a provided abort costs one cell per callback creation (§10) | one per (function, names, tunneled row's shape, environment type, handler state type). With the renaming lemma, one per (shape, environment type, handler state type) | **one body per (function, profile of the tunneled row)**, plus inlined copies the heuristic chooses, plus renamed instances on a name collision (§6) |
| **3. Evidence** | an existential `VTy` former; T2 for control effects | an indirect call per answering operation; a label comparison per control handler | one per function | one per function |

**Expected code size (hypothesis).** Rust's or less.

- Rust copies a generic function per closure type (`impl Fn`).
- Here, without inlining, one body serves every callback of a profile, and effects add no copies
  of their own.
- With inlining, the copies are those the heuristic chooses, as Rust's inliner chooses.

## 5. The recommended mechanism, as elaboration rules

All of this is elaboration into the core the checker already derives (`Frontend/Elab/Effects.lean`,
`Frontend/Sugar.lean`).

### 5.1 Computation parameters (R1)

- **What one is.** A parameter whose type is a function type with a row is a computation
  parameter, written `(A…) -> B with P` in the sketch. `P` is its provided row, which may be
  empty.
- **Ports.** Each control effect `E` in `P` has a port `p_E`: a static name fixed by the
  parameter's declaration, one per instance of a generic function.
- **Answering effects in `P`** are passed as capability arguments: a `Mut` location and the
  clause's closure value (R2d).
- **The function's own row** is inferred per instance: `P`'s effects that it does not serve, its
  own operations less what it handles, and the argument's tunneled row `T`.
  - The report prints `T` as `..f`.
  - Its **profile** is part of the instance key.

### 5.2 Calls (R2)

At a call `h(…, c, …)`, where `c` is at a computation parameter `f : (A) -> B with P`:

**R2a. The default: a closure value.**

- **Code.** `c` is elaborated once, where it is written, into
  `code_c : !U(∀'x. Mut 'x Env_c ⊗ A ⊸ F_{ports(P) ∪ T} (Mut 'x Env_c ⊗ B))`.
  - `P`'s control operations are at `h`'s ports for `f`.
  - `T`'s are at the names that serve them where `c` is written.
  - Its captures that are not persistent form `Env_c`. They include the borrows of tunneled
    answering capabilities.
- **Environment.** `Env_c` is lent to `h` as `Mut 'l Env_c`, from a cell scoped to the call
  (SPEC §16's lend of a value).
  - **Exception:** when `h` never calls `f` again after an abort it served, `Env_c` may instead be
    passed by value and handed back, with no cell (R2e).
- **The call.** `h` is called at one instance: the key is `(h, names, the shape and profile of T,
  Env_c's type)`. The body of `h` is shared by every callback of one profile (§5.8).
- **Inside `h`**, `f(v)` is `force code [] (e, v)` on a reborrow `e` of the environment. Its
  operations at `h`'s ports reach the site of that name in `h` that encloses the call. The
  elaborator names `h`'s `with` of `E` around a call of `f` by `p_E` (as R6 rule 5).

**R2b. Specialisation (optional).**

- When `c` is a known code (a literal, a named function, or a computation parameter of an
  enclosing specialised copy), the elaborator may make a copy of `h` with `code_c` substituted.
- In the copy, `ports(P)` become the names of the sites that serve them at each call point, and
  `Env_c`'s components become parameters threaded as capabilities are. A component that crosses
  a site with an abortive operation is lent per entry to that site by `withbor3U`.
- A heuristic chooses: callee size, call count, and whether the callback is the only one at that
  type.
- **Specialisation changes no meaning (hypothesis).** The copy is the default's instance with
  `force code` β-reduced and the ports renamed (the renaming lemma, §9.2), and §9.3 states the
  law.

**R2c. A provided effect that `h` passes on instead of serving.**

- If `f(v)` is not under a site of `h` for `E ∈ P`, then `E` reaches `h`'s own row, served by
  `h`'s caller at a name `m`. The port `p_E` must be relabelled to `m` at that call.
- **Abortive `E`.** `hnd (p_E, (return, λv. raise_m v)) (f v)`. Typable today: the clause is `!`,
  captures nothing, and its argument drops. Its cost is a retag on the error path.
- **Resuming `E`.**
  - The relabel clause `λ(v, κ). y ← perform_m v; (force κ).1 y` holds an affine `κ` across a
    control operation. `κ` has no destructor (SPEC §15, *A body that performs a control
    operation*). So `effLet`'s `S.Weak → Γ₂.Drops` premise fails, and **the clause is not
    typable today**.
  - Two ways out:
    - specialisation (R2b), which substitutes `m` for `p_E` in the inlined code; or
    - a kernel primitive `rename (p, m)` (§5.6).
  - Until one of them is chosen, R2b is **required** in exactly this case. The elaborator reports
    it.
- **Passing `f` on** to another function `k` whose parameter has its own port `p'_E` is the same
  case: the closure value is wrapped by the relabelling site. Abortive: typable, and the wrapper
  is a stack closure value. Resuming: as above.

**R2d. Answering effects.**

- A provided answering effect is passed to `f` as an argument. So is the capability a function
  with an answering row receives from its caller.
- The argument is the handler's state, lent as `Mut 'l S`, and its clause as a closure value
  `!U(Mut 'x S ⊗ A ⊸ F(Mut 'x S ⊗ B))`.
- There is **no code copy per handler**: the body calls the clause through its closure value,
  which is direct when the flow finds one handler.
- There is **one typing instance per state type `S`**, because the kernel has no existential type
  to hide `S`. The code is shared, because the state is behind a one-word location.
- Today's per-handler copies (`f__h`, SPEC §18) become R2b specialisations, chosen by the same
  heuristic.

**R2e. Captures, linearity, and re-lending to an aborting site.**

- **Does `withbor3U` re-lending still work with a closure value? Yes, given the environment is a
  separate `Mut` location.** `h` reborrows `Mut 'l Env_c` per site entry with `withbor3U`. An abort
  ends the reborrow, and `h` has `Mut 'l Env_c` again (`withbor3U_compatX`).
- **It does not work if the captures are inside the thunk.**
  - A thunk `U(A ⊸ …)` that captures a `Mut` borrow is linear, so it can be forced once.
  - `!U` cannot capture it: `bangThunkV` asks `Persistent Γ`, and `lam_bang_persistent` at the
    paper level.
  - So a callback called more than once, with linear captures, must carry them in an environment
    passed beside the code: SPEC §2's `FnMut` row.
- **It does not work if the environment is passed by value and handed back.** An abort of the
  callee's call abandons it: its owned parts are dropped and its borrows end. That is the
  unwinding `[let]`/`[then]`'s meaning.
  - So the environment must be behind a location exactly when `h` serves an abortive provided
    operation and may call `f` after it.
  - Otherwise it may be threaded by value, with no cell.
- **Capture linearity is checked by the unchanged checker.** A callback that consumes an owned
  capture is a `U` thunk (one use), and `h` may call it once.

### 5.3 Site freshness (R3), the escape check (elaborator only, decision 57)

At each site `hnd (n, H) e` with context `Γ₂`, result `F_Σ R`, and the handled effect's operation
types `E`, the name `n` must not occur **free** in:

- the type of any slot of `Γ₂` the body uses;
- `R`;
- the operation types of `Σ`;
- `E`.

A port's occurrence as the **provided** part of a computation parameter's or stored callback's
type is bound, not free.

- **Origin.** Zhang & Myers, `[t-down]`: "the label ℓ must not occur free in the result type T and
  effects e. Otherwise, ℓ could outlive its binding scope." `Γ₂` is added because our names are
  static literals, in scope everywhere.
- **It is an abstraction property, not a safety one.** `effHandle` is sound without it
  (`handle_compatC`), so the FP holds either way.
- **The kernel.** It may move into `effHandle` later as a pure restriction of the rule, with
  `handle_compatC` unchanged.

### 5.4 `|>` (R4)

- `e |> g(a, …)` is `g(e, a, …)` (decision 50).
- When `g` is a handler, it is `with g(a, …) { e }`.
- When `g`'s first parameter is a computation parameter, `e` is that argument.

### 5.5 Second-class callbacks (R5)

- **The rule.**
  - A computation parameter may be called, or passed at a computation parameter.
  - It is not stored, returned, captured by a stored closure, or bound to a value.
  - A closure literal that captures it and is itself passed at a computation parameter is still
    second class.
- **Its reading: a borrowed thunk.**
  - `h` holds a borrow of the callback's environment for the duration of the call (R2a's
    `Mut 'l Env_c`).
  - The creator owns it, below `h` on the stack.
  - This is `HandlersAsBorrows`' encoding of Ξ's blocks: "a block receives the environment at
    each call instead of capturing it" (`x_sharedUnit`). It is why two callbacks may use one
    stateful capability: each borrows it from the creator's environment in turn. That is
    `sharedUnit_safe`'s shape, not `twoBlocks_refused`'s.

### 5.6 Stored callbacks (R6)

A stored callback is a closure value that reaches data, a cell, a returned value or a collection.
Its type, in the kernel:

    [@c] !U(∀'l₁ … 'l_k. Mut 'l₁ S₁ ⊗ … ⊗ A ⊸ F_{p₁:E₁, …} (Mut 'l₁ S₁ ⊗ … ⊗ B))     (many uses)
    [@c]  U(∀'l₁ … . …)                                                                (one use)

1. **Captures.** A many-use stored callback captures only persistent values: `!` today, data and
   `Imm` once promotion is widened (#9, T6; `bangThunkF_compatG` in `experiments/Grades`). A
   one-use one captures anything. A stored callback has no lent environment: nothing it was given
   outlives the storing.
2. **Lifetime-bounded capture.** It is boxed at a lifetime `@c` that each captured borrow outlives
   (`boxI`, with `CtxOutlives`; `box_lolli_outlives_iff`, `crossProg`).
3. **No stateful capability is captured** (`not_sharedCapture`, and promotion). The answering
   effects of its row are passed in by its caller (R2d), with the handler fixed by the stored
   type. The hidden-state object (Option 3, `dyn`) is deferred until a heterogeneous registry
   needs it (decision 57).
4. **Control effects are ports**, fixed by the stored type, one per type declaration (per
   instance of a generic one).
5. **Serving a port.**
   - The `with` of `E` around a call of a stored callback (directly, or through the rows of the
     calls between) takes the name `p_E`. Rows are inferred before sites are named (`rowC`).
   - Two ports of one effect under one site are rejected. The general fix is `rename` (below).
   - Nested sites of one name type today: an inner `hnd p`'s result row lacks `p`, and `effSub`
     restores it for the outer body.
6. **Collections** of callbacks with different rows take the union, by `effSub` on each body.

**`rename` (Open; Frank's adaptor).**

- **Step:** `rename(p,m) K[perform (p, v)] ↦ y ← perform (m, v); rename(p,m) K[y]`.
- **Rule:** `e : F_{p:E, Σ} A ⊢ rename (p, m) e : F_{m:E, Σ} A`.
- **Cost:**
  - one primitive;
  - one compatibility lemma, by induction on `ewpTS` like `handle_compatC`'s forwarding case;
  - the unique-decomposition and determinism cases of one new frame.
- **What it would make unnecessary:** R2c's required inlining, and the rejection of two ports
  under one site.

### 5.7 Named instances (#155)

- A named instance in `P` (`body: () -> A with a: Kube, b: Kube`) is two provided instances, with
  two ports or two capability arguments.
- Tunneled named instances are resolved where the argument was written.

### 5.8 What is copied, and why

The first version of this design copied a function per (callback, assignment), and called that a
code cost. It is three separate things.

**(1) Instances per assignment of names: typing, not code.**

- Two instances of `h` that differ only in the names of the sites and ports serving its effects
  have derivations that differ only in name literals. Their code differs in three places:
  - the key `(n, i)` a `raise` puts in its payload;
  - the name a `catch n` compares;
  - the variant of a suspension's payload.
- **Sharing the code (hypothesis, for the backend).**
  - A body's own sites and ports are the body's own constants.
  - Its own-row operations (served by its caller) are relabelled at the call boundary. That is a
    retag of `inr p` in the arm that already branches, and of the outcome's variant on the suspend
    path.
  - Tunneled operations pass through the body unexamined, except at a `catch` of the body's own
    name, which compares against its own constant.
  - So one code serves every name assignment. **Exception:** when a tunneled name equals one of
    the body's own names (§6.2), a renamed instance with its own constants is needed.
- **Checking once: the renaming lemma (hypothesis, §9.2).**
  - `CDerives` is equivariant under an injective renaming of operation names that fixes `0`.
  - So the checker derives an instance once, and every instance that differs by names follows by
    renaming, with no re-derivation.
  - Inlining (R2b) is also a renaming: the port `p_E` becomes the serving site's name.

**(2) Copies per callback: an optimisation.**

- **The default.** One body per (function, profile of `T`), with each callback a closure value.
  - The **profile** changes code: whether `h` branches after calling `f` (abort); whether `h` is a
    state machine (suspension); whether `h`'s context across the call must be persistent
    (multi-shot); and the drop glue around the call.
  - The **shape** of `T` within a profile does not change code: tunneled answering effects are in
    `Env_c`; tunneled control operations pass through; the payload variant is program-wide.
- **Typing per shape.** Instances that differ in `T`'s shape but not its profile are still
  separate typing instances, because the kernel has no row variable. A row-extension lemma (§9.2,
  item 3) would remove them. It is a hypothesis, and harder than renaming.
- **Specialisation per callback** (R2b) is chosen by a heuristic. It is required only by R2c's
  resuming case.

**(3) Answering effects: no copies.** A capability is an argument (R2d). Typing instances per
state type remain, as a typing artefact.

## 6. Accidental handling

### 6.1 The claim

> `retry`'s own `Fail` handler does not catch a `Fail` that the callback performs for its
> creator.

- The callback's provided `Fail` is at retry's port `p`, served by retry's site `p`.
- An unrelated `Fail` is tunneled, at the creator's name `m`.
- So the question is whether an operation at `m` can be caught by a site of retry. The general
  form is Zhang & Myers' `map` with an internal handler (their §1).

### 6.2 Where static names suffice (hypothesis, with the argument)

`Head.hop` catches at the **nearest** `hnd (m, …)`. So a tunneled operation at `m` is mis-caught
only if another `hnd (m, …)` lies between it and the instance its code was resolved to. Name that
configuration **N(m)**.

1. **A body's own names are not its callbacks' tunneled names, except on a collision.**
   - The names of `h`'s own sites and ports are fixed at `h`'s declaration.
   - A callback's tunneled names are those of the sites around where it was written.
   - They coincide only if the callback was written inside an instance of `h`'s own site (or
     inside code called from it), and is passed back into `h`.
   - **Rule:** the instance of `h` for a callback whose tunneled row mentions one of `h`'s own
     names is **renamed**: injectively, to fresh names, with its own code. R3 checks this: without
     the renaming, the call's `Γ₂` would mention the name free.
2. **A stored or returned value cannot carry a name out of its site** (R3). This is the case of a
   closure run under a later instance of the same site: the next turn of a loop, or the next call.
3. **Reified continuations do not count.** A suspended instance inside `κ` is not on the stack,
   and resuming `κ` reinstalls its own `hnd` (`kappa`).
4. **Renaming terminates** when the program has no recursion through a site whose callback tunnels
   that site. Each renamed instance is made at a call written outside the instance being renamed.

**So, by this argument:** with R3 and rule 1, every operation is handled by the instance its code
was resolved to. The provable core is §9.2's uniqueness lemma.

### 6.3 Where it fails: recursion through a site (rejected, decision 57)

- **The pattern.**
  `fn walk(t, f: () -> 1) = with to_result { f(); for c in children(t) { walk(c, { raise(e) }) } }`
  - Each level's callback raises to the previous level's site.
  - Rule 1 asks a renamed instance per level: polymorphic recursion over names.
  - With `rec` as an operation (decision 24), R3 rejects it: the operation's argument type
    mentions the site's name in its outer row.
- **To accept it** needs generative labels: Biernacki et al.'s labels by night, behind T2 (#173).
- **Stage 3 (`rec`) must add a corpus program of this pattern:** a recursive-descent parser with a
  per-level error handler whose callback raises to an outer handler. #173 is raised only if that
  pattern bites (decision 57).
- I have not built these configurations in Lean.

### 6.4 Comparison

| system | how `map`'s internal handler is kept from catching the callback's effect |
|---|---|
| Koka | it is not: `mask` by hand, or named handlers |
| Effekt / System C | capabilities: the callback holds the creator's capability |
| Zhang & Myers | generative labels; a label must not escape its binder |
| Biernacki et al. | effect variables bound by the handler; labels at run time |
| **here** | static names: a body's own, and its callbacks' tunneled ones; R3; a renamed instance on a collision; generative labels only behind T2 |

## 7. Higher-order effects: out of scope (decision 57)

Each scoping construct is a function over a passed computation that installs ordinary handlers:

| construct | as a function over a computation |
|---|---|
| `catch(M, h)` | `M |> to_result`, then a branch |
| `local(f, M)` | a `Reader` handler at `f(ask())` around `M` |
| `retry(n, M)` | target 1 |
| `timeout(d, M)` | a handler of `M`'s provided `Wait` that forwards each `wait` and cancels `κ` at the deadline; clock reads are a tunneled answering effect |
| `finally(M, D)` | `M then x. return x unwind D` |

- **Handler order.** The literature's concern (Wu et al.) is that a construct's meaning depends
  on handler order. Deep handlers with explicit order give both answers (SPEC §19 program 1).
- **Reinterpreting a construct.** What a function cannot do is let an outer handler choose the
  construct's meaning, as an elaboration in hefty algebras does. The way to get that is to make
  the construct's primitives effects. A test harness serving `Clock` changes what `timeout` does.
- **An operation that takes a computation** needs a clause polymorphic in the body's row: rank-2
  row polymorphism, Option 1. It is out of scope.

## 8. Interactions

- **#172 (T1).** A callback's **non-abortive** control operation inside a `borrow` block whose
  handler is outside is T1. It is rejected as today: `Row.Unwind` admits only abortive operations.
  Answering and abortive operations cross. R2e's re-lending uses the unwinding borrows, under the
  same rule.
- **#215.** `retry` drops the error of a failed attempt: an ordinary destructor once payloads may
  be linear. The last error propagates.
- **#216.** The retry above needs none. A `default`-style handler over a passed computation needs
  #216, as `default` does today.
- **Multi-shot.** An unrestricted operation's `[let]` asks `!Γ₂` (`effLet`'s `hU`).
  - `h`'s body across a call of a callback whose profile is multi-shot must hold only persistent
    values. That is a separate code profile (§5.8).
  - A lent environment `Mut 'l Env_c` is not persistent. So a callback that may perform a
    multi-shot operation is passed with a persistent environment (`!` captures), or is inlined
    with persistent captures (`lam_bang_persistent`'s rule, now on the instance).
- **Divergence and generators.**
  - A callback that loops makes `h`'s profile suspending (a `Loop_Σ` body).
  - Stored generators over a row (SPEC §15 Open) would be R6 applied to `pull`'s observations.
    Not designed here.
- **Answering effects inside clauses** (SPEC §18 *Not provided*): unchanged.

## 9. What the proofs need

### 9.1 Kernel

**No new rule, no relation change, no FP change.** Every elaborated program is checked by today's
checker. The following carry over unchanged:

- `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD`;
- every compatibility lemma, including `handle_compatC`, `let_compatC`, `then_compatC`,
  `withbor3U_compatX` and `boxI_compatC`.

**For stored callbacks that capture data:** #9 (T6), `bangThunkF_compatG` promoted into `Core/`.

**Optional:**

- R3 as a side condition of `effHandle`: a restriction, so `handle_compatC` is unchanged
  (decision 57 keeps it in the elaborator);
- `rename` (§5.6).

### 9.2 Lemmas (statements; none is proved)

1. **Uniqueness of resolution** (§6.2), on `Paper/`'s machine.
   - Let `NoNest m K` say no frame `hnd (m, _)` of `K` lies under another frame `hnd (m, _)` of
     `K`. If `K = K₁[hnd (m, H) K₂]`, `K₂.HasHnd m = false` and `NoNest m K`, then
     `K₁.HasHnd m = false`.
   - Proof: induction on `Kont`. It uses no relation and no inversion.
   - Its use: with an invariant over the elaborator's output, tested by the corpus and the `call`
     reports.

2. **Renaming** (the checker derives once and instantiates).

   **Statement.** Let `π : UInt32 → UInt32` be injective with `π 0 = 0`. Let `π` act on:
   - `OpSig` (`o.n ↦ π o.n`), `Row`, `VTy` and `CTy` (at `.eff` only);
   - `Expr`, at the name positions of `opArgE`, `hndTerm` and the `raise`/`perform` forms only, and
     at no other integer literal;
   - `Ctx` (slot types) and `Jdg`.

   Then

       CDerives Δ Γ e j → CDerives Δ (Γ.ren π) (e.ren π) (j.ren π)

   **Why it should hold** (hypothesis: equivariance, names as atoms in the nominal sense):
   - In a derivation, names are only compared for equality (`Row.find`, `effHandle`'s `hnS`,
     `Row.Uniq`) and with `0` (`effHandle`'s `hn0`, `Row.NZ`). Both are preserved by an injective
     `π` fixing `0`.
   - Every other premise inspects types without looking at names.
   - `0` is fixed because it is the reserved cancel name (`⊥`) of `Head`'s cancel steps.
   - **It needs no R3**: renaming is pure syntax. An injective `π` preserves R3.
   - The proof is a forward induction over the 88 rules, as `CDerives.append_dead` is, not an
     inversion.

   **What it must commute with** (each a small lemma):
   - **rows** (`Core/EffRules.lean`, `Core/Types.lean`):
     - `CTy.effOf`, with `(effOf S R).ren π = effOf (S.ren π) (R.ren π)`;
     - `Row.find`, with `Row.find (S.ren π) (π n) i = (Row.find S n i).map (·.ren π)`, which needs
       injectivity;
     - `RowLe`, `Row.NZ`, `Row.Uniq`, `Row.Weak`, `Row.Unr`, `Row.abortOnly` and `OpSig.abort`;
     - `Row.ofEff`, `clausesTy` and `retTy`;
   - **the unwinding borrows** (`Core/EffBorrow.lean`): `Row.Unwind`, and the unwinding borrows'
     types (`withbor3UTy` and its siblings);
   - **terms**: `hndTerm`, `opArgE`, `thenE`, `withborUE`;
   - **type functions in rule conclusions**: lifetime substitution, `unfoldTy` and `ν`'s
     instantiation, the folds' types, the array and slice constants' types;
   - **type predicates that must be invariant**: `Drop`, `Persistent`, `CtxOutlives`, `Cl`,
     `NuOk`, `EffLeaf`, `EffFree`, `isRet`, `Ctx.Drops`, and the destructor class.

   **Cost (hypothesis).** The size of `Core/Weaken.lean` (172 lines) plus one commutation lemma
   per type function above. It is dominated by the type functions, not by names.
   - The lemma has no consumer in the relation: `ewpTS` is not involved.
   - A semantic version (`cC` invariant under renaming of the table) is not needed, because the
     FP applies to each renamed derivation.

3. **Row extension at a fixed profile** (removes typing instances per shape of `T`).

   **Statement (hypothesis, and harder).** If `h`'s instance is derived with a tunneled row `T`,
   then it is derivable with `T′` whenever:
   - `T′` has the same profile as `T`;
   - `T′`'s names are fresh for the derivation;
   - `T′`'s operation types satisfy the same predicates (`Drop`, closedness for `Row.Unwind`).

   This is row polymorphism as a meta-theorem over `CDerives`, not as a kernel former, so it does
   not touch decision 19. Not needed for correctness: without it, the checker derives one instance
   per shape.

### 9.3 Laws (optional, as SPEC §18's `op_tail`, `handle_fold`)

**Specialisation is meaning-preserving.** For a known `c`, R2b's copy and R2a's call
`h (code_c, &mut env_c)` reach the same answers and memories at every host. This is a β-law
over `ewpTS` (`ewp_bind_pure_frame`, the `[let]` frame) composed with the renaming lemma.

## 10. Lowering

| piece | lowering | cost against hand-written |
|---|---|---|
| a callback, default (R2a) | a defunctionalised closure value: a tag and a pointer to its environment; a call is direct when the flow finds one code, otherwise a `switch` | no heap allocation for the value; its environment needs one cell when re-lent to an aborting site (R2e), otherwise none |
| a callback, specialised (R2b) | inlined; captures are parameters | 0 allocations, 0 dispatches: Rust's monomorphised closures |
| a provided abortive operation | branch per call; the port's site a `catch` | the `Result` program's |
| a provided resuming operation | state machine; a tail-resumptive clause known per instance is a direct call (SPEC §19) | as today |
| a relabelled port (R2c, abortive) | a retag of `inr p` in the arm that already branches | none on the normal path |
| a tunneled operation | passes through | as today |
| an answering effect (R2d) | an argument: a location and a clause; a direct call when the flow finds one handler | none when the flow finds it; a `switch` otherwise |
| a stored callback | a closure value; one allocation at creation when it captures; an indirect call | Rust's `Box<dyn Fn>`, and `Box<dyn Future>` when it suspends |
| code size | one body per (function, profile); inlined copies by the heuristic; renamed instances on collisions | hypothesis: Rust's or less |

**The one cost Rust does not pay:** the environment cell of a default (un-inlined) callback
re-lent to an aborting site.

- Rust passes `&mut F` to a frame on the stack.
- Here a cell is a heap allocation (`Backend/README.md`, *Cells*).
- Two ways out: inlining (R2b), or a backend lowering of a call-scoped cell to a stack slot.
  Neither is designed here.

**No run-time handler search is added.** Names stay static, and ports are static names.

## 11. Decisions (the user's, 2026-10-01; decision 57)

1. **Option 2.** No row variables in the kernel. A function type states only what the callee
   provides.
2. **The provided/tunneled split**, with the provided row written on the parameter.
3. **R3 is in the elaborator only.** It is an abstraction property, not a safety one, so the FP
   holds either way. It may move into the kernel later as a pure restriction of `effHandle`.
4. **Recursion through a site is rejected for now.** Stage 3 (`rec`) must add a corpus program of
   that pattern: a recursive-descent parser with a per-level error handler whose callback raises
   to an outer handler. #173 is raised only if the pattern bites.
5. **Stored callbacks use ports, with capabilities passed by the caller.** The `dyn` object with a
   hidden state is deferred until a heterogeneous registry needs it.
6. **Operations that take computations are out of scope.**
7. **Spellings stay provisional.**

**Still open** (not decided):

- the inlining heuristic;
- whether to build `rename` (R2c, §5.6) or keep inlining required in R2c's resuming case;
- whether to build the renaming lemma (§9.2, item 2) before the surface work, or check every
  instance meanwhile;
- a stack lowering of call-scoped cells (§10).

## 12. Proposed rewrite of #161's body

> **Effects S4c: functions over effectful computations (effect polymorphism, stored callbacks)**
>
> Design: `docs/effect-polymorphism.md`; decision 57. No kernel change.
>
> **Mechanism:**
> - No row variables in the kernel. A computation parameter's written row is what the callee
>   provides (its control effects at **ports**, static names fixed by the parameter); everything
>   else tunnels to the handlers where the argument was written.
> - **One body per (function, profile of the tunneled row).** A callback is a defunctionalised
>   closure value whose environment is lent (`Mut`), re-lent per entry to an aborting site
>   (`withbor3U`). Inlining a known callback is an optimisation chosen by a heuristic, required only
>   for a provided resuming effect the callee passes on (until `rename`).
> - Answering effects are capability arguments: no copies.
> - Site freshness (R3, elaborator only); a renamed instance when a callback tunnels a callee's own
>   name; recursion through such a site rejected.
> - `|>` at a computation parameter or a handler (decision 50).
> - Stored callbacks: `[@c] !U(∀'l. Mut 'l S ⊗ A ⊸ F_{ports} (…))`, persistent captures (#9),
>   capabilities passed by the caller, ports served by the `with` around the call.
>
> **Acceptance:**
> 1. `retry` over a computation that captures a lend, re-run after an abort, with one body.
> 2. `run() |> to_result`, and `report(body)`.
> 3. `corpus/pending/yield-callback.bc` runs.
> 4. An event registry and a manager of reconcile functions, stored, dispatched with the caller's
>    `Log` capability and a `Fail` port.
> 5. The north-star chain, once `Wait` (#52) and stage 3 of #188 exist; until then without
>    `timeout`.
> - A higher-order function with an internal `Fail` site does not catch a callback's `Fail` to its
>   creator (a corpus program and its `call` report).
> - Rejects with messages:
>   - recursion through a site with a tunneled callback;
>   - a name escaping its site;
>   - a second-class callback stored;
>   - two ports of one effect under one site;
>   - a non-abortive operation of a callback across a borrow (#172).
> - Counts at parity with the hand-written programs when inlined. A code-size column: one body per
>   profile when not inlined.
> - Proof: the uniqueness lemma; the renaming lemma (so the checker derives once); #9 for stored
>   captures.
>
> **Open:**
> - the inlining heuristic;
> - `rename` (Frank's adaptor);
> - row extension at a fixed profile;
> - a stack lowering of call-scoped cells;
> - generative labels (T2, #173) if the stage 3 pattern bites;
> - the `dyn` capability object;
> - stored generators over a row.
>
> Depends on #9, #52 (`Wait`), #188 stage 3. Related: #155, #172, #215, #216. Part of #18.

## Sources

- Zhang & Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019,
  https://cs.uwaterloo.ca/~yizhou/papers/abseff-popl2019.pdf (read: abstract, §§1, 3, 4.2–4.3).
- Biernacki, Piróg, Polesiuk & Sieczkowski, *Binders by Day, Labels by Night*, POPL 2020,
  https://dl.acm.org/doi/10.1145/3371116 (abstract).
- Xie, Brachthäuser, Hillerström, Schuster & Leijen, *Effect Handlers, Evidently*, ICFP 2020,
  https://www.microsoft.com/en-us/research/publication/effect-handlers-evidently/ (abstract).
- Xie & Leijen, *Generalized Evidence Passing for Effect Handlers*, ICFP 2021,
  https://dl.acm.org/doi/10.1145/3473576.
- Brachthäuser, Schuster & Ostermann, *Effects as Capabilities*, OOPSLA 2020; Brachthäuser,
  Schuster, Lee & Boruch-Gruszecki, *Effects, Capabilities, and Boxes*, OOPSLA 2022,
  https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects/ (abstract).
- Schuster, Brachthäuser & Ostermann, *Compiling Effect Handlers in Capability-Passing Style*, ICFP
  2020, https://dx.doi.org/10.1145/3408975 (abstract); *From Capabilities to Regions*, OOPSLA 2023,
  https://dl.acm.org/doi/10.1145/3622831 (title).
- Convent, Lindley, McBride & McLaughlin, *Doo Bee Doo Bee Doo*, JFP 2020,
  https://www.cambridge.org/core/journals/journal-of-functional-programming/article/doo-bee-doo-bee-doo/DEC5F8FDABF7DE3088270E07392320DD
  (abstract).
- Tang, Hillerström, Lindley & Morris, POPL 2024; van Rooij & Krebbers, *Affect*, POPL 2025:
  `experiments/HandlersControl` §3.
- Tang, White, Dolan, Hillerström, Lindley & Lorenzen, *Modal Effect Types*, OOPSLA 2025,
  https://dl.acm.org/doi/10.1145/3720476 (abstract).
- Wu, Schrijvers & Hinze, *Effect Handlers in Scope*, Haskell 2014,
  https://people.cs.kuleuven.be/~tom.schrijvers/portfolio/haskell2014.html (abstract).
- Bach Poulsen & van der Rest, *Hefty Algebras*, POPL 2023, https://dl.acm.org/doi/abs/10.1145/3571255
  (abstract).
- Lindley, Matache, Moss, Staton, Wu & Yang, *Scoped Effects as Parameterized Algebraic Theories*,
  ESOP 2024, https://arxiv.org/pdf/2402.03103 (abstract).
