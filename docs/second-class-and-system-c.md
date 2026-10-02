# Second-class closures, System C, and capability-indexed prompts

A theory spike for #229, #216 and #161. Experiment: `experiments/SecondClass/` (non-default
library `SecondClass`, imported by nothing). It changes nothing in `Core/`, `Frontend/` or
`Backend/`.

**Status.** §8's step 1 is built: SPEC §21, decision 59. Recursive groups are generators called
directly, layers transform them, abortive clauses run after the handler and a handler whose
operations resume has a state. Not built from step 1: a recursion whose body loops (its
`Exhausted` would be performed inside a loop, and a handler around a div computation is not
provided) and a native handler parameter in the lowering.

**How claims are marked.**

- **[Lean]**: a theorem in `experiments/SecondClass/SecondClass/`. Axioms are within
  `[propext, Classical.choice, Quot.sound]`, with no `sorry`.
- **[checker]**: a hand-written core program in `experiments/SecondClass/probes/`.
  - `bcc check` accepts it. The checker is certifying: a success carries a `CDerives`
    derivation (`Frontend/Check/Checker.lean`).
  - It also runs to the stated answer, with `live 0`, at the source, `clos` and `flat` stages
    and compiled to WebAssembly (`bcc run`).
- **[inspection]**: read off the rules or the code, with no proof.
- **[hypothesis]**: not checked.

---

## 0. Answers

1. **Capability-indexed prompts, the primary question (§2).**
   - **What they close.** Indexing native capture by a prompt variable bound at the handler
     closes the apparatus of decision 57: copies per assignment of names, ports and R3.
     Generative names would add recursion through a site.
   - **The semantic side is checked [Lean].** Handling at a name chosen at run time is sound in
     the existing relation, provided the name is fresh for the prompts in scope
     (`handleAt_compatC`). `handle_compatC` uses the static name only for that freshness.
   - **What is missing.** Two things, neither built:
     - a machine step that generates names;
     - name variables in rows, read by the relation through a map from name variables to names.
   - **What they do not close.** #229, #216, loops in recursion, members' result types, or
     effects under `deep`.
   - **Watch item (1), recursive types through `⊸`/`U`.** The design does not lean on it as
     long as tables are computed from types. The System C-faithful variant does: it drops rows
     and keeps protocols in the world, which needs higher-order state in the Kripke world. Do
     not take that variant (§2.6).
2. **The gaps are not one family (§1).** The hypothesis "every gap is a `!`-closed effectful
   value" is only partly right:
   - **Two gaps are as hypothesised:** #216's clause captures, and an answering capability in a
     recursion.
   - **Two are caused by the `rec` site,** not by `!`:
     - resuming operations in a recursion: the site's clause cancels its continuation at a row
       with resuming operations;
     - loops in a recursion: the step's body runs under the site's handler.
   - **One comes from the group's shape:** members with different result types.
   - **Two are separate:** effects under `deep`, and generic recursion.
3. **What closes most of them (§3).** One principle with two forms, and no kernel change.
   - **The principle.** Effectful code is `!` code. Its environment is passed at each call: a
     component of the argument, a handler's parameter, or a lent `Mut 'x Env`. It is never
     captured by the code.
   - **First form, for recursion.** A recursive group is the bounded fixed point of a
     *generator*, called directly, at a record type. Cook and Palsberg's account: objects are
     fixed points of generators.
   - **Second form, for clauses.** A clause either receives its environment through the
     handler's parameter (resuming operations), or runs after the handler with its captures
     outside (abortive operations).
   - **Evidence [checker].** Every probe program types in the kernel and runs compiled. The
     elaborator change is not built.

   | gap | closed by | status |
   |---|---|---|
   | answering effect in a recursion | the passed environment | [Lean] `recLog_derives`; [checker] P1 |
   | resuming operation in a recursion | direct self-calls (no `rec` site) | [checker] P2, compiled: 6 allocations, 0 indirect calls |
   | loop in a recursion | direct self-calls at a loop type | [checker] P3 |
   | members with different result types | a fixed point at a record of functions | [Lean] `boundedFixRec_compatX`; [checker] P6 |
   | recursion through values | groups are SCCs of references already; then #161 | [inspection] |
   | #216 clause captures | abortive clauses: run after the handler; resuming clauses: the handler's parameter | [Lean] `d_handleAbortCapture`; [checker] P4 |
   | #161, effectful callbacks | R2a is already this principle | design only (`docs/effect-polymorphism.md` §5.2) |
   | effects under `deep` | not closed: a per-row `deep`, and T1 for borrowed capabilities in its frames | separate |
   | generic recursion | not closed: instantiate, then group | separate |
   | decision 57's copies, ports, R3 | not closed by this principle; closed by §2's prompt variables | design |

   So **one principle closes five of the eight listed gaps** at elaboration. A sixth (#161) is
   already designed this way. Two are separate.
4. **System C (§4).** System C accepts two blocks sharing one stateful capability because its
   operations transfer control to the handler, which owns the state.
   - `twoBlocks_refused` belongs to the answering encoding, where the capability *is* the state.
     It is not caused by linearity.
   - With a control operation and the state as the handler's parameter, P5 types System C's
     program and runs it [checker].
   - What is essential is narrower: a shared token cannot carry state in direct style
     (`experiments/HandlersControl` §1).
5. **The missed trick (§5).**
   - **Not a missing construct.** It is closure conversion at the seams: pass the environment
     to `!` code instead of asking for an effectful `!` closure.
   - **Prior work already had it.** SPEC §2 (the `FnMut` row), HandlersAsBorrows (`EnvTy`),
     the generators' elaboration (the loop's state passed through `yield`) and R2a all use it.
   - **Where it was not applied.** Not to `bounded_fix`'s step, and not to handler clauses.
6. **Recursion (§6).**
   - **An ambient depth budget needs no new construct.** It is the budget passed down as an
     argument (P7).
   - **`bounded_fix` stays the only knot.** Totality (`total_no_infinite_run`) excludes Landin's
     knot.
   - **The fixed point at a record** is covered by `boundedFix_compatX` as proved. The `rec`
     site should be replaced by generator transformers (P8).

---

## 1. The gaps, diagnosed

**Where each gap is rejected.** Each is a rejection in `Frontend/Elab/Effects.lean`
(`defineGroup`, `copyFor`, `deepCopy`) or SPEC §18–§20.

### An answering capability in a recursion (#229)

- **Rejected at:** `copyFor` and `defineGroup`, with "is recursive and uses the capability of
  …: not provided".
- **Cause [inspection]:**
  - the group's step is `!U(…)`, a top-level `def`, so it cannot capture the capability;
  - the elaborator does not pass the capability through the step's argument.
- **The kernel already accepts it.** `bounded_fix[A, C]` holds at every `A`, so
  `A = Mut 'h S ⊗ A₀` with `C = F(Mut 'h S ⊗ B)` is an instance:
  - `boundedFixEnv_compatX` [Lean];
  - `recLog_derives` types such a recursion, and `recLog_sem` is its soundness [Lean].

### A resuming operation in a recursion (#229)

- **Rejected at:** `defineGroup`, with "a recursion's continuation is cancelled at an abortive
  row only".
- **Cause [inspection].**
  - The group's calls of itself are a `rec` operation at a site of the group's own.
  - The site's clause is `b ← force f a unwind κ.cancel; κ.resume b`.
  - `[then]`'s finaliser must be at `F_{Σ^abort} 1` (`CDerives.effThen`, `hD`).
  - `κ.cancel : F_Σ 1`, and `Σ` holds the resuming operation.
- **The cause is not `!`.**
  - Without the site, the step calls its self-reference directly: `case self { inj₁ _ ⇒
    exhausted () | inj₂ f ⇒ f a }`.
  - P2 is that recursion. It yields before and after its call of itself, raises `exhausted`
    when the budget is spent, and is handled by a non-tail-resumptive clause [checker].
  - It compiles: 6 allocations, 0 indirect calls.

### A `while`/`loop` in a recursion (#229)

- **Rejected at:** `defineGroup` (`hasWhile`).
- **Not the stratification.** `bounded_fix` is stated at every computation type, a loop type
  among them. P3 instantiates it at `C = F(U(loop i32 1))` [checker]:
  - each level runs a loop of `n` observations, then the next level's loop by `div_bind`;
  - `div_fuel` drives the whole loop.
- **What the recursion is.** Its depth is bounded, and the loop it builds may diverge, which is
  what its type says.
- **Likely cause [hypothesis].** The same as the last: the step's body runs under the `rec`
  site's handler, and a div body's state machine (SPEC §15) would have to cross that handler's
  frame. P3 has no site.
- **Cost.** P3 uses nested `div_bind`s: 102 allocations, 35 indirect calls. The elaborator would
  build one state machine per body instead (SPEC §15), as it does for every div body.

### Members with different result types (#229)

- **Cause [inspection].** A group is one `bounded_fix[A, C]`: the members' arguments are a sum
  and their answers one `C`.
- **The fix.** Take the fixed point at a record of functions, `C = &ⱼ (Aⱼ ⊸ Cⱼ)`, `A = 1`
  (Bekič). `boundedFix_compatX` already covers it: it is proved at every `C`
  (`boundedFixRec_compatX` [Lean]).
- **P6** is mutual recursion between `ev : i32 ⊸ F(1 ⊕ 1)` and `od : i32 ⊸ F i32` [checker].
  - A call of a member forces the self-reference and projects.
  - It compiles with 0 allocations and 0 indirect calls.

### Effects under `deep` (#229)

- **Rejected at:** `deepCopy`, with "a recursion that performs an effect is not provided under
  the heap driver".
- **Two causes, separate from the rest [inspection]:**
  - `deep` is one library definition at a pure `Loop B 1`. A row needs `Loop_Σ`, so `deep` needs
    a copy per row, as functions with rows get.
  - An answering capability in `deep`'s frames is a borrow held in a loop's state across
    observations. That is T1 (#172; `experiments/LoopBorrow`, `refoldKripke_false`).
- Not closed here.

### Generic recursion (#229)

- **Cause [inspection].** Groups are formed before generic functions are instantiated.
- **Fix.** Instantiate first, then group. Polymorphic recursion (an instance calling another
  instance) is not monomorphisable.
- Separate from everything else here.

### Recursion through values

- **Groups already span value references.** `recGroupsOf` takes strongly connected components
  of *references* (`refsV`), not only of calls [inspection].
- **So a value cycle is already a group.** A function that passes itself to a higher-order
  function, or callbacks that call back into their caller, form a group whenever the cycle runs
  through named functions.
- **Every recursion runs through a group or `ν` [inspection].** The kernel has no other knot
  (§6.5).
- **What blocks it: #161.** A member's row has `Exhausted`, so passing it as a value is "a
  function with a row passed as a value".

### #216: clause captures

- **Cause [inspection].** `[handle]` types each clause `!` (`clauseTy`, `retTy`).
  - `handle_compatC` relies on it: a clause is run at a later world, and it is valid there only
    because it holds `∅` (`clausesTy_empty`, `ext_empty'`).
  - The machine relies on it too: `[op]` copies `H` into `κ`, so a clause's captures would be
    duplicated.
- **The kernel already admits both cases (§3.2):**
  - an **abortive** operation never copies `H` (`[unwind]` runs `h_op v` once), so its clause
    can run after the handler;
  - a **resuming** operation's clause can take its environment from the handler's parameter.

---

## 2. The primary question: capability-indexed prompts

The proposal is Effekt's design.

- `hnd` introduces a fresh prompt and lends a capability for it, with a lifetime, to its body.
- `perform` takes that capability.
- Escape, polymorphism and accidental handling then come from lexical capability values, not
  from static names, rows and R3.

### 2.1 What the relation already does [Lean]

`ewp_handle` (`Core/EffRules.lean`) is stated at an arbitrary name `n` and two operation tables.
Its only premise relating them is `Tin m i = Tout m i` for `m ≠ n`, and it does not ask for
`n ∉ Tout`. So shadowing is semantically safe: the machine picks the nearest `hnd n`, and the
table follows.

`handle_compatC` uses the static literal in one place, `hnS : ∀ o ∈ Σ, o.n ≠ n`. That premise
rules out an operation of the outer row at the handler's name, at an index the inner effect
lacks. `SecondClass/Prompts.lean`:

- `PromptEnv` is the prompts in scope, each a run-time name with its effect, and `P.row` its row.
- `handleAt_compatC`: for every nonzero `n ∉ P.names`, a body sound at `(n, E) :: P` is handled
  soundly at `P`. The name enters only through freshness (`row_names`).
- `fresh_exists`: every environment of fewer than `2³² − 1` prompts has a fresh nonzero name.

So **the semantic core of a capability-indexed `hnd` is already proved, at whatever name the
run produces**. What is missing is (a) and (b) below.

### 2.2 What a capability-indexed `hnd` needs, and what it costs

**(a) A source of fresh names in the machine.**

- Names are `UInt32` values in `hnd`'s and `perform`'s payloads (`opArgE`, `hndTerm`), and no
  step produces one.
- The fresh name must be fresh for every prompt whose capability the body can hold.
  - Capabilities cannot outlive their handler's scope, so those are the handlers on the current
    stack [hypothesis, by the scoping argument of §2.3].
  - A head step cannot see the stack: `Head` is context-free, and `wpG_bind` relies on that.
  - So the supply must be global. Either:
    - a counter in the machine state, never reused, which gives persistent labels and suits
      multi-shot continuations; or
    - a cell allocated by `hnd` whose location is the name, freed when the `hnd` frame returns.
      A cell suits linear and affine continuations, since the frame and its `κ` own it. It does
      not suit multi-shot continuations, whose copies would share an owned cell.
- **Cost:** one primitive, plus its cases in unique decomposition and determinism (`head_det_eff`).
  - A counter changes `Heap`, which is the paper's machine state, or adds a component beside it.
  - Names as locations change `Head.hop`'s name type.
- **Not built.** I have not derived a fresh-name step and have not verified any obstruction to
  one.

**(b) Name variables in rows, read through a map in the relation.**

- `cC (F_Σ A) ls δ` reads its table from `Σ` (`Row.tab Σ δ`), whose names are literals.
- **The change.** A capability type `Tok ν` needs:
  - `CTy.eff`'s name to be a name variable or literal;
  - a binder `∀ν` (one compatibility lemma, of `allI`'s shape);
  - the relation to read `ν` through a map from name variables to run-time names, beside `δ`.
- **The token's value relation** is "the value is the name `ν` maps to". It holds `∅`, and it
  carries no protocol: the protocol stays in the row's table. So no recursion enters the
  relation (§2.6, item 1).
- **Cost.** The map is either:
  - a new argument of `cC` and `SemC`, which touches every lemma that states them; or
  - a component of `LSub`, which is the paper's substitution.

  Prompts could instead *be* lifetimes, with the run-time name read off the semantic lifetime;
  I have not checked that the machine's choice of name and the proof's choice of lifetime can be
  kept in step. Either way this is the large part. It is comparable to §19's original type-level
  work, not to a compatibility lemma.
- **Scoping replaces R3 [inspection].** A token's type mentions `ν`, and so does the row of any
  closure that uses it. So no value that can perform on `ν` is well-scoped outside `ν`'s binder.
  This is Zhang and Myers' `[t-down]` as scoping, and System C's "`σ at {f}` is not well-formed
  outside `f`'s binder". It does not use lifetimes at all.

  This matters, because a lifetime-bounded token captured by `!` code would be unsound in BoLo.
  `!T ⊐ @a` holds at every `@a`, and `[]E` unboxes `[@c] !U(…)` with no premise. That is the
  T2 former the kernel lacks (SPEC §19, *Why not generative names*).

### 2.3 What survives unchanged [inspection]

- **The continuation qualifiers, unwinding and decision C.** They live in the protocol table
  (`contShare`, `cancelOwed`, `errOk`, `cancelTab`), which is per name. It would be read at the
  name the map gives, so they carry over unchanged.
- **The persistent-capture rule for multi-shot continuations (watch item 2) stays intact.**
  - A token holds `∅`, so an unrestricted `κ` may capture it.
  - The `[let]` premise `S.Unr → Persistent Γ₂` is unchanged.
  - Nothing linear becomes copyable: the token is not a resource.
- **Accidental handling (watch item 3).** Lexical tokens solve it, as in Effekt. Static names
  already solve it except for recursion through a site (decision 57), and generative names
  solve that case too.
- **Shared mutable state and concurrency (watch item 4).** The design forecloses neither.
  - Generative names across threads need an atomic counter or a per-thread name space.
  - State behind control (§4) keeps each handler's state in its frame.

### 2.4 Three levels, and what each closes

| level | change | closes | cost |
|---|---|---|---|
| **L1: name variables** | rows keyed by name variables; `∀ν`; tokens as values; static names at sites | decision 57's copies per name assignment (one derivation per function, instantiated by `∀E` instead of the renaming lemma); ports (the port is the bound `ν`) | (b) |
| **L2: generative names** | L1, plus (a) | recursion through a site (a fresh prompt per level); R3 becomes `∀ν`'s freshness, discharged at run time | (a) + (b) |
| **L3: rowless, System C-faithful** | protocols stored in the world, keyed by prompt; `F A` carries only a profile (lin / aff / unr / abortive) for the `[let]` side conditions | tunneling for free: a callback's effects are its captured tokens, so higher-order functions need no row of the callback | **open problem, watch item 1**: the world would store predicates over worlds. Do not take it |

**Which listed gaps a capability-indexed design closes [inspection]:**

- **Closed:** decision 57's apparatus (L1); recursion through a site (L2); #161's tunneling, at
  L3 only.
- **Not closed:** effects in recursion, loops in recursion, different result types, effects
  under `deep`, generic recursion, #216.
  - Those are about how a step, a clause or a frame receives its environment, and are the same
    at any naming of prompts.
  - With tokens, a clause still cannot capture an outer token in `!` code without a scoped `!`.
  - The step of `bounded_fix` is `!U`, so it still takes tokens as arguments.

### 2.5 Lowering

- **Static resolution survives where provenance is known.** When the elaborator knows which
  `hnd` lent a token, which is nearly always, `perform` resolves statically as now:
  - an abort is a branch;
  - a tail-resumptive operation is a direct call;
  - a suspension is a state machine.
- **Unknown provenance costs an indirect call.** A token reaching code through a stored callback
  needs dispatch: a search of the handler stack by name, or evidence, where the token points at
  the handler's frame and an operation is an indirect call. Zero-cost is lost only there
  [hypothesis]. I have not checked which of these Effekt's LLVM backend (Muhcu et al., ICFP
  2025) uses.

### 2.6 Open-problem watch

1. **Recursive types through `⊸`/`U` without step-indexing.**
   - **L1 and L2 do not lean on it [inspection].** Tables are computed from the row's types
     (`OpSig.ent δ`), and a token's relation pins only its name. A token in an operation type
     needs no recursion in the relation: `Tok ν` does not mention its effect.
   - **L3 does lean on it.** A world that maps prompts to protocols is higher-order state in the
     Kripke world, whose usual treatment is step-indexing, which BoLo avoids.
   - **Native capture steps around `no_uniform_comp` already.** `κ`'s type is given by `[op]`,
     not by a recursive type, and nothing here reintroduces it.
2. **Linearity and multi-shot.** Intact (§2.3).
3. **Accidental handling.** Solved lexically (§2.3).
4. **Shared mutable state and concurrency.** Not foreclosed (§2.3).

### 2.7 The diagnosis, checked

The redirect's diagnosis is that every gap sits where an answering capability meets the control
machinery. That holds for the answering capability in a recursion, for #216 and for #161. It
does not hold for:

- P2: a recursion with a resuming *control* operation and no answering capability. Its blocker
  is the `rec` site's clause.
- P3: a loop with no effect.
- P6: result types.

So capability-indexing, valuable for decision 57, is not the construct behind #229 and #216.

---

## 3. The principle: `!` code with a passed environment

### 3.1 Recursion: the bounded fixed point of a generator, called directly

    bounded_fix[E ⊗ A, C] : !U(!U((1 ⊕ !U(E ⊗ A ⊸ C)) ⊗ (E ⊗ A) ⊸ C) ⊗ (I32 ⊗ (E ⊗ A)) ⊸ C)

**The restated step.**

- The step (the *generator*) is `!` code.
- The environment `E` is a component of the argument, handed back in `C` when the caller
  needs it. `E` holds the answering capabilities the group uses, a layer's state, and owned
  values the group threads.
- The self-reference is `!` code, called directly: `case self { inj₁ _ ⇒ exhausted () | inj₂ f ⇒
  f (e, a) }`.
- There is no `rec` site.

**Compatibility.**

- It is `boundedFix_compatX` at `A := E ⊗ A₀` (`boundedFixEnv_compatX` [Lean]). No new
  obligation.
- At a record, `C := &ⱼ(E ⊗ Aⱼ ⊸ Cⱼ)`, it is `boundedFixEnvRec_compatX` [Lean].
- `envStepTy_persistent` [Lean]: the step is persistent whatever `E` is, because `E` is not in
  its captures.

**Layers.** Decision 24's layers (`memo`, fuel, logging) are generator transformers, applied
before the fixed point (Cook and Palsberg 1989).

- P8 applies a counting layer to a generator that knows nothing of counting [checker].
  - The layer wraps the self-reference in `!` code that ticks a counter, then calls through.
  - The counter is the environment.
  - It compiles with 1 allocation (the counter's cell) and 0 indirect calls.
- A layer with state (a memo map) adds its state to `E`, so its type is
  `Gen(E ⊗ A, F(E ⊗ B)) → Gen(E' ⊗ E ⊗ A, F(E' ⊗ E ⊗ B))`.
- Transformers compose by function composition.
- At a record they act per field. I have not built that, but nothing in the record changes the
  shape of a field [inspection].
- This removes the `rec` operation's reason to exist. Its site was what intercepts calls, and
  intercepting is what a transformer does to the self-reference.

### 3.2 Handler clauses

**Abortive operations: the clause runs after the handler.** `[unwind]` runs `h_op v` once and
copies nothing, so:

    handle_n e with { return x ⇒ N_v ; op v ⇒ N_e }
      ≜  r ← handle_n e with (λx. inj₁ x, λv. inj₂ v);  case r { inj₁ x ⇒ N_v | inj₂ v ⇒ N_e }

- `d_handleAbortCapture` [Lean] types it for any captures `Γc`: owned values, borrows,
  capabilities.
  - `N_v` and `N_e` share `Γc` additively, which is #216's "at most once".
  - The side conditions are `[let]`'s on `Γc`. Under an outer row with weakening the captures
    must drop; under an unrestricted one they must be persistent.
  - A native rule would need the same conditions: the captures sit in the handler's frame,
    which an outer continuation captures.
- `handleAbortCapture_sem` is its soundness, by `fundamentalC`.
- P4(b) is an instance [checker]. `default(d)` with an owned `d` is this rule.

**Resuming operations: the environment is the handler's parameter.** The clauses stay `!` and
closed.

- The environment `S` travels through the state-passing answer `U(S ⊸ F(R ⊗ S))`.
- Each clause receives `S` when its thunk is applied, and hands it on to `κ`'s result.
- P4(a) is an instance, with `S = ref i32 ⊗ mut 'h i32` (an owned cell and an answering
  capability) [checker]. It compiles with 5 allocations and 3 indirect calls.
  - The indirect calls are the state-passing thunks.
  - SPEC §19 *Open* lists a native parameter. That is the lowering to build, not a typing rule.

**Compatibility.** `handle_compatC` is used unchanged by both forms. The abortive form is a
derived rule; the resuming form is a handler at a particular answer type.

### 3.3 Callbacks

R2a (`docs/effect-polymorphism.md` §5.2) is already this principle: `code_c :
!U(∀'x. Mut 'x Env_c ⊗ A ⊸ F(…))`, with `Env_c` lent. R5's reading is that a second-class
callback is a borrowed thunk.

### 3.4 How much of #229 the principle closes

| gap | by |
|---|---|
| an answering capability in a recursion | the passed environment |
| a resuming operation in a recursion | direct self-calls |
| a loop in a recursion | direct self-calls (at a loop type) |
| different result types | the record |
| recursion through values | the self-reference is an ordinary `!` value, once #161 lets a function with a row be passed |

Direct self-calls and the record are part of the same account: a group is the fixed point of
a generator. They are not part of the passed-environment rule itself.

---

## 4. System C, mapped (question 1)

Sources: Brachthäuser, Schuster, Lee and Boruch-Gruszecki, OOPSLA 2022, extended TR, and its Coq
artifact (zenodo 5833713); Brachthäuser, Schuster and Ostermann, OOPSLA 2020.

| System C | BoLo + kernel | status |
|---|---|---|
| value type `τ` | value type | as #184 |
| second-class block, parameter `f : σ` | `!` code with its environment lent for the call (R5) | [inspection]; #184's `x_sharedUnit` is the shape |
| tracked variable `f :* σ`, capture set `{f}` | a lifetime the environment's type mentions | [inspection] |
| transparent `def f = b` (`f :^C σ`) | a `let` of `!` code and its environment | [inspection] |
| `box b : σ at C` | closure conversion: `Env ⊗ !U(Env ⊗ A ⊸ C)`, data with outlives rules, bounded by `Env`'s lifetimes; for a linear closure, `[@c] U(…)` (`crossProg`) | [inspection] |
| `unbox e` (requires `C` in scope) | well-scopedness of `Env`'s type | [inspection] |
| a persistent box over borrows | **no former.** `[@c] !U` unboxes to `!U`, which outlives everything (T2) | SPEC §19 |
| `try {f ⇒ s} with {(x, k) ⇒ s'}` | `[handle]` at a static name (§19) | built |
| `resume` (`k :^C τ₀ → τ`, transparent, multi-shot) | `κ : U((B ⊸ F_Σ R) & …)` or `!U` at `unr` | built |
| a clause using outer capabilities | the clause's environment from the handler's parameter, or the clause run after the handler | §3.2 |
| recursion | not in the calculus or the Coq development. The Effekt implementation binds each function to a capture unification variable before checking its body | **ours: `bounded_fix`, the step taking the capabilities as part of its argument** |
| `region {r ⇒ s}`, `var x in r` | a `withbor` of a cell, or state behind control | #184, §4 below |
| effect safety (Cor. 9; progress and preservation, Coq) | FP and adequacy | built |

**Two blocks sharing one stateful capability.**

- **System C accepts it.** Capture sets combine by union, and nothing splits them. The paper's
  Example 10 enqueues two boxes over the same region and `resume`.
- **The reason is control.** An operation transfers control to the handler, which owns the
  state, so exclusivity comes from sequential control, not from uniqueness.
- **Ours refuses it in the answering encoding** (`twoBlocks_refused`), where the capability *is*
  the state, `Mut 'x S`. That refusal belongs to the encoding.
- **With a control operation it is accepted.** The state goes in the handler's parameter, and
  the capability is the static name, which captures nothing. P5 then types System C's program:
  two `!` closures in one pair, each performing `flip` on one handler. It runs, and the second
  closure sees the first's update [checker].
- **What is essential, and is not a limit relative to System C:**
  - a shared token cannot *mutate* in direct style. An `Imm`-lent cell comes back unchanged
    (6.64), and `!` holds `∅` (`experiments/HandlersControl` §1);
  - System C does not do that either.

**Where our embedding of Ξ and System C lost expressiveness, and why:**

1. **Recursion.** System C's calculus has none. Effekt's implementation uses general recursion
   (not total). Ours needs `bounded_fix`, and the elaboration did not pass the capabilities to
   the step (§1).
2. **Clauses.** Ξ and System C clauses are ordinary blocks. Ours are `!` because `[op]` copies
   `H`. The encodings of §3.2 recover them.
3. **Persistent boxes over borrows.** These are the T2 former. Closure conversion replaces them,
   at the price of an environment type that is visible: there are no existentials
   (`envShape_unlinked`, decision 3). System C exposes its capture sets too, but not the
   captured types.
4. **Aliased stateful capabilities in the answering encoding.** By design, as above.

---

## 5. The missed trick (question 2)

| candidate | verdict |
|---|---|
| second-class closures as borrowed thunks (environment lent) | **this one**, but it is not unbuilt. SPEC §2's `FnMut` row, #184's `EnvTy`, the generators' state passed through `yield` (`corpus/sugar/gen-yields.core.bc`) and R2a all use it. It was not applied to `bounded_fix`'s step or to handler clauses |
| capture sets as lifetimes (the `[@c]` box) | right for linear closures (`crossProg`). Wrong for persistent ones: `[]E` reaches `!`, which outlives everything. Scoping by name variables (§2.2) is the sound way to bound a persistent capability-using closure |
| graded `!` (#9) as promotion with captures | widening to persistent *data* is sound (`bangThunkF_compatG`). Widening to capability tokens needs a `!` bounded by a scope, which is T2. Not needed if environments are passed |
| a region or local-state construct | the handler's parameter (§3.2) is the local state. A native parameter is a lowering item (SPEC §19 *Open*) |

---

## 6. Recursion: one budget, Bekič, generators, Landin's knot (question 5)

### 6.1 (a) An ambient depth budget is expressible with `bounded_fix` as it is

- **Construction [checker, P7].**
  - Each step carries a copy of its driver's remaining budget in its argument, and counts it
    down with each call of itself, as `bounded_fix` counts its own.
  - A nested recursion's driver is called at the caller's copy, so the depths add up to at most
    the outer budget. P7 runs out exactly when they would exceed it.
- **The budget is a reader, not state.** It is passed down by value, never returned, and copied
  freely, since `I32` is persistent.
- **It is part of the passed environment, so no new construct is needed.**
- **What it is not.** It is not `bounded_fix` over the whole program's call graph, and not a
  graded resource.
- **Per call or per group?** Decrementing on *every* call is not needed for totality, since
  non-recursive call depth is bounded statically. It matters only for stack precision, which
  LLVM's stack-pointer check gives directly.

### 6.2 (b) The row cost

- **Where `Exhausted` appears.** In the row of every function that can reach a recursion.
- **Quieting it.** Treat it as ambient, as #228 proposes for `Alloc`: handled by the platform
  around `main` and left out of printed rows.
- **The real cost is drop glue.** `Exhausted` is abortive, so a call that can exhaust is a
  weakening point, with drop glue for the owned locals live across it. That is Rust's landing
  pads for panics.
  - With per-driver budgets, only calls that reach a group pay it.
  - A per-call check would put it on every call.

### 6.3 (c) Interactions

- **Multi-shot.** The budget is persistent data, so a multi-shot continuation copies it, which
  is right for depth: each resumption has a stack of its own.
- **State is different.** A shared *count* (total work, not depth) would be state, a `Mut`, which
  `!Γ` keeps out of multi-shot continuations.
- **Second-class closures.** The budget is part of the environment passed to `!` code.

### 6.4 (d) Not redundant

- **`bounded_fix` is still the only knot.** The ambient budget changes only where `k` comes
  from.
- **The per-group budget is the special case** of a constant per driver.
- **The static group fixed point stays the fast path:** direct calls of known code, nothing
  allocated (`corpus/rec-fib.bc`: 0, 0, 0; P6, P8 likewise).

### 6.5 (e) Landin's knot

- **Excluded [Lean, existing].** A knot through a cell would give a closed computation of `F A`
  that diverges, and `total_no_infinite_run` (`Core/Totality.lean`) rules that out.
- **The mechanism [inspection]:**
  - promotion needs `!` captures, so code cannot capture the cell it is stored in;
  - `μ` excludes `X` under `⊸` (T15).
- **Nothing else is lost [inspection].** Every recursion runs through `bounded_fix` or `ν`, and
  a value cycle among named functions is already a group (§1).

### 6.6 Mutual recursion with different result types

- **Covered, as §1 shows.** `boundedFix_compatX` holds at `C = &ⱼ(Aⱼ ⊸ Cⱼ)` as proved, and P6
  uses it.
- **The elaborator could use it** [inspection]. `groupCopy` would build the step as `⟨M₁, …,
  Mₙ⟩` over `self : 1 ⊕ !U(1 ⊸ C)`, and a call of member `j` would be `(force (unbang g) ()).j a`.
- **Cost.** One more β-step per call, the record's λ-value. Nothing is allocated (P6).

### 6.7 Cook and Palsberg, checked

The account in our terms:

- an object is `fix(gen)`, so a group is `bounded_fix` of a generator at a record type;
- layers are generator transformers (P8);
- recursion through stored callbacks is the same fixed point with the generator not known
  statically.

**What holds [inspection, P6 and P8].** Layers compose by composition before the fixed point.
The record is only the type at which the fixed point is taken, so the two compose.

**One mismatch: open recursion through a stored value has no fixed point of its own here.** All
recursion goes through a statically known group, and a stored callback only calls a group's
member.

- **What it would take:** an extensible object whose generator is supplied at run time, such as
  a plugin overriding a method. That needs `bounded_fix` applied to a generator that is itself a
  stored value.
- **It types already [inspection].** The step is any `!U` value.
- **What is not designed:** the elaboration of such programs.

---

## 7. The probes

| probe | shows | typed | runs (answer, live 0) | counts (alloc, indirect, copies) |
|---|---|---|---|---|
| `p1-rec-log.bc` | answering capability through a recursion | [checker]; [Lean] `recLog_derives` (the same shape) | 6 | 1, 0, 0 |
| `p2-rec-yield.bc` | `yield` before and after the self-call; `exhausted` | [checker] | 165; 99999 at budget 3 | 6, 0, 0 |
| `p3-rec-loop.bc` | a loop in each level (`bounded_fix` at a loop type) | [checker] | 0; 77 when the fuel is short | 102, 35, 0 |
| `p4-clause-captures.bc` | (a) parameterized handler over an owned cell and a capability; (b) abortive clause run after the handler | [checker]; [Lean] `d_handleAbortCapture` for (b) | 170 | 5, 3, 0 |
| `p5-two-blocks.bc` | System C's `twoBlocks`: state behind control | [checker] | 1 | 0, 3, 0 |
| `p6-rec-record.bc` | mutual recursion, different result types, record fixed point | [checker] | 1 (10 at `n = 8`) | 0, 0, 0 |
| `p7-shared-budget.bc` | one budget across nested recursions | [checker] | 10; 4006 at budget 4 | 0, 0, 0 |
| `p8-layer.bc` | a counting layer as a generator transformer | [checker] | 1505 | 1, 0, 0 |

**Lean, `experiments/SecondClass/SecondClass/`.**

- `Restated.lean`:
  - `CDerives.boundedFixEnv` and `boundedFixEnv_compatX`;
  - `CDerives.boundedFixRec` and `boundedFixRec_compatX`;
  - `boundedFixEnvRec_compatX`;
  - `envStepTy_persistent`.
- `RecLog.lean`:
  - `stepE_derives`;
  - `recLog_derives`: in context `c : Mut @a I32`, at every `Δ` and `a`;
  - `recLog_sem`.
- `AbortClause.lean`:
  - `d_handleAbortCapture`;
  - `d_handleAbortCapture_pure`;
  - `handleAbortCapture_sem`.
- `Prompts.lean`:
  - `row_names`;
  - `handleAt_compatC`;
  - `fresh_exists`.

---

## 8. Recommendation

1. **Now, as one spec entry with no kernel change:** apply the principle at the seams.
   - Recursive groups:
     - generators called directly; drop the `rec` site;
     - pass the environment (capabilities, layer state) in the argument;
     - a record fixed point for heterogeneous members;
     - layers as generator transformers;
     - a div step when a body loops.
   - Handler clauses:
     - abortive: run after the handler (`d_handleAbortCapture`);
     - resuming: the handler's parameter.
   - Then build #161's R2a, which follows the same principle.
   - **Gaps this closes:** answering and resuming effects in recursion, loops in recursion,
     different result types, #216, and recursion through values, which needs #161 as well.
   - **Baseline:** every existing theorem keeps its statement, and nothing new is proved beyond
     derived rules.
   - **Work to land it:** elaborator work in `groupCopy`/`defineGroup` and the clause
     elaboration, plus a native handler parameter in the lowering, so P4(a)'s thunks do not
     cost indirect calls.
2. **Next, as the replacement for decision 57's apparatus: L1, prompt variables.** Rows over
   name variables, `∀ν`, and tokens as values.
   - It removes copies per name assignment, the renaming lemma, ports and R3.
   - It costs the relation a name map (§2.2 (b)), which should be scoped as an issue first.
3. **Only if recursion through a site bites: L2, generative names** (§2.2 (a)).
4. **Not L3.** It needs higher-order state in the Kripke world, which is open problem
   territory.
5. **Separately:**
   - effects under `deep`: a per-row `deep`, and T1 for capabilities in frames;
   - generic recursion: instantiate before grouping.

## 9. Not verified

- **The elaborator changes of §8.1.** Not built. Each probe is hand-written core.
- **The cause of the loop rejection (§1)** is a hypothesis. P3 shows only that the kernel types
  the program.
- **Every statement in §2 about (a), (b) and L1–L3** is design.
  - What is checked is `handleAt_compatC` and `fresh_exists`.
  - I have not derived a fresh-name step or the name map, and have not verified that any
    obstruction to them is real.
- **The scoping argument of §2.3** (capabilities in scope are handlers on the stack) is not
  proved.
- **Layers on a record type** (§3.1) were not built.
- **The run-up.** The Fundamental Property used throughout (`fundamentalC`) is the library's. Its
  paper-level run-up includes `[TR]` Lemma 6.40, the one untranscribed row of `Paper/INDEX.md`,
  inherited and not used directly.

## Sources

- Brachthäuser, Schuster, Lee, Boruch-Gruszecki. *Effects, Capabilities, and Boxes*. OOPSLA 2022,
  doi:10.1145/3527320. Artifact: doi:10.5281/zenodo.5833713.
- Brachthäuser, Schuster, Ostermann. *Effects as Capabilities*. OOPSLA 2020,
  doi:10.1145/3428194.
- Muhcu, Schuster, Steuwer, Brachthäuser. *Multiple Resumptions and Local Mutable State,
  Directly*. ICFP 2025, doi:10.1145/3747529.
- Müller, Schuster, Starup, Ostermann, Brachthäuser. *From Capabilities to Regions*. OOPSLA 2023,
  doi:10.1145/3622831.
- Boruch-Gruszecki, Odersky, Lee, Lhoták, Brachthäuser. *Capturing Types*. TOPLAS 2023,
  doi:10.1145/3618003.
- Zhang, Myers. *Abstraction-Safe Effect Handlers via Tunneling*. POPL 2019.
- de Vilhena, Pottier. *A Type System for Effect Handlers and Dynamic Labels*. ESOP 2023. This
  is the closest prior semantic treatment of label-indexed handlers, with rows of label
  variables. It was not read in this spike.
- Tang, Hillerström, Lindley, Morris. *Soundly Handling Linearity*. POPL 2024.
- Cook, Palsberg. *A Denotational Semantics of Inheritance and its Correctness*. OOPSLA 1989.
