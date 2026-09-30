# Typed elaboration — design

Status: design only (issue #54, step 2, first item). Nothing here is implemented. It builds on
draft 0 of the surface ([`surface-cbpv.md`](surface-cbpv.md)), the core syntax
([`syntax-core.md`](syntax-core.md)), SPEC §11 (externs, `&c`, `for`) and SPEC §14 (divergence),
and on decisions 13, 16, 26 and 33–36 ([`decisions.md`](decisions.md)).

## 0. Summary

Today `Frontend/Sugar.lean` rewrites the program before anything knows a type. Every
shortcut listed on #54 comes from that. Each one stands in for a type the elaborator could not
see:

- residuals picked by the names `In`/`Out`;
- `n : T <-` on every threaded local;
- `(inl () : B)`;
- div calls recognised only as `return (f V)` heads;
- specialization only for callbacks passed by name;
- a `stdout` injected so that a loop can be driven;
- `for` only over `bytes c`.

This note makes elaboration run on types. The pipeline becomes:

```
source ─parse─▶ surface AST ─infer─▶ typed IR ─lower─▶ core AST ─check─▶ Expr + CDerives
               (superset of core)   (untrusted)       (untrusted)       (unchanged, trusted)
```

- **Inference** is bidirectional over the surface, one declaration at a time, in declaration
  order. It fills every hole the core requires: bracket arguments, binder types, injection and
  `roll` types, lifetime arguments and borrow witnesses. It also fixes each function's
  computation type (`F B`, or `U (Loop B R)` when it diverges) and makes the specializations
  that higher-order calls need.
- **Lowering** reads only the typed IR. It turns each sugar form into fully annotated core. It
  applies a *selective* delay-bind translation to divergent bodies only, which is Koka's
  selective CPS with `div_bind` as the bind.
- **Checking** is the existing checker, unchanged. It re-derives everything and returns a
  `CDerives` proof. The elaborator is not trusted: if it is wrong, the checker rejects the
  program, and no unsound program can pass.

Lifetimes are never solved as a constraint system. Every lifetime is introduced by a borrow
block or a callback binder and is named fresh there. The only other operation on lifetimes is
first-order *matching* when a lifetime-generic function is called. Value-type holes use
first-order unification, limited to one declaration. Linearity is kept by a structural
invariant: lowering copies no subterm outside additive positions, and every place a sugar
"lends" is rebound by shadowing.

## 1. Architecture

### 1.1 The phases

| phase | input → output | trusted | new or existing |
|---|---|---|---|
| parse | text → surface AST | no | `Frontend/Parser.lean`, extended |
| infer | surface AST → typed IR (TIR) | no | new: `Frontend/Elab/Infer.lean` |
| lower | TIR → core AST | no | new: `Frontend/Elab/Lower.lean`, replacing `Frontend/Sugar.lean` |
| check | core AST → `Expr` + `CDerives` | derivation checked by Lean | `Frontend/Check/`, unchanged |

**One grammar, one `.bc` file type** (decision 4, §8). **The surface AST is a superset of the
core AST**, as today: core is the sublanguage in which
every annotation is written and no sugar node occurs. Hand-written core (the escape hatch the
issue keeps, such as explicit `alloc`) mixes freely with sugar in one file. On a core node,
inference runs in check mode, fills nothing, and lowering is the identity.
`scripts/check-sugar.sh` already enforces this: "a core form is its own elaboration". Draft 0's
forms (`fn`, `let`, `f(e)`, `{ … }`) are added to the same AST (stage 5, §7).

**The typed IR** has one node per surface construct. Each node records:

- its span;
- its type: a value or computation type, over a mirror of `CVTy`/`CCTy` with one extra
  constructor for a metavariable, `?n`;
- at a binder, the variable's *identity* and its *class*: persistent, has a destructor, or has
  none (SPEC §12's three classes, decided by the checker's own functions);
- the summaries lowering needs: the node's *effect* (total or div), and the `let mut` variables
  it assigns and reads.

It is the counterpart of Rust's THIR: every implicit step is made explicit, and the
"adjustments" (a lend, an elided unit, a filled injection) are recorded on the nodes they
apply to.

**Types are the checker's types.** Inference elaborates written types with
`Frontend/Check/Elab.lean` (`elabV`, `elabC`, the same `Scope`, the same `Δ` numbering). It
decides side conditions with the checker's own Bool functions: `ltB`, the outlives decider,
`persistent`, `FShape` decoding, and `A_R`/`A′_R`/`A″_R`. So "the type inference computed"
and "the type the checker will derive" are computed by one piece of code. Lowering prints
types back to surface syntax with `ppV`/`ppC`, using a name map from binder numbers to fresh
lifetime names.

### 1.2 After, or interleaved?

Inference runs **before** lowering and is **interleaved with specialization**. Within a
declaration there are two passes: infer the whole body to TIR, then lower it. Neither is
interleaved with checking.

Why the body is not lowered as it is inferred (Lean's single pass): two lowerings depend on
what comes *after* a node.

- **Div.** Whether `x <- M; N` becomes a plain bind or a `div_bind` depends on `M`'s effect.
  Whether a terminal becomes a one-step loop depends on the effect of the whole body.
- **`let mut`.** The variables a `case` or a `for` must return, or thread, are those assigned
  in its subtree.

Both are synthesized attributes. Inference computes them bottom-up, and lowering reads them.
This replaces the syntactic pre-scan `loopsAt` and the separate pass `loopBody` of
`Sugar.lean`.

**Specialization is interleaved with inference**, because a specialization changes types. When
inference meets a call `h(args)` whose argument effects differ from `h`'s parameters (§2.4), it
infers a copy of `h` at those types first. It caches the copy by (function, instantiation) and
gives the call the copy's result type. The recursion is structured (decision 24), so each copy
calls only earlier declarations or their copies. The existing fuel bound (`elabDecl`) stays as
a guard.

**Declaration order** is kept. A declaration is inferred, specialized and lowered before the
next one is looked at. Its elaborated type (a div function's `U (Loop B R)`) is what later
declarations see.

### 1.3 What inference infers

| what | how | fills |
|---|---|---|
| value types of locals | synthesis at the binding | `x : T <-` annotations, `for` state types, `fun` binder types, `let mut` threading |
| bracket arguments | from operand and callback types (draft 0 §3.2) | `alloc[A]`, `swap[A, B]`, `withbor*[…]`, `withswap[…]`, `withload[…]`, fold `F`/`R`, `unfold[C, S]`, `div_bind[…]` |
| injection types | the expected type (check mode), or a metavariable resolved later | `(inl V : A + B)`, `(roll V : μ…)`, `absurd` |
| computation types | the declared result, plus the body's effect | `F B` or `U (Loop B R)`; `thunk` or `thunkv` and the eta form a `{ … }` needs (removes draft 0's S08) |
| effects | a two-point lattice per arrow, `total ⊑ div` (§2.4) | div inference, `total fn` checking, HOF specialization |
| residuals | the destructor-less part of the result type, by identity (§2.4) | `R` in `Loop B R`, the close paths |
| lifetime holes | fresh at binders; matching at instantiations (§2.3) | `'x` of every borrow block, `[@]` instantiations, `@b`/`@w` witnesses, `boxed['x]` |

### 1.4 Relation to the checker

The checker is not changed: no new rule, no special case, no hole filling. Draft 0 §3.2 and Q1
proposed filling holes *in the checker*; this design moves that into the elaborator, and the
core stays fully annotated (syntax-core §11: "the annotations the checker cannot infer are
required"). There are three reasons:

- `bcc desugar` keeps printing a program a user could have written by hand;
- the sugar pairs keep comparing complete core terms;
- the proof-producing checker keeps its size.

The one change outside elaboration is the wrapper for a looping `main` that uses no capability
(§4, row "injected `stdout`"). It is a change to the runtime's obligation in SPEC §11, not to a
rule.

No `CDerives` inversion, substitution lemma or completeness proof is needed (decision 21). The
elaborator proves nothing. It computes types with the checker's functions, and its output is
checked.

## 2. The algorithm

### 2.1 Bidirectional inference over the surface

The judgments follow the core's modes (syntax-core §6), lifted to the surface (Dunfield and
Krishnaswami's recipe: introduction forms check, elimination forms synthesize):

    Γ ⊢ e ⇐ A ~> t        Γ ⊢ e ⇒ A ~> t        (expressions: value-judged)
    Γ ⊢ S ⇐ C ~> t        Γ ⊢ S ⇒ C ~> t        (statement sequences: computations)

Here `t` is the TIR node, and `Γ` maps each name to (type, identity, class).

- **Synthesize:** variables, calls (from the callee's type), `*e`, constructors of a declared
  `data` type, literals (`i32` by default), operators, projections and observations, and
  ascriptions.
- **Check:**
  - `inl`, `inr`, `roll`, `absurd`, `()`, and tuples against a known product;
  - thunks `{ … }` and `{ p -> … }`, whose binder types come from the expected
    `U (A -o C)`;
  - `match` and `if` arms against the join type;
  - the tail of a body against the declared result.
- **Mode switch:** in check mode against `A`, a synthesizing form's type is unified with `A`.
  The adjustments of §5 are tried when unification fails (unit elision, a lend's hand-back),
  and never before.

The expected type flows *into* arguments. A call `f(e₁, …, eₙ)` synthesizes `f`'s type, then
checks each `eᵢ` against its parameter's type. So `putb(&mut stdout, 32)` needs no ascription,
and neither does `is_space` returning `true`.

### 2.2 Unification: value-type holes only, one declaration at a time

A metavariable `?n` stands for a value type the expected type did not provide, such as
`let x = inl ();` with no annotation. Unification is first-order over the `CVTy` mirror. There
is no generalization: definitions are monomorphic (decision 8); a generic `fn` is a template
instantiated per use, and its type arguments at a call are matched (§7, *Generic functions*). Metavariables are local to one declaration and are zonked when it
ends. An unsolved metavariable is an error that names the hole and its span ("the type of this
`inl` is not determined; ascribe it").

Lifetimes are not unification variables (§2.3). Computation types are not either. The only
unknown in a computation type is its effect, which §2.4 solves on its own lattice.

A metavariable has an unknown class, so inference treats it as linear until it is solved. This
matters only to the linearity lint (§2.5): the checker decides drops and persistence on the final
types.

### 2.3 Lifetimes: lexical, fresh, matched

Lifetimes stay explicit in the core and **lexically scoped** in the surface.

- **Introduced fresh.** Every lifetime is introduced by a binder, and the elaborator names it:
  - a borrow block `borrow mut r { b -> S }` gets a fresh `'x` (lifetime elision, §5);
  - a callback, a fold algebra `'y`, a family's internal `'a`/`'b`: fresh;
  - `'x` is written only when a type in the block mentions it.

  The name is fresh against the enclosing `Δ`, and the core numbers it `Δ.freshVar`, as the
  checker does.
- **Matched at instantiation.** For a call of `f : all 'a < @. A => B`, the argument's
  synthesized type is matched against `A`, which gives `'a := @x`. This is one-way,
  first-order matching over the lattice terms; there is no solving. The elaborator emits
  `(unbang f) [@x] V` and checks the bound `@x ⊏ @` with `ltB`, so that it can report a
  surface error before the checker would.
- **Conflicts meet.** When `'a` matches two different lifetimes (`f(b₁, b₂)`, both at `'a`),
  the elaborator takes their meet and shortens the longer argument with `:>`. `:>` is `⊑Imm`
  or `⊑Mut` on one borrow, and it erases. This is the only step that goes beyond matching, and
  it is closed-form. If `'a` occurs contravariantly (in a callback's parameter), a conflict is
  an error that asks for `f['x](…)`.
- **Witnesses are computed.** `withbor2`'s `@b` and `withbor_f2_mut`'s `@w` are the `∃ b` of
  the rule: a lifetime that `A` outlives. The elaborator takes the meet of the lifetimes free
  in `A`, or `top` when there are none. Every corpus program uses `top` today.
- **Outlives constraints are checked, not solved.** Every outlives side condition (`boxI`,
  `withbor*`, `foldImm`'s `R`) is decided by the checker's decider on known lifetimes. The
  elaborator runs the same decider first, only to attach a surface span to the error.

There is no region inference and no NLL. A borrow lives exactly as long as its block, and a
`&mut x` lives for one call. This is Rust's pre-NLL lexical model with every region made
explicit, but without the constraint solver pre-NLL `rustc` needed. That solver existed to infer
region extents, and here every extent is written by the block structure.

### 2.4 Computation types: effects, residuals, specialization

**Effects.** Each surface arrow carries an effect `ε ∈ {total, div}`. Inference computes the
effect of each TIR node: a join over its spine, where the join of `total` and `div` is `div`. A
node is `div` when:

- it is a `for` over a source whose type is codata (`U (iter …)`, `U (loop …)`); or
- it is a call of a function whose (possibly specialized) type returns `U (Loop B R)`, in
  direct style (below).

A `for` over finite data is total (§4). A function is div when its body is. `total fn` makes
that an error, reported at the first div node with its reason, as today. `div fn` forces the
function to be div.

**Direct-style calls, anywhere.** In a body, any call of a div function that is not wrapped in
`{ … }` (below) *runs* it. Lowering puts the body in A-normal form first: a nested div call
`g(f(x), y + 1)` becomes a sequence of binds, left to right. This is the order the value-level
application `lolliE` already evaluates in. The bind of a div call then becomes a state of the
body's state machine that holds the callee's loop, with the rest of the body run when it finishes
(SPEC §14, §15; §7 below); `div_bind` is the same bind as library code. So a div call may stand in an
argument, an operand, a `let`, a `match` scrutinee or a tail, not only at the head `return (f V)`.
Because inference types every call, no syntactic pattern is involved.

**Taking the loop as a value.** `{ f(x) }` is the loop value `U (Loop B R)`, and it is how a
loop is passed to `div_fuel` or stored. It follows draft 0's rule that `{ … }` is the visible
thunk, the shift that survives, and it **runs nothing until it is first observed** (decision 2,
§8). It lowers through a library function in `lib/div.bc`:

    div_defer[B, R] : U (F (U (Loop B R)) & F R) => U (Loop B R)

Its argument is a thunk with two observations. `start` runs the code up to the first loop and
returns that loop. `abort` hands back the residual without running anything. `div_defer` is
`unfold` at `Loop B R`, with state `U (F (U (Loop B R)) & F R) + U (Loop B R)`:

- **before the first observation**, `next` runs `start` and observes the loop it returns, and
  `close` runs `abort`;
- **after it**, both observations go to the loop.

`{ S }` for a div block `S` lowers to `div_defer (thunkv < ⟦S⟧, abort >)`, where `abort` hands
back the residual from the captured variables by identity (as at any close point, below). The
two components capture the same variables additively, as `div_bind`'s continuation does.
`{ f(x) }` is the instance `S = f(x)`, so its `start` is the call `f V`.

**The residual, from the type.** A loop closed early must release what it holds. Anything with
a destructor is dropped by the checker, on the close path, like any unused value (SPEC §12). What
has no destructor (a capability, a `ref` of an opaque type) must be handed back. So:

> The residual of a div function with result `B` is `K ⊗ 1`, where `K` is the tuple of the
> components of `B` that have no destructor (SPEC §12, class 3), in their order in `B`; or `1`
> when there are none.

This is decided by the `HasDtor` classes, not by the names `In`/`Out`. It gives today's answer on
every corpus program. It also covers any future capability type (`Args`, `Fs`, a user handle)
with no list to update.

At each close point, lowering must name the variables that hold `K`. It uses identities, not names:

- every destructor-less resource bound in the body gets an identity when it is bound (a
  parameter, an extern, a pattern);
- rebinding keeps the identity (`&mut c`, the `for` hand-back, `let mut`);
- the body's terminals determine which identity fills each position of `K`, and every terminal
  must agree;
- at a close point, the live variable with that identity is returned in that position.

If a destructor-less resource is live at a close point but has no position in `K`, or a position
has no live resource, closing would leak or invent one. That is reported as "closing the loop
here would leave `c : ref output` unreleased". This replaces `termCaps`, `capNorm` and the
restriction that a div call "must lend with `&c` or hand back exactly the caller's residual". A
callee's residual `R'` is converted to the caller's `R` by identity: the hand-backs the call's
lends produce are rebound, and the other components are those the caller holds.

**Specialization at the callback's computation type.** Inference treats the effect of each
arrow in a function's *parameter* types as an effect variable. It is instantiated at each call by
the argument's synthesized effect, and closed by the body. SPEC §14 describes this, and the typed
IR widens where it applies:

- **Any callback whose computation type is known is covered:** a named function, a closure
  `{ x -> … }`, a local variable holding either (its type is in `Γ`), a component of a tuple
  argument, a callback returned by an earlier call. The instantiation is read from the
  argument's type, not from its syntax.
- **The key** is (function, instantiated effect of each callback parameter). A copy is inferred
  with those parameter types. Its body's calls through the parameter are then div calls, so the
  copy is div by the ordinary inference, and its result type follows.
- **The written type** of a callback parameter (`A => B`) is read as "any effect". A parameter
  that must stay total is written `total A => B`, so a div argument there is an error at the call,
  not a copy.
- **Not covered:** a callback whose effect is fixed by a *stored* or *returned* type (a field
  of a `data` value, a cell's contents, a function result). Its written type is its type:
  effect inference is on parameter types only (decision 6, §8).

It stays whole-program monomorphization (decision 8). The core never gets effect polymorphism.
The mechanism is the one SPEC §14 names for later control effects: each effect contributes an
element of the lattice, its node rule (as `for` and div calls are div's), and its lowering (as
`div_bind` is div's). Finding, keying, copying and renaming are shared.

### 2.5 Linearity: elaboration never duplicates

The checker enforces linearity on the output. The elaborator keeps a stronger invariant, so that
its own errors come first and the checker's split errors do not point at generated code.

1. **Fill once per additive branch.** A user subterm is placed in the output at most once per
   additive branch: once, or once in each arm of a `case`, or once in each component of
   `< …, … >`. Today's templates already do this: `nu_in < (nu_out (force f s0)).1, (… ).2 >`
   uses `f` and `s0` once per component. Lowering is written as a function from TIR to core that
   places each child at most once per branch, so the invariant holds by construction, not by
   checking.
2. **Name, then use.** When a sugar needs a value in two places that are not additive (the
   hand-back of a lend, the state of a `for`), it binds the value to a variable first. Only a
   persistent variable is used twice.
3. **Lend and rebind by shadowing.** Every form that lends a place hands it back under the same
   name, and the old binding is consumed: `&mut x`, `&x`, `*r`, borrow blocks, `modify`, `for`
   over `bytes(&mut c)`, and a `let mut` variable a loop threads. The reader keeps using `x`; the
   core has `let (x, v) = …`.
4. **No inserted copies or drops.** Drops are the checker's (SPEC §12). Implicit copies of `imm`
   borrows are #58, a separate spec entry. If it lands, it is one more lowering rule, which
   decision 26 permits.
5. **A use-count lint on the TIR.** Before lowering, each non-persistent variable is counted per
   additive branch. A second use is reported at the surface span of that use: "`c` was lent to
   `bytes` at 12:14 and is used again here". The checker would reject the program anyway; the
   lint only makes the message precise.

### 2.6 Lowering

Lowering is a total function of a TIR node and its recorded types. It builds core AST
directly: no templates are printed and re-parsed, so no node gets a position inside a template
string. Every node it emits carries the span of the surface node it came from (§3).
Generated names use a reserved prefix. Elaboration rejects that prefix in user programs, and
printed core still re-parses.

Per declaration, lowering does the following, in order:

1. the local sugars of §5: constructors, patterns, operators, `if`, `*`, lends, unit elision;
2. `let mut` to rebinding and scoped cells;
3. then, **only if the body is div**, the delay-bind translation: A-normal form for div calls,
   `div_bind` at each, loops for `for`, one-step loops at terminals, the residual at each close
   path;
4. ambient capabilities in `main` (`wrapTail`, unchanged in behaviour).

## 3. Error reporting

**Spans on everything.** Surface nodes carry spans. The TIR node keeps the surface span. Every
core node that lowering emits for a surface node carries that node's span. The checker's errors
therefore always point into the user's file, never at `Span.none` or a template offset.

**Origins.** Lowering records, in a side table keyed by span, which sugar produced the core at
that span (`for`, `&mut`, `let mut`, a div call, a residual close path). The span stays a plain
`Span`, so `Frontend/Syntax.lean` and the checker are untouched. The error renderer:

1. prints the surface line and caret, as for any error;
2. if the span is in the origin table, adds a note: "in the core elaborated from this `for`
   (`bcc desugar` shows it)";
3. renames generated variables in the message through a table that lowering writes (`io_st` →
   "the loop's state"; a rebound `c` → `c`);
4. prints types back in surface form where one exists: `U (A -o F B)` as `{A -> B}`,
   `U (A -o F (U (loop B R)))` as `A -> div B`, `1 + 1` as `bool`, a generated `μ` by its
   `data` name.

**Which phase reports what.**

| error | phase | example |
|---|---|---|
| syntax | parse | as today (`corpus/fail/`) |
| type mismatch, unsolved hole, unknown name | infer | "`count` returns `In * (i32 * …)`, but `i32` is expected here" |
| effect: `total fn` that loops; a loop body that loops | infer | as today (`total-loops.bc`) |
| lend that cannot come back; a second use | infer (lint) | "`&mut c` needs `c` to be a place; this is an expression" |
| residual mismatch at a close point | lower | "closing the loop here would leave `stderr` unreleased" |
| borrow escape, overlap, outlives, missing destructor | check | "`b` escapes its borrow block" (the checker's message, at the block's span) |

A checker error on a program that inference accepted is expected for the last row only: borrow
discipline and ownership, which the elaborator does not model. For any other kind (a type
mismatch the checker finds after inference agreed), the renderer marks the error
`internal: elaboration disagreed with the checker` and attaches the core. That is an elaborator
bug, and the corpus should have none. It is the analogue of Lean's elaborator producing a term
the kernel rejects.

`corpus/reject/` gains an `-- expect:` for each new message, as today, including one per
generated-code error to pin the rendering.

## 4. How each shortcut disappears

| shortcut (today) | where | mechanism | |
|---|---|---|---|
| **Residual by syntax**: the capability part of a result is recognised by the names `In`, `Out`, `ref input`, `ref output` (decision 36) | `isCapTy`, `capPart`, `capNorm`, `termCaps` | The residual is the destructor-less part of the result type, by SPEC §12's classes (§2.4). Close paths fill it by resource identity, not by name. A callee's residual is converted by identity, so "lend with `&c` or hand back exactly the caller's residual" goes. | SPEC §14's paragraph on the residual is restated, with the same result on the corpus. |
| **Typed `for` locals**: `n : T <- …` on every threaded variable (`io-for-untyped.bc`) | `forLoop`, `latest` | The TIR has every variable's type. The loop threads the `let mut` variables its body assigns or reads, at their inferred types. | `corpus/reject/io-for-untyped.bc` becomes a pair. |
| **Injection ascriptions**: `(inl () : B)` | checker's `synV` on `inl`/`inr` | Checked against the expected type (§2.1), or a metavariable solved by a later use (§2.2). Lowering writes the ascription out. | `bool`'s `true`/`false` need none (§5). |
| **Narrow direct-style div calls**: only a head `return (f V)` or `return ((unbang f) V)`, at most one `&c` | `callee`, `divCall`, `loopBody` | Every call is typed. In a div body, lowering puts nested div calls in A-normal form, left to right, and `div_bind`s each. `{ f(x) }` takes the loop as a value (§2.4). | Several lends per call are allowed (§5). |
| **Narrow HOF specialization**: named functions without type parameters, the callback a named div function in a tuple component | `specParamN`, `hofOf`, `elabDecl` | Callback parameters have effect variables, instantiated by the argument's *type* at each call: closures, locals, returned callbacks (§2.4). Keyed by (function, instantiation). | A div function still has no type parameters. |
| **`stdout` injected into a looping `main` without capabilities** (decision 36) | `ambientCaps` | Not sugar: the `run_io` loop wrapper (`Frontend/Check/Externs.lean`, `ioMainOf`, `loopWrapperSrc`) accepts `main : F (U (Loop A B))` with no capability, as the instance `Caps = 1`. It makes all three streams itself, as it already does for the undeclared ones. SPEC §11's "Programs that run until their input ends" is restated for `Caps = 1`. `externs_loop_every_run` and `IORun.loop_every_run` are stated at the checked `run_io`, so they cover it with no new lemma. This must be confirmed when implementing: if a statement fixes `Caps ≠ 1`, it gets a `Caps = 1` instance. The backend already drives the checked `run_io` term, so it should need no change; if it does, that is coordinated with #80. | The one change outside elaboration. It is a runtime obligation, not a rule. |
| **Finite `for`**: `for` only over `bytes c`, always div | `forLoop` (`bytes` pattern) | (As built, §7 stage 9: a bounded source, by name, is `count_fold` with the source's bound.) Chosen by the source's type. Codata (`U (iter …)`): a loop by `unfold`, div. An array borrow `array_imm 'a A`, or a count `range(n)`: a **total** index loop bounded by the length, a `fold_own` over the unary count as `div_nat` does, with the loop state as the fold's result. It is library code in the prelude, picked by type (decision 26's "choosing `fold_imm`/`fold_own` from a type"). | Lists: see below. |

**Lists and finite `for`.** A left-to-right `for` over a `μ` list needs one of three things:

- a fold whose result is the state transformer `S -o F S`, which `fold_imm`'s outlives premise
  excludes (`U` does not outlive);
- a right-to-left order, which reverses the loop's effects;
- a finite borrowed iterator, which is #57.

The design therefore provides finite `for` over arrays and counts now, and over lists when #57
lands. Until then, the `fold_*` block forms consume lists, as draft 0 does.

## 5. The rest of step 2, on top

Each item is pure elaboration into existing core, checked by the unchanged checker, and gets a
sugar pair.

### 5.1 `&x` and `&mut x`: one form for #78's `&c` and draft 0's `&mut x`

**Decided** (decision 3, §8). There is one pair of forms. `&mut x` lends `x` exclusively to one construct, and
`&x` lends it shared. Afterwards `x` is usable again, possibly changed. `&c` is retired, and
existing uses become `&mut c`. `x` must be a place: a variable, which the construct rebinds. The
lowering is chosen by the types of `x` and of the parameter it is passed to (decision 26):

| `x : …` | parameter `: …` | lowering |
|---|---|---|
| `ref A`, written `box A` (an owned cell: a capability, a `box`) | `mut 'a A` | `withbor2` around the call, fresh `'x`; `x` rebound from the pair |
| `ref A` | `imm 'a A` (`&x`) | `withbor1`, likewise |
| a `let mut` value `A` | `mut 'a A` / `imm 'a A` | a **scoped cell**: `alloc`, `withbor2`/`withbor1` around the call, `free`, `x` rebound to the value |
| `mut 'b A` | `mut 'a A` | `withbor3` (reborrow) |
| `imm 'b A` | `imm 'a A` | `copy`, keeping one copy |
| `ref A` or `A` | owned `ref A`/`A`, where the callee hands it back first (`… => A * B`) | move and rebind: `let (x, v) = f(x, …)`. This is §11's `&c`, the case a div callee needs, because a borrow cannot outlive a call that returns a loop. |
| `ref A`, iterator source | `bytes(&mut c)` in `for` | move; at the iterator's finish or close, the handed-back `A` rebinds `c` |
| `array A` (owned) | `array_mut 'a A` (`&mut x`) / `array_imm 'a A` (`&x`) | `slice_borrow_mut`/`slice_borrow_imm` around the call, fresh `'x`, no cell; a view the call hands back dropped inside; `x` rebound from the pair (SPEC §9) |
| `array A`, source of a total `for` | `iter_mut(&mut x)` | a `borrow mut x` block around the whole loop (SPEC §16) |

To the reader, all rows mean the same thing: "lent here, back afterwards". Which core
mechanism implements it is a cost detail that types decide. The rule on surviving shifts is
not affected, since no row makes a thunk or suspends. A call may lend several places, each
lowered separately, in argument order. The restriction "one `&c` per call" goes. So does "only
in the head of a bind", because the A-normal form of §2.4 gives every call a bind.

### 5.2 `let mut`

- **Rebinding.** `let mut x = e;` then `x = e′;` lowers to shadowing (`x <- return ⟦e′⟧`).
- **Joins.** A `case`/`if` whose arms assign `let mut` variables returns them. Lowering makes
  the `case` a bind that yields the tuple of the variables its arms assign, typed from the TIR,
  and rebinds them. This is SSA conversion: what `io-wc.bc` writes by hand
  (`lines : i32 <- case … { … return lines … }`).
- **Loops.** A `for` threads the `let mut` variables its body assigns, and those it reads that
  are linear, and rebinds them after the loop.
- **Borrowed.** `&mut x` / `&x` on a `let mut` value is a cell scoped to that one construct
  (§5.1). Cells are stack slots; placement belongs to the backend (#15, decision on `box`).
- A `let mut` variable is linear or persistent by its type, like any other. Assigning a linear
  variable consumes its old value, which the checker drops if unused.

### 5.3 `data` and `box`

`box e` is the only surface heap allocation, apart from arrays (user decision). The surface
heap type is spelled `box A`, and it is the core's `ref A` (decision 7, §8). The core's
`box @ A`, the lifetime box `[@]`, takes a lifetime and is never written in the surface, so the
two do not collide. `box e` is `alloc[A] ⟦e⟧`, and `free(r)` is unchanged.

**A node is one block, with a cell per field** (decision 1, §8). The prelude's `List` is

```
data List = Nil | Cons(head: i32, tail: List)
```

This generates:

- **The type and shape.** `shape List_Cons = node (leaf i32) (leaf List)` and
  `type List = mu X. 1 + (ref i32 * ref X)`, the corpus's `List`. Each constructor is one
  summand (right-nested `+`); a constructor with fields is the block of its fields, so every
  field is a separately borrowable place, and recursion sits under a cell as decided. A
  constructor with no fields is `1`.
- **Construction.** `box Cons(x, t)` is `(roll (inr (alloc_s[List_Cons] (x, t))) : List)`: one
  explicit heap allocation per node, visible at the site. `Cons(x, t)` without `box` is an
  error that asks for `box`, never a silent promotion. `Nil` is `(roll (inl ()) : List)`, with
  no allocation.
- **Reassembly from cells.** `Cons(c, d)` applied to cells (`c : box i32`, `d : box List`)
  rebuilds a node from existing cells without allocating, which is what `fold_reuse` needs.
  This form is typed: it is taken only when the arguments are cells.
- **Patterns.** `match l { Nil -> S₁ | Cons(c, t) -> S₂ }` is
  `case (unroll l) { inl u -> let () = u; ⟦S₁⟧ | inr p -> let (c, t) = p; ⟦S₂⟧ }`, binding the
  cells. The pattern `box Cons(x, t)` frees the block (`free_s`) and binds the values.
- **Fold arms** use the same constructor patterns. Recursive fields are replaced as the fold's
  `A_R`/`A′_R`/`A″_R` dictate, computed by the checker's functions: in `fold_own` the `tail`
  field binds the result `R`; in `fold_reuse` it binds `(emptied cell, R)`. The algebra's type
  is filled, which removes the hand-computed fold types.

A field may also have type `box A` explicitly: a cell of its own inside the node's value, for a
type with no block (`data Opt = None | Some(v: box T)` does not need one). A recursive
occurrence that is under neither a block nor `box` is an error.

Nested patterns and match compilation stay out (draft 0 Q9). A pattern is one constructor
over variables, `_`, `()`, tuples, and `box p`.

### 5.4 `bool`, `true`/`false`, `if`

The prelude fixes the convention once, as the host tests already return it (syntax-core §8a):

```
type bool = 1 + 1          -- inl () is false, inr () is true
```

`true` is `(inr () : bool)` and `false` is `(inl () : bool)`. `if e then S₁ else S₂` is
`case ⟦e⟧ { inl u -> ⟦S₂⟧ | inr u -> ⟦S₁⟧ }`, and an `if` without `else` has `S₂ = ()`.
`a && b` and `a || b` are `if`s, short-circuiting. `not e` swaps the arms. `!` is not used for
negation, because it forces a thunk. `host[...]` leaves user code.

### 5.5 Operators and literals

- A literal checks against `i32` or `i64` and gives `i32[n]`/`i64[n]`. When it synthesizes, it
  defaults to `i32`.
- `+ - * & | ^ << >> == != < <= > >=` choose their host operation by the operands' type
  (`add32` or `add64`, and so on). This answers draft 0 Q5 now that types are available.
  Comparisons return `bool`.
- Signedness: `<` and `>>` are signed, and `<u`/`>>u` (or `lt_u(…)`) are unsigned.
- There is no `/` or `%` operator (decision 5, §8). Division and remainder are the prelude
  functions `div(a, b)` and `rem(a, b)` (signed; `div_u`, `rem_u` unsigned), returning
  `i32 + 1` with `inr ()` where Wasm traps.

### 5.6 Unit elision

A unit component may be left out wherever the types determine it. Elision is tried only when the
full form fails to unify, so it is never ambiguous: `A = A * 1` has no finite solution.

- A pattern `x` against `A * 1` binds `x : A` and consumes the unit (`let (x, u) = …; let () = u`).
- A tail `x` against the expected `A * 1` is `(x, ())`.
- A statement `e;` with `e : 1` is `let () = ⟦e⟧`.
- A lend's hand-back hides the handed-back component (§5.1), so `putb(&mut stdout, b);` is one
  statement.
- This removes the `let () = u` lines after every `swap`, `withswap` and borrow.

### 5.7 Lifetime elision in borrow blocks

`borrow mut r { b -> S }` is draft 0's `borrow mut r { 'x, b -> S }` with `'x` fresh (§2.3).
Fold blocks elide `'y` the same way. `'x` must be written only when a type written inside the
block names it. Signatures keep explicit lifetime parameters (`fn f<'a>(…)`): elision in
signatures is not part of step 2.

### 5.8 `*r`

`*e` synthesizes and reads a persistent payload. By `e`'s type:

| `e : …` | lowering |
|---|---|
| `imm 'a A` | `withload['a, 'x, A, A'] e { v -> v }` (draft 0) |
| `ref A`, `e` a variable | `withbor1` then `withload`; `r` is rebound (§5.1) |
| `mut 'a A`, `A` persistent | `withswap` with `x -> (x, x)` |

A non-persistent payload is an error, "`*` copies; `A` is not persistent". Array element reads
`a[i]` wait for the element borrow (#8), as the issue says.

### 5.9 A prelude, and `include` (#59)

- **The prelude** is `lib/prelude.bc`: `bool`, the I/O library (`lib/io.bc`), the div library
  (`lib/div.bc`), the finite `for` consumers, and the common `data` types. It is always in scope.
  Its declarations are emitted only if the program reaches them, as `usesName` does today, so
  `bcc desugar` and the erasures stay small.
- **`include "path.bc"`** puts that file's declarations in scope at that point, in order. It is
  textual, with a duplicate-name error. It has no namespaces; modules are #63. Include cycles
  are an error.
- The per-file copies of `List`, `cons`, `plus` and `getb` go.
- The ambient-capability trigger stays: a `main` that mentions `stdin`, `stdout` or `stderr` in a
  program that declares no extern.

## 6. Worked examples

The core shown is sketched: the shape is exact, and some repeated lines are elided with `…`.

### 6.1 `io-wc` (SPEC §11, §14)

Surface, 19 lines (the core file is 46):

```
fn is_space(b: i32) -> bool = b == 32 || b == 10 || b == 9

fn count(c: In) -> In * (i32 * (i32 * i32)) =
  let mut lines = 0;
  let mut words = 0;
  let mut chars = 0;
  let mut in_word = false;
  for b in bytes(&mut c) {
    chars = chars + 1;
    if b == 10 { lines = lines + 1 };
    if is_space(b) { in_word = false }
    else { if not in_word { words = words + 1 }; in_word = true }
  };
  (c, (lines, (words, chars)))

main -> i32 * (i32 * i32) =
  let (lines, (words, chars)) = count(&mut stdin);
  put_dec(&mut stdout, lines); putb(&mut stdout, 32);
  put_dec(&mut stdout, words); putb(&mut stdout, 32);
  put_dec(&mut stdout, chars); putb(&mut stdout, 10);
  (lines, (words, chars))
```

What inference decides:

- `count` has a `for` over `U (iter i32 In In)`, which is codata, so it is div.
- Its residual is `In * 1`: the destructor-less part of its result is `In`, whose identity is
  `c`.
- `main` calls `count` directly, so it is div too.
- `count(&mut stdin)` is row 6 of §5.1 (move and rebind), because `count` takes `In` and hands it
  back first.
- The `for` threads `lines`, `words`, `chars` and `in_word`, at `i32` and `bool`.
- The `if`s are joins that return the variables they assign.

Core (sketch):

```
def is_space : !(i32 => bool) = !thunkv fun (b : i32) ->
  case (unbang host[eq32]) (b, i32[32]) {
    inl u -> case (unbang host[eq32]) (b, i32[10]) {
               inl u2 -> return ((unbang host[eq32]) (b, i32[9]))
             | inr u2 -> return (inr () : bool) }
  | inr u -> return (inr () : bool) }

-- S = U (iter i32 In In) * (i32 * (i32 * (i32 * bool)))
def count : !(In => U (loop (In * (i32 * (i32 * i32))) (In * 1))) =
  !thunkv fun (c : In) ->
    lines : i32 <- return i32[0];  words : i32 <- return i32[0];
    chars : i32 <- return i32[0];  in_word : bool <- return (inl () : bool);
    el_step : !U (S -o F ((In * (i32 * (i32 * i32))) + S) & F (In * 1)) <-
      return (!thunkv fun (el_s : S) ->
        < let (el_it, el_st) = el_s;  let (lines, el_1) = el_st;  …;
          el_o <- (nu_out (force el_it)).1;
          case el_o {
            inl el_p -> let (b, el_it) = el_p;
              chars : i32 <- return ((unbang host[add32]) (chars, i32[1]));
              lines : i32 <- case (unbang host[eq32]) (b, i32[10]) {
                               inl u -> return lines
                             | inr u -> return ((unbang host[add32]) (lines, i32[1])) };
              el_j : i32 * bool <- case (unbang is_space) b {
                inl u -> words : i32 <- case in_word { inl v -> return ((unbang host[add32]) (words, i32[1]))
                                                     | inr v -> return words };
                          return (words, (inr () : bool))
              | inr u -> return (words, (inl () : bool)) };
              let (words, in_word) = el_j;
              return (inr (el_it, (lines, (words, (chars, in_word)))))
          | inr c -> return (inl (c, (lines, (words, chars))))
          },
          let (el_it, el_st) = el_s;  …;
          c <- (nu_out (force el_it)).2;
          return (c, ()) >);
    el_f <- return (unbang (unfold[loop (In * (i32 * (i32 * i32))) (In * 1), S] el_step));
    el_s0 : S <- return (bytes c, (lines, (words, (chars, in_word))));
    return (thunkv nu_in < (nu_out (force el_f el_s0)).1, (nu_out (force el_f el_s0)).2 >)

main : F (U (loop ((In * Out) * (i32 * (i32 * i32))) ((In * Out) * 1))) =
  el_m <- return ((unbang count) stdin);
  return (div_bind[In * (i32 * (i32 * i32)), (In * Out) * (i32 * (i32 * i32)), In * 1, (In * Out) * 1]
    (el_m, thunkv
      < fun (el_a : In * (i32 * (i32 * i32))) ->
          let (stdin, el_v) = el_a;  let (lines, el_w) = el_v;  let (words, chars) = el_w;
          el_1 <- return (put_dec (stdout, lines));  let (stdout, u1) = el_1;  let () = u1;
          …                                          -- five more lends, each rebinding stdout
          el_r : (In * Out) * (i32 * (i32 * i32)) <- return ((stdin, stdout), (lines, (words, chars)));
          return (thunkv nu_in < return (inl el_r), let (el_k, el_x) = el_r; return (el_k, ()) >),
        fun (el_c : In * 1) -> let (stdin, u) = el_c; return ((stdin, stdout), ()) >))
```

`main`'s residual `(In * Out) * 1` comes from its result type, whose destructor-less part is
`In * Out`. The continuation's close observation fills it by identity: `stdin` comes from the
callee's residual, and `stdout` is the caller's own.

This is the draft's form. As built, `main` is one state machine (§7, *Whole-body state
machines*): the call of `count` is a state holding `count`'s loop and `stdout`, whose `close`
binds `stdin` from the callee's residual in the same way.

### 6.2 `map-reuse` (block constructors, `fold_reuse`, `&mut` on a `let mut`)

Surface, 15 lines (the core file is 44):

```
data List = Nil | Cons(head: i32, tail: List)

fn map_inc(l: List) -> List =
  fold_reuse l {
    Nil -> Nil
  | Cons(c, (d, t)) ->
      let (c, x) = swap(c, ());
      let c = swap(c, x + 1);
      let d = swap(d, t);
      Cons(c, d)
  }

fn digits(l: List) -> i32 = fold_own l { Nil -> 0 | Cons(c, t) -> free(c) + t * 10 }

main -> i32 =
  let mut l = box Cons(1, box Cons(3, box Cons(5, Nil)));
  modify &mut l { k -> map_inc(k) };
  digits(l)
```

What inference decides:

- `fold_reuse`'s algebra type is `1 + ref i32 * (ref 1 * List)`: `A″_R`, computed. The arm
  `Cons(c, (d, t))` binds the head cell `c : ref i32`, the emptied tail cell `d : ref 1`, and the
  recursive result `t : List`.
- `Cons(c, d)` on cells builds the node without allocating.
- `swap(c, x + 1)` returns `ref i32 * 1`, so the unit is elided.
- `&mut l` on a `let mut` value, passed to `modify` (which takes `mut 'a List`), is a scoped cell:
  §5.1, row 3.

Core (sketch):

```
type List = mu X. 1 + (ref i32 * ref X)
shape List_Cons = node (leaf i32) (leaf List)

def map_inc_alg : !(1 + ref i32 * (ref 1 * List) => List) =
  !thunkv fun (r : 1 + ref i32 * (ref 1 * List)) ->
    case r {
      inl u -> let () = u; return (roll (inl ()) : List)
    | inr p -> let (c, el_1) = p;  let (d, t) = el_1;
        el_2 <- return (swap[i32, 1] c ());  let (c, x) = el_2;
        el_3 <- return (swap[1, i32] c ((unbang host[add32]) (x, i32[1])));  let (c, u1) = el_3;  let () = u1;
        el_4 <- return (swap[1, List] d t);  let (d, u2) = el_4;  let () = u2;
        return (roll (inr (c, d)) : List) }
def map_inc : !(List => List) = fold_reuse[1 + ref i32 * ref X, List] map_inc_alg

def digits_alg : !(1 + ref i32 * i32 => i32) = …          -- as corpus/map-reuse.bc
def digits : !(List => i32) = fold_own[1 + ref i32 * ref X, i32] digits_alg

main : F i32 =
  l <- return (roll (inr (alloc_s[List_Cons] (i32[1],
         (roll (inr (alloc_s[List_Cons] (i32[3], … (roll (inl ()) : List) …))) : List)))) : List);
  el_c <- return (alloc[List] l);
  el_q <- return (withbor2['x, top, List, 1] el_c
            (thunkv Fun 'x < dom. return (thunkv fun (el_b : mut 'x List) ->
               el_w <- return (withswap['x, List, 1] el_b (thunkv fun (k : List) -> return ((unbang map_inc) k, ())));
               let (el_b, u) = el_w;  let () = u;
               return (boxed['x] ()))));
  let (el_c, u) = el_q;  let () = u;
  l <- return (free[List] el_c);
  return ((unbang digits) l)
```

This is `corpus/map-reuse.bc` up to names and the `!` that draft 0 gives every `fn`. The sugar pair would compare their erasures.

### 6.3 `family-swap` (a family borrow, `modify`, rebinding)

Surface, 6 lines (the core file is 19):

```
main -> i32 * i32 =
  let ra = box 9;
  let rb = box 500;
  borrow mut (ra, rb) { (ma, mb) ->
    modify ma { x -> let y = modify mb { y -> (x, y) }; y } };
  (free(ra), free(rb))
```

What inference decides:

- The block form `borrow mut (ra, rb)` is `withbor_f2_mut` with a fresh `'c` and fresh `'a`/`'b`,
  `@w = top` (`i32` has no lifetime), `A = B = i32` from the cells' types, and `T = 1` from the
  body.
- The block rebinds `ra` and `rb`, and its `1` result is elided.
- The inner `modify mb { y -> (x, y) }` returns `(mb, y)`: `mb` is rebound (and later dropped by
  the checker), and `y` is the value.
- The outer body's tail `y` checks against `i32 * ?B`, fails, and elides to `(y, ())`, so
  `B = 1`.

Core: `corpus/family-swap.bc` exactly, with `withbor_f2_mut['c, 'a, 'b, top, i32, i32, 1]`, the
two `withswap`s at `['c, i32, 1]` and `['c, i32, i32]`, and the `let () = u` lines generated.

## 7. Staging plan

Every stage:

- passes `scripts/ci-local.sh`;
- keeps every existing `corpus/sugar/` pair;
- adds new pairs whose `.core.bc` side is **hand-written** core, compared by erasure;
- adds `corpus/reject/` entries for its new errors.

A stage that generalizes a sugar deletes the narrow version in the same change (decision 20).

| # | stage | removes | pairs and rejects added |
|---|---|---|---|
| 1 | **TIR and inference over today's AST**, lowering the identity on core and delegating to `Sugar.lean` for sugar nodes. Spans and the origin table (§3). | none | every corpus file: `bcc desugar` output unchanged |
| 2 | **Port `Sugar.lean` onto the TIR.** Typed `for` locals; injection ascriptions filled; residual from type by identity; direct-style div calls anywhere (A-normal form). Delete `isCapTy`, `capPart`, `capNorm`, `termCaps`, `callee`, `divCall`, `loopsAt`. | residual-by-syntax, typed `for` locals, injection ascriptions, narrow div calls | `io-for-untyped` becomes a pair; nested div call; a helper holding `stderr` and `stdout`; a residual-mismatch reject |
| 3 | **Specialization by effect instantiation** (§2.4). Delete `specParamN`, `hofOf`. | narrow HOF specialization | a callback through a local, a closure, a returned callback; a `total` parameter reject |
| 4 | **Looping `main` without capabilities.** The `run_io` wrapper for `Caps = 1`; SPEC §11/§14 text. Delete the `stdout` injection. | injected `stdout` | `div-hof.bc` runs with no capability; `bcc trusted` output |
| 5 | **Draft 0's expression layer**: `fn`, `let`, `f(e)` without `unbang`/`force`, nested direct style, tail `return` elided, `{ … }`/`!` (with `div_defer` in `lib/div.bc`), borrow blocks with lifetime elision, unit elision, literals and operators. | none | one pair per form; draft 0 §5.1–5.6 as pairs against their core files |
| 6 | **Lends and places**: `&x`/`&mut x` (§5.1) replacing `&c`, `*r`, `modify`, `let mut` (rebinding, joins, threading, scoped cells). | `&c` | `lend.bc` and `io-*` rewritten; a scoped-cell pair; a double-use reject |
| 7 | **Prelude and `include`** (#59), with `bool`/`true`/`false`/`if`/`&&`/`||`/`not`. | per-file `List`/`plus`/`getb` | `is_space` pair; an include-cycle reject |
| 8 | **`data` and `box`**: constructors, block constructors, patterns, fold arms. | hand-written `μ`/`shape`/`roll` | `map-reuse`, `sum-i32` as pairs; an unboxed-recursion reject |
| 9 | **Finite `for`** over arrays and counts (total), in the prelude. | "`for` over `bytes c` only" | `array-sum` with `for`; a total function with `for` |

**Stage 1, as built.** `Frontend/Elab/` holds the typed IR (`Tir.lean`), inference
(`Infer.lean`) and the pipeline (`Pipeline.lean`), which `checkProgram` and `bcc desugar` run.
The sugar is still elaborated first, by `Sugar.lean`; the typed IR is inferred on the core it
produces; lowering rebuilds each node from its lowered children, which is the identity on core.
Where a type needs one of the core's substitutions (instantiating a lifetime, unrolling a `μ` or a
`ν`, shortening a family), inference asks the checker's own synthesis for that node's type. The
checker is used as a function and is not changed. `Sugar.lean`'s templates are respanned to the
sugar that produced them and recorded as origins, so a checker error in generated code is
reported at the sugar, with its name (`corpus/reject/for-generated-origin.bc`). `bcc tir` prints
the typed IR, and `scripts/check-elab.sh` checks that every checked corpus program is fully
typed and lowers back unchanged, and pins two outputs (`corpus/tir/`). `Backend/Driver.lean`
still calls `Sugar.elaborate` directly. It sees the same core, because lowering is the identity;
switching it to `Elab.elaborate` is a one-line change for the stage that makes lowering do
something.

**Stage 2, as built.** `Sugar.lean` now decides on types. A typing context (`TCx`,
`Frontend/Elab/Meta.lean`) types the program as written, with each `def` at the type elaborated
so far, so a div function has its loop type and a call of it in direct style binds the loop's
`B`. The syntactic `isCapTy`, `capPart`, `capNorm`, `residual`, `termCaps`, `callee`, `divCall`,
`divCallAt`, `fnTy`, `pairTypes` and the `bytes` pattern are deleted:

- **The residual** is the destructor-less components of the result (`isLinear`, `loopCxOf`),
  named by the terminal's variables (`termParts`) (`corpus/sugar/residual-alias.bc`).
- **A call in direct style** is any application of loop type where that loop is not expected
  (`directCall`, `callIn`), and nested calls are lifted in evaluation order (`liftApps`)
  (`corpus/sugar/div-nested.bc`).
- **`for`** threads its variables at their inferred types, and reads its element type off the
  iterator's (`corpus/sugar/for-untyped.bc`).
- **Metavariables** are value types with unknowns, solved by first-order unification within one
  declaration (`fillProgram`). They annotate bindings whose injection's type only the uses
  determine (`corpus/sugar/inject.bc`).

Lowering is still the identity, so `Backend/Driver.lean` keeps calling `Sugar.elaborate`, which
now includes all of this. What remained of §4's table after stage 2, specialization and the
injected `stdout`, is stages 3 and 4. One limit stays: a call lends at most one capability, and a
div call's residual is matched to its `&c`.

**Stage 3, as built.** Specialization runs on types (`specDecl`, `specV`, `specC` in
`Sugar.lean`). A traversal of each declaration with its typing context finds calls of named
higher-order functions (plain or `!`). It types the argument, elaborating a closure at a callback
type as a div body when it loops (`closureAt`), and reads the instantiation off the argument's
type (`specTy`). The copy is made on first use and cached by (function, parameter type). The
syntactic `calls`, `renameCalls`, `fnShape`, `specParamN`, `specParam`, `copyFor` and
`Decl.calls` are deleted. Pairs: `corpus/sugar/hof-local.bc`, `hof-closure.bc`,
`hof-returned.bc`.

**Stage 4, as built.** `ioMainOf` (`Frontend/Check/Externs.lean`) takes a `main` with no externs
whose type is `F (U (loop A B))` as a program run by `run_io` with no capabilities, and
`loopWrapperSrc` binds the loop's result directly when there are none. `ambientCaps` no longer
gives such a `main` `stdout`. The backend needed no change: `convertMain` already handles zero
capabilities. `IORun.loop_every_run` is stated at the checked wrapper and covers it unchanged.
Pair: `corpus/sugar/loop-main.bc`, whose core form on `main` before this stage ran once and
printed `<fun>`.

**Stage 5, as built.** Draft 0's expression layer is in the one grammar (decision 37 of
`docs/decisions.md` lists what it follows and what it defers). The parser desugars the forms
that need no type; `Val.sugar` nodes carry the rest, and `surfDecl`/`surfV`/`surfC` in
`Sugar.lean` elaborate them on types, before specialization and divergence. `TCx` tracks the
lifetime binders it enters (`pushLife`), so a borrow block's body is typed at its lifetime and its
type arguments are printed by name. `{ S }` of a body that loops is `div_defer` (decision 2),
ascribed its loop type so that it is a loop value, not a call run in direct style. Pairs:
`corpus/sugar/surface-fn.bc`, `surface-ops.bc`, `surface-closure.bc`, `surface-defer.bc`,
`surface-borrow.bc`. Surface versions of three corpus programs run with the same goldens and the
same counts: `corpus/surface/family-swap.bc` (19 core lines, 7 surface), `io-wc.bc` (46, 33),
`io-upper.bc` (11, 5).

**Stages 6–7, as built** (decision 38 of `docs/decisions.md`). `&mut x`/`&x` are `Val.lend`
with a mode; `lendCall` wraps a call whose parameter at the lent place is a borrow in
`withbor2`/`withbor1`, or in a scoped cell (`lendBorrow`), keeping the lent place as the
borrow's place so that `Comp.elab`'s lend rebinding hands it back. `*e` and `modify &mut x` are
elaborated the same way. `let mut`, assignments and joins are desugared by the parser, which
tracks the `let mut` variables in scope and those each arm assigns. `lib/prelude.bc` holds
`true`, `false`, `not`; `include` resolves against `libModules`. Surface versions:
`corpus/surface/io-wc.bc` is §6.1's program (19 lines against 46), `map-reuse.bc` (20 against 44;
its `main` is the scoped cell) and `array-sum.bc` (16 against 25), each with the same answer and
counts. Pairs: `corpus/sugar/surface-mut.bc`, `surface-lend.bc`, `surface-bool.bc`.

**Borrow scopes over loops, as built** (SPEC §14; decision 40 of `docs/decisions.md`).
`Frontend/Elab/LoopLend.lean` runs inside `surfC`, on the program as written: a binding whose head
is a borrow block whose body loops, or a `let r = &x`, is rewritten so that each stretch of the
body that uses the borrow is a borrow block of its own and each `for`'s body borrows per step; the
result is elaborated as any surface code. A `def` over a borrow whose body loops is rewritten to
take the owner before `surfDecl` (`lentDef`). Pairs: `corpus/sugar/lend-block.bc`, `lend-let.bc`,
`lend-div.bc`.

**Whole-body state machines, as built** (SPEC §15, *One state machine per body*; #109 item 8;
decision 42 of `docs/decisions.md`). `mWalk` in `Sugar.lean` walks a generator or div body once,
on the same typing context as the rest of the elaboration, and records a point for each `yield`'s
continuation, loop head, `yield from`, call of a div function in direct style, and loop join,
with the variables live there (their inferred types; the capabilities of the residual by name).
The code between points is the program's own, with each transition replaced by a move: a call of
the point's `!` function, or its state returned as a skip. `mAssemble` builds the sum type of the
states, the functions (last point first), the step with a `case` on the state for `next` and for
`close`, and the `unfold`; each point's code is a template at the span of the sugar it comes
from, so an error in it is reported there. `genDef`, `genValue` (blocks and callbacks) and every
div body (`divBody`: `def`s, `main`, closures, `{ … }`) use it; a body it does not cover, and one
the elaboration rejects, is elaborated by `genBody` and `loopBody` as before. The core forms of
`corpus/sugar/gen-from.bc` and `for-value.bc` are written by hand as machines; those of the other
pairs whose elaboration changed are the elaboration as `bcc desugar` prints it. The divergence library is emitted only when the
elaborated program names it.

**Generic functions and inferred arguments, as built** (#130; SPEC §15, *Generic functions*;
decision 45 of `docs/decisions.md`). `fn f[A, …]<'a, …>(…)` is parsed as a template
(`Mark.template`) and, like a generic generator, instantiated per use at the call's types
(`makeInst`), its body elaborated at those types; `fn f<'a, 'b>` declares lifetime parameters
(`all 'a < top. all 'b < top.`, a `Fun` for each around the body). Every call whose callee is
generic goes through one function, `genericCall` in `Sugar.lean`: the callee's type is a pattern
whose type parameters are placeholders and whose lifetime parameters are unknowns; each argument
is elaborated once, against the pattern solved so far, and its type matched against it
(`matchV`, first-order, §2.2), closures with a hole and injections last; what is still open is
matched against the expected result; each lifetime parameter is the lifetime its argument gives
it, or the meet of two, the argument shortened with `:>` (§2.3). The call is then
`(unbang f__gN) ['x] ['y] W`, `f[T] …` for a core `def f[A]`. This replaces `instLife`, which
found one lifetime. An open type or lifetime is an error at the call that names it
(`corpus/reject/generic-type-unknown.bc`, `generic-lifetime-unknown.bc`). `lib/slice.bc` is
written in these forms, its loop steps closures; the corpus calls it as `reverse(v)`,
`eq(a, b, eq_u8)`, with the same outputs and counts, and `corpus/slice-lib.bc` calls the rest.
Pairs: `corpus/sugar/generic-fn.bc`, `generic-infer.bc`, `generic-lifetimes.bc`.

**Stage 9, as built** (strings S4; SPEC §16, *The total `for`*; decision 46 of
`docs/decisions.md`). `forTotal` in `Sugar.lean` runs in `surfC` at a `for` whose source is
bounded (`boundedFor`: `range`, a view's `iter_imm`/`iter_mut`, an adapter that observes its
source once per observation over one, `take` over a bounded or never-skipping source) and whose
body neither yields, breaks nor returns. It writes the loop as surface code around the body, a
template: the source computed once with its bound (`boundedPlan`), and `count_fold[S]` whose `!`
step observes it and runs the body, with `S` the source (or what it finished with) and the
variables the body reads or assigns at their inferred types; the source's type is read by
elaborating its code once first. Over `range` there is no iterator. The result is elaborated as
any surface code, so the body's own sugar, an inner total `for` included, is elaborated in the
step. The per-observation lend (`LoopLend`) treats such a `for` as a statement, so a borrow block
around it stays one block. A lend of an owned array in the source is a borrow block around the
loop, and `lendCall` lends an array at a view parameter for one call (`lendSlice`, the §5.1
row). The divergence inference never sees these loops: `sum_squares` of
`corpus/for-finite.bc` is `total`. Generic instances take the lifetimes their type arguments
mention as lifetime parameters (`makeInst`), so the adapters take `iter_imm`'s `imm 'x A`.
Pairs: `corpus/sugar/for-range.bc`, `for-view.bc`, `lend-array.bc`; reject
`corpus/reject/total-for-unbounded.bc`. Not done: a total `for` whose body breaks or whose value
is kept, and a bound read off a type (a program's own finite source is a loop).

Stages 1–4 retire the #54 shortcuts and change no surface syntax, except that `&c` stays until
stage 6. Stages 5–9 are the rest of step 2. After stage 9, step 3 of #54 (rewriting 6–10 corpus
programs and measuring) can start.

The only change outside `Frontend/Elab/` and `Frontend/Parser.lean` is stage 4's wrapper in
`Frontend/Check/Externs.lean`, with its SPEC text. `Backend/` is not touched by this plan. If
stage 4 turns out to need a runtime change, it is raised on #80.

## 8. Decisions

The user settled the seven questions of the first draft. The sections above follow them.

1. **The `data` layout.** A node is one block with a cell per field. The allocation is written
   at construction, `box Cons(x, t)`: one explicit heap allocation per node. The prelude's
   `List` uses it (§5.3).
2. **`{ f(x) }` is lazy.** It runs nothing until it is first observed, through the library
   `div_defer`. This is consistent with braces meaning "suspend" (§2.4).
3. **One spelling, `&mut x`,** for "lent and handed back", and `&x` for a shared borrow. The
   mechanism (a real borrow, a scoped cell, or move-and-rebind for a div callee) is chosen by
   type. `&c` is retired (§5.1).
4. **One grammar and one `.bc` file type.** Surface and core mix freely (§1.1).
5. **No `/` or `%` operator for now.** `div(a, b)` and `rem(a, b)` return `i32 + 1` (§5.5).
6. **Effect inference on callback parameter types only,** for now. Stored and returned callback
   types keep their written effect (§2.4).
7. **The surface heap type is spelled `box A`,** which is the core's `ref A` (§5.3).

## 9. Prior art

- **Bidirectional typing.** J. Dunfield, N. Krishnaswami, "Bidirectional Typing", ACM
  Computing Surveys 54(5), 2021; "Complete and Easy Bidirectional Typechecking for Higher-Rank
  Polymorphism", ICFP 2013.
  - Taken: the mode discipline (introductions check, eliminations synthesize), and the
    annotation principle that an annotation is needed exactly where no type flows in.
  - Taken, simplified: their ordered contexts with existential variables solved in place, as
    metavariables local to one declaration with no generalization.
- **Rust.** `rustc`'s HIR → typeck → THIR → MIR.
  - Typeck records node types and "adjustments" (autoref, autoderef, coercions) in a side
    table. THIR is built from HIR and those tables, with every adjustment made explicit.
  - Our TIR and lowering are this split. Our adjustments are lends, unit elision, filled
    injections and the div translation.
  - Region inference before NLL solved constraints over lexical regions, and NLL solves them
    over the MIR control-flow graph. We need neither: every region is a block written by the
    programmer or introduced by one sugar form, so there is nothing to infer, only matching at
    calls.
- **Koka.** D. Leijen, "Type Directed Compilation of Row-Typed Algebraic Effects", POPL 2017.
  - Koka translates only the effectful functions into continuation-passing style, chosen by
    their inferred effect types. Our div lowering is the same selective translation, with
    `div_bind` as the bind and a two-point effect lattice.
  - Koka keeps effect-polymorphic code polymorphic (evidence passing). We monomorphize
    instead, because the core has no polymorphism over computation types (decision 8).
- **Effekt.** J. Brachthäuser, P. Schuster, K. Ostermann, "Effects as Capabilities", OOPSLA
  2020. Capabilities are passed as arguments, and blocks are second class by default. We take
  both, and our lends of capabilities (`&mut stdout`) are its capability passing in borrow form.
  Effekt's effect polymorphism is contextual, through second-class blocks. Ours is
  specialization at the callback's type, which reaches the same "no colouring" for the call
  sites the TIR can type.
- **Lean 4's elaborator.** Syntax is elaborated to `Expr` with metavariables, postponement, and
  errors attached to syntax references. Its output is checked by the kernel, which alone is
  trusted. Our trust split is the same (untrusted elaborator, checked `CDerives`), and so is
  our error discipline: every generated node keeps its source reference, and a kernel
  rejection of elaborated output is an elaborator bug.
