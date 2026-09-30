# Surface syntax: CBPV made visible, and pleasant — draft 0

Status: design only (issue #54, step 1). Nothing here is implemented. The parser extension is
step 2 and comes after general `ν` (#31). The core syntax this desugars to is
[`syntax-core.md`](syntax-core.md) (draft 1); section numbers `§N` below refer to it unless they
say `SPEC §N`.

## 0. Summary

The core syntax is call-by-push-value written out in full: every bind, force, return and thunk
is on the page. Across the six core programs of section 5 (five from `corpus/`, one adapted),
115 of 203 non-comment lines (57%) carry `<-`, `force`, `thunkv`, `unbang` or `return`. That matches the corpus review's measurement for
issue #17 (calls, binds and forces about 60% of lines, then eta-wrappers and hand-computed fold
types). Most of these shifts cancel: they cost nothing at run time, and they make the page
harder to read without telling the reader anything.

The surface removes those and keeps the rest. It is governed by one rule:

> **Sugar may elide a polarity shift only if the shift cancels.** Surviving shifts stay visible.

Cancelling shifts are the bind of a nested call, the force in calling a named function, the
`return` of a tail value, and eta-wrappers. Surviving shifts are a thunk that escapes (a closure
allocation), a force of a live object (an indirect call, a codata observation), a suspension
point (a reified continuation), and materializing codata into data. Surviving shifts get a
token on the page: `{ … }`, `!`, `.next`/`.poll`/`.close`, `<-`, `suspend`,
`loop`/`unfold`/`generate`, `collect`. Section 4 says how the checker rejects sugar that would
hide one.

Line counts for the examples of section 5 (non-blank, non-comment lines):

| program | core | surface | Rust |
|---|---:|---:|---:|
| 5.1 sum over a borrowed list | 26 | 10 | 11 |
| 5.2 in-place map | 44 | 19 | 17 |
| 5.3 family swap | 19 | 7 | 6 |
| 5.4 delay loop | 55 | 21 | 12 |
| 5.5 stream pipeline, take and sum | 16 | 2 (7 without the zoo) | 4 |
| 5.6 implicit drops | 43 | 22 | 17 |
| 5.7 effects as capabilities (sketch, #18) | — | 11 | 6 |
| **total, 5.1–5.6** | **203** | **81** | **67** |

## 1. The governing rule

CBPV has two shifts. `U C` turns a computation into a value (a thunk); `F A` turns a value into a
computation (`return`, eliminated by `x <- M; N`). A shift *cancels* when its introduction meets
its elimination in known code: `force (thunk M) = M` and `x <- return V; N = N[V/x]`. A
cancelled shift leaves no closure, no indirect call and no stored continuation (dream property
C2, [`dream-properties.md`](dream-properties.md)). A shift *survives* when its introduction and
elimination are separated by an unknown or escaping value: a thunk stored, returned or passed to
code that keeps it; a continuation handed to a handler that keeps it; a codata object observed
later.

| shift in the core | cancels when | surface |
|---|---|---|
| `x <- return V; N` (the bind of a nested call, `run`, `ofRet`) | always: the value is in hand | **elided**: `f(g(x))`, `let x = e` |
| `return V` at the tail | always: the caller binds it | **elided**: the last expression of a body |
| `force f` where `f` is a named `fn` or `def` | always: the code is known | **elided**: `f(x)` |
| `thunkv fun x -> return (f x)` (eta-wrapper) | always: it is `f` | **elided**: write `f` |
| a callback thunk passed to a borrow constant, `withswap`, a fold, or `for_each` | the constant forces it within its own extent; it cannot escape (its type is bounded by the callback's lifetime, or the body is closed) | **elided**: `borrow … { … }`, `modify … { … }`, `fold_own … { … }`, `for x in … { … }` |
| `unbang` of a `!` def | always: `!` is not a shift, and `unbang` erases | **elided** |
| `boxed['x] V` at a borrow callback's tail | always: `[]I` erases | **elided** |
| a thunk literal that may escape | only if C2 shows it does not | **visible**: `{ … }` |
| `force x` of a local thunk (a closure call) | only after specialization | **visible**: `x!`, `f!(e)` |
| codata construction (`fixd`/`unfold_s` and the in/out eta) | never: it allocates the object's state | **visible**: `loop f from s`, `unfold f from s` |
| codata observation `(out (force d)).i` | never: it runs the object's step | **visible**: `d.poll`, `s.next`, `d.close`, bound with `<-` |
| an operation whose handler receives the continuation | never: the continuation is reified | **visible** in the inferred effect row and `bcc check`'s per-call-site report, and as the explicit `k` in the handler; no token at the call (decision 49; draft 0 wrote `suspend c.op(e)`) |
| turning codata into data | never: it allocates the data | **visible**: a call of `collect`; no sugar produces one |

Two consequences shape the whole surface:

- **Expressions contain no surviving force.** A surviving force (`!`, an observation,
  `suspend`) may stand only at the head of a statement: the right side of `<-`, the scrutinee
  of a `match`, or the tail. It never hides inside an argument, an operand or a tuple.
- **A `<-` line is a line where a live object is forced; a `{` in expression position is where
  a closure may be made.** A `{` attached to a keyword (`borrow`, `modify`, `fold_*`, `for`,
  `match`) never allocates. The cost of a program can be read off these tokens.

## 2. The forms

### 2.1 Values and computations

The surface keeps the core's two categories (§6) under familiar names.

- An **expression** `e` is a value-judged expression, read call-by-value: variables, literals,
  tuples, `inl`/`inr`/`roll`/`unroll`, calls, operators, thunk literals, ascriptions, and the
  block forms of 2.6–2.9 used as values. Evaluation is left to right. Calls inside an expression
  are the core's value-level application `V W` (`lolliE`), whose erasure already sequences them;
  no bind is written.
- A **statement sequence** `S` is a computation: `let`, `<-` and statement expressions separated
  by `;`, ending in a tail. A tail expression is returned; a tail computation (a `match`, an
  observation, a force) is the result.

The category of each position is fixed by the grammar, as in the core, so the desugarer never
needs a type to decide it. Sequences extend as far right as possible and end at `)`, `}`, `>`,
`|`, or a `,` between `<M, N>` components (§6.5). `{ … }` is free for thunks, as in Frank.

### 2.2 Direct-style nesting and calls

    f(g(x), y + 1)          -- (unbang f) ((unbang g) x, (unbang host[add32]) (y, i32[1]))

- `f(e₁, …, eₙ)` for a declared `fn f` calls it. `fn`s take their parameters as one tuple (the
  corpus convention: `cons : i32 * List => List`), so a call is one value-level application and
  nesting needs no binds.
- A `fn` with lifetime parameters is called the same way; the lifetime arguments are holes
  `[_]`, filled by the checker (section 3.2). `f['x](b)` writes them.
- A constant (`alloc`, `free`, `swap`, `copy`, …) is called by its name with its bracket
  arguments as holes: `swap(c, v)` is `swap[_, _] c v`. The arity and currying of each constant
  are fixed by its row in §8, so this is syntactic.
- A computation form in expression position (a `match`, `if`, `borrow`, fold, …) is wrapped in
  `run` (`ofRet`), which is the cancelling `F` shift. It may not contain a surviving force at its
  head (section 4).

### 2.3 Thunks `{ … }` and force `!`

After Frank: braces suspend, `!` forces.

| surface | meaning |
|---|---|
| `{ S }` | a thunk of the computation `S` (`U C`) |
| `{ p -> S }` | a thunk of a function, `U (A -o C)`; `p` is a pattern |
| `{ 'x, p -> S }` | a lifetime-generic function in the value-level `all` shape, `all 'x < dom. A => B` |
| `!{ … }` | a persistent thunk (`!U C`): it may capture only persistent variables (SPEC §10) |
| `t!` | force a local thunk `t` of type `U (F A)` |
| `f!(e)` | force a local thunk `f` of type `U (A -o C)` and apply it |

A named `fn` is called without `!`: its force cancels. A local variable of thunk type is called
with `!`: that is an indirect call through a closure. The checker's error when `!` is missing is
in section 4. In types, `{A -> T}` abbreviates `U (A -o F T)` (or `U (A -o C)` when `T` is a
computation type), and `{C}` abbreviates `U C`, so braces mean "thunk" in both terms and types.

### 2.4 `let` and `<-`

| surface | use |
|---|---|
| `let p = e; S` | bind an expression. `p` is a pattern: `x`, `_`, `()`, `(p, q)`. |
| `p <- M; S` | bind the result of a surviving force: `t!`, `f!(e)`, `d.poll`, `s.next`, `d.close`, `suspend c.op(e)`, or a `match` on one of these |
| `linear let x = e; S` | the core's `linear` binder (SPEC §12 opt-out) |
| `e; S` | a statement whose value is `()` |

`<-` is required exactly where the right side forces a live object, and a warning elsewhere.
It is not a monadic bind in the source's types: there are no surface monads (decision 16), and
the `F` it eliminates is never written. A
`_` pattern binds a fresh variable that implicit destructors (SPEC §12) drop at the end of the
path, or reject if its type has no destructor.

### 2.5 Declarations and computation types in signatures

    fn name<'a, …>(x₁: A₁, …, xₙ: Aₙ) -> T = S
    fn name[P, …]<'a, …>(…) -> T = S          -- value-type parameters, as core defs
    main -> T = S

- If `T` is a value type (its sort is read from its syntax, §4), the result is `F T`: the
  return is the cancelling shift. If `T` is a computation type, it is written as is:
  `fn cd_step(s: i32 * i32) -> F (i32 + i32 * i32) & F 1`. Codata, pairs of computations and
  the `F` of a delay step therefore show in signatures, and nothing else does.
- A `fn` is a closed top-level definition, so it is always `!`-promoted: it is static code, and
  using it as a value (`walk(xs, f)`, `fixd` of it) costs nothing.
- Lifetime parameters `<'a>` are `all 'a < top`; a bound is written `<'b < 'a>`.
- `def`, `type`, `shape` and `extern` are unchanged from §10.
- **Divergence is inferred** (SPEC §14). A `fn` whose body loops (a `for` over a source that
  may not end, or a direct-style call of a div function) is div: its `-> T` elaborates to
  `-> U (loop T R)`, and a call of it in direct style is the delay bind. `main` is div when its
  body loops. `total fn` asserts that a function does not loop, which inference checks; it is
  the common annotation, the one a library writes to promise termination. `div fn` (or
  `-> div T`) is allowed but never needed. The core today spells these `total def` and
  `div def`.

### 2.6 Borrowing

Each borrow constant gets a block form. The block is the callback; its tail is boxed at the
callback's lifetime by the desugarer. The block is second-class: the constant forces it within
its own extent, and the callback's type (bounded by `'x < dom`, returning `box 'x B`) keeps it
from escaping, so it never allocates.

| surface | constant | result |
|---|---|---|
| `borrow imm r { 'x, b -> S }` | `withbor1` | `(r, B)` |
| `borrow mut r { 'x, b -> S }` | `withbor2` | `(r, B)` |
| `reborrow m { 'x, b -> S }` | `withbor3` | `(m, B)` |
| `borrow mut (r₁, r₂) { 'c, (m₁, m₂) -> S }` | `withbor_f2_mut` (`imm` likewise) | `((r₁, r₂), B)` |
| `borrow mut block s { 'c, f -> S }` | `withbor_s_mut` (`imm` likewise) | `(s, B)` |
| `load v { 'x, y -> S }` | `withload` | `B` |
| `*v` | `load v { 'x, y -> y }` | the payload, when its view outlives `'x` |
| `modify m { x -> S }` | `withswap` (`S` returns `(new, B)`) | `(m, B)` |

The choice between `withbor1`, `withbor2` and `withbor3` depends on whether the source is a
`ref` or a `mut`, which is a type. The keywords (`borrow` against `reborrow`, `imm` against
`mut`) say it instead, so the desugaring stays syntactic.

### 2.7 Folds

    fold_imm e { inl p -> S₁ | inr q -> S₂ }     -- likewise fold_own, fold_reuse

The arms are the algebra, matched on the unrolled shape with the recursive results in place. The
algebra's type (`A_R`, `A′_R`, `A″_R`, §8) is a hole: the checker already computes it to compare
with the written one (§8 notes), so it can fill it instead. This removes the hand-computed fold
types of the corpus review. When a `fn` body is exactly a fold of its only parameter, the
desugarer emits the fold application itself (`def sum = fold_imm[…] alg`), which is the
eta-reduction of the wrapper.

### 2.8 Codata

| surface | meaning |
|---|---|
| `loop f from e` | the delay `fixd f` started at `e` (allocates its state); `e` binds tighter than `\|>` |
| `unfold f from e` | the stream `unfold_s f` started at `e` (allocates its state) |
| `< S₁, S₂ >` | a pair of computations (`withI`), for a step's observations |
| `d.poll`, `s.next` | the first observation: `(delay_out (force d)).1`, `(stream_out (force s)).1` |
| `d.close` | the second observation, `close` |

Construction is a keyword because it is a surviving shift: the object's state is allocated and
captured in a thunk. It also removes the only eta-wrapper the corpus writes (§6.4's
`thunkv delay_in < (delay_out (force f s)).1, (delay_out (force f s)).2 >`), because the
desugarer knows the unrolling of each former it names. After #31, `delay_out` and `stream_out`
become one `out`, and observation names come from the codata declaration (`Iter`'s `next` and
`close`), each name mapped to one projection index.

### 2.9 `|>` and `for`

- `e |> f(a, …)` is `f(a, …, e)`, and `e |> f` is `f(e)`: last-argument, left-associative,
  lowest precedence (#17). No shift is involved.
- `for x in e { S }` is the `for_each` consumer of #48 (decision 24). Let `v⃗` be the free local
  variables of `S` other than `x`, computed from the syntax. If `v⃗` is empty, it is
  `for_each(e, !{ x -> S })`. Otherwise the loop threads them as state:
  `let (v⃗) = for_each_with(e, (v⃗), !{ (x, (v⃗)) -> S; (v⃗) })`. The body is closed either way,
  so it is static code: no closure, and after `for_each` is specialized (defs are macros, §10),
  one loop.
- A `for` over a source that may not end (the input, `bytes c`) is a loop: it makes the enclosing
  function div (SPEC §14), and may appear in any function. A `for` over a finite source is total
  (not yet provided).
- A body that consumes a threaded variable (a `mut` borrow passed away, an owned value freed) is
  rejected, because it cannot hand it back. Borrowed variables are threaded by reborrowing; see
  open question Q3 for `imm`.

### 2.10 Implicit destructors

Unchanged from SPEC §12: an unused owned value is dropped at the end of its path, and `linear`
opts out. The surface adds only `_` patterns and `linear let`. A drop of codata runs its
`close`, which is a force of a live object that the programmer does not write; open question Q6
asks whether that needs a mark.

### 2.11 Effects as capability arguments (sketch, #18)

This part is a sketch against #18 and #52; none of it has a core counterpart yet.

    cap Log { emit(x: i32) -> 1 }                  -- returning: the handler answers
    cap Gen { yield(x: i32, k: {1 -> r}) -> r }    -- suspending: the handler gets the continuation

- A **capability** is an ordinary argument, passed as a borrow (`log: imm 'h Log`). Higher-order
  code takes it like any other argument, so there is no function colouring: `walk` in 5.7 is
  written once, and used with a returning and with a suspending callback.
- **Polarity decides the cost** (#52, #18). An operation whose handler-side signature has no
  continuation returns a value (`A -o F B`): a call is a direct call, and the shift cancels. An
  operation whose handler-side signature has a continuation parameter `k : {B -> r}` hands the
  handler a `U`: the continuation is reified, which is a stackless state machine (decision 25).
  No operation-kind keyword is needed; the `{…}` in the declaration is the shift.
- **The suspension point is marked where it happens**: `suspend gen.yield(x)`, as a statement.
  The mark is on the operation call, not on the enclosing function or its type. Callers of
  `produce` do not change; the instantiation of `walk` inside `produce` is compiled as a state
  machine and the one inside `report` as a loop, chosen by monomorphization.
- `handle Log { emit(x) -> S } in { log -> S' }` lends a capability for a scope (a borrow).
  `generate { gen -> S }` runs `S` under a library handler for `Gen` that stores the
  continuation in an iterator's state: the braces and the keyword mark the allocation.

### 2.12 Integers, conditions, patterns

- A literal `100` is `i32[100]`; `100i64` is `i64[100]`.
- `+ - * == != < <= > >=` are the 32-bit host operations (`add32`, …, `lt_s32`, …), wrapped in
  `unbang`. The width is not inferred (section 3.3).
- `if e then S₁ else S₂` is a `case` on `1 + 1` with `inr ()` as true (§8a).
- `match e { inl p -> S₁ | inr q -> S₂ }` is a `case`. Each arm's pattern is irrefutable below
  the tag (variables, `_`, `()`, tuples), so no match compilation is needed and every arm's
  consumption is the core's (§7).

## 3. Desugaring

### 3.1 The translation

`⟦e⟧` is the core value-judged expression of an expression, `⟦S⟧` the core computation of a
sequence. `y#` is a fresh name. `⟦S⟧^'x` is `⟦S⟧` with each tail `return V` replaced by
`return (boxed['x] V)` and each tail computation `M` by `z# <- M; return (boxed['x] z#)`.
Everything below reads only the syntax: no type is consulted.

**Declarations**

| surface | core |
|---|---|
| `fn f(x: A) -> T = S`, `T` a value type | `def f : !(A => T) = !thunkv fun (x : A) -> ⟦S⟧` |
| `fn f(x₁: A₁, …, xₙ: Aₙ) -> T = S` | `def f : !(A₁ * … * Aₙ => T) = !thunkv fun (p# : A₁ * … * Aₙ) -> let (x₁, …) = p#; ⟦S⟧` |
| `fn f(…) -> C = S`, `C` a computation type | the same with `!U (A -o C)` |
| `fn f<'a>(…) -> T = S` | `def f : !(all 'a < top. A => T) = !thunkv Fun 'a < top. return (thunkv fun (p# : A) -> ⟦S⟧)`, nested per lifetime |
| `fn f<'a>(x: imm 'a L) -> R = fold_imm x { … }` | `def f : … = fold_imm[_, 'a, top, R] alg`, `alg` as for the fold form below |
| `main -> T = S` | `main : F T = ⟦S⟧` (or `main : C`) |

**Expressions**

| surface | core |
|---|---|
| `100`, `100i64` | `i32[100]`, `i64[100]` |
| `f(e₁, …, eₙ)`, `f` a `fn` | `(unbang f) (⟦e₁⟧, …, ⟦eₙ⟧)`; with lifetimes, `(unbang f) [_] … (…)` |
| `f`, `f` a `fn`, not called | `unbang f` |
| `c(e₁, …, eₙ)`, `c` a constant | `c[_, …] ⟦e₁⟧ … ⟦eₙ⟧`, curried as in §8 |
| `e₁ + e₂` | `(unbang host[add32]) (⟦e₁⟧, ⟦e₂⟧)` |
| `*e` | `withload[_, 'x#, _, _] ⟦e⟧ (thunkv Fun 'x# < dom. return (thunkv fun (y# : _) -> return (boxed['x#] y#)))` |
| `{ S }` | `thunkv ⟦S⟧` if `⟦S⟧`'s head is `fun`, `Fun` or `<,>`; `thunk ⟦S⟧` otherwise (§6.4) |
| `{ p -> S }` | `thunkv fun (y# : _) -> ⟦let p = y#; S⟧` |
| `{ 'x, p -> S }` | `thunkv Fun 'x < dom. return (thunkv fun (y# : _) -> ⟦let p = y#; S⟧)` |
| `!{ … }` | `!thunk` / `!thunkv` likewise |
| `borrow imm e { 'x, p -> S }` | `withbor1['x, _, _] ⟦e⟧ (thunkv Fun 'x < dom. return (thunkv fun (y# : _) -> ⟦let p = y#; S⟧^'x))` |
| `borrow mut e { … }` / `reborrow e { … }` | `withbor2['x, _, _, _]` / `withbor3[_, 'x, _, _]`, the same callback |
| `borrow mut (e₁, e₂) { 'c, (p, q) -> S }` | `withbor_f2_mut['c, 'a#, 'b#, _, _, _, _] (⟦e₁⟧, ⟦e₂⟧) (…)`, with `let (p, q) = y#` |
| `load e { 'x, p -> S }` | `withload[_, 'x, _, _] ⟦e⟧ (…)`, the same callback |
| `modify e { p -> S }` | `withswap[_, _, _] ⟦e⟧ (thunkv fun (y# : _) -> ⟦let p = y#; S⟧)` |
| `fold_own e { arms }` | `(unbang (fold_own[_, _] (!thunkv fun (r# : _) -> ⟦match r# { arms }⟧))) ⟦e⟧`; `fold_reuse` likewise |
| `fold_imm e { arms }` | `(unbang (fold_imm[_, 'y#, _, _] (!thunkv Fun 'y# < top. return (thunkv fun (r# : _) -> ⟦match r# { arms }⟧)))) [_] ⟦e⟧` |
| `loop f from e` (`f` a `fn`, passed as the `!` value itself) | `run (g# <- return (unbang (fixd[_, _] f)); s# <- return ⟦e⟧; return (thunkv delay_in < (delay_out (force g# s#)).1, (delay_out (force g# s#)).2 >))` |
| `unfold f from e` | the same with `unfold_s`, `stream_in`, `stream_out` |
| `e \|> f(a, …)` | `⟦f(a, …, e)⟧` |
| `(e : A)` | `(⟦e⟧ : A)` |
| a computation form `M` in expression position | `run (⟦M⟧)` |

**Sequences and computations**

| surface | core |
|---|---|
| `let x = e; S` | `x <- return ⟦e⟧; ⟦S⟧` (`x <- ⟦e⟧; ⟦S⟧` when `e` is a computation form) |
| `let (p, q) = e; S` | `let (y#, z#) = ⟦e⟧;` then `p`, `q` bound from `y#`, `z#` |
| `let () = e; S`, `e; S` | `let () = ⟦e⟧; ⟦S⟧` |
| `let _ = e; S` | `y# <- return ⟦e⟧; ⟦S⟧` (`y#` is dropped by SPEC §12) |
| `linear let x = e; S` | `linear x <- return ⟦e⟧; ⟦S⟧` |
| `p <- M; S` | `y# <- ⟦M⟧; ⟦let p = y#; S⟧` |
| tail `e` | `return ⟦e⟧` |
| `t!` | `force t` |
| `f!(e)` | `y# <- return ⟦e⟧; (force f) y#` |
| `d.poll`, `s.next`, `d.close` | `(delay_out (force d)).1`, `(stream_out (force s)).1`, `(… (force d)).2` |
| `match e { inl p -> S₁ \| inr q -> S₂ }` | `case ⟦e⟧ { inl y# -> ⟦let p = y#; S₁⟧ \| inr z# -> ⟦let q = z#; S₂⟧ }` |
| `match d.poll { … }` | `o# <- ⟦d.poll⟧; case o# { … }` |
| `if e then S₁ else S₂` | `case ⟦e⟧ { inl u# -> ⟦S₂⟧ \| inr u# -> ⟦S₁⟧ }` |
| `< S₁, S₂ >` | `< ⟦S₁⟧, ⟦S₂⟧ >` |
| `for x in e { S }`, no free locals | `let () = (unbang for_each) (⟦e⟧, !thunkv fun (x : _) -> ⟦S⟧)` |
| `for x in e { S }`, free locals `v⃗` | `let (v⃗) = (unbang for_each_with) (⟦e⟧, (v⃗), !thunkv fun (y# : _) -> let (x, st#) = y#; let (v⃗) = st#; ⟦S; (v⃗)⟧)` |

`for_each` and `for_each_with` are library `def`s of #48, over the finite iterator of #31; they
are not written yet. `suspend`, `handle`, `generate` and `cap` have no core target until #18.

### 3.2 Holes: the one thing sugar cannot do

Almost every constant takes bracket arguments that are types (§8): `withbor1['x, A, B]`,
`alloc[A]`, `swap[A, B]`, `fold_imm[F, 'y, @c, R]`, and `fun` binders need their type (§11). A
syntactic desugarer cannot supply them. The desugaring above writes each as a hole `_`, and the
**checker fills holes by synthesis**: in bidirectional mode the argument's type is known
(`withbor1`'s `A` from `r : ref A`, `B` from the callback body, a `fun` binder from the type it
is checked against, a fold's algebra type from `F` and `R`, which the checker already computes).
A hole it cannot fill is an error naming the bracket position.

This is a change to the core syntax and the checker, not sugar, and it is proposed as core
syntax draft 2. It stays out of the trusted base for the same reason the checker does: every
filled hole ends in a `CDerives` derivation that Lean checks (§11). Without it the surface is
still valid with every bracket written out: the line counts of section 5 do not change, but most
`borrow`, `modify`, `alloc`, `swap` and fold sites gain one to four bracket arguments.

### 3.3 Other places where a form would need types

| form | why it needs a type | the explicit alternative |
|---|---|---|
| `x + y` at `i64` | the width of the operation | `+` is `i32`; `i64` arithmetic is `add64(x, y)`. Operator overloading by width is open (Q5). |
| `{ M }` where `M` is a non-`F` computation whose head is not a λ (for example `f!(s)` at `delay A`) | the eta-expansion that `thunkv` needs (§6.4) follows the type | annotate: `{ M : delay A }` eta-expands syntactically through the named former (`A -o C` by `fun`, `&` by `<M.1, M.2>`, `delay`/`stream` by in/out). Or use `loop`/`unfold`, which cover every case in the corpus. |
| `d.close` before #31 | `delay_out` against `stream_out` | the surface lands after #31, when there is one `out`. Before it, `d.close_delay` / `s.close_stream`. |
| `borrow`/`reborrow`, `imm`/`mut` | `ref` against `mut` source | the keyword says it (2.6). |
| `roll`/`unroll`, `inl`/`inr` of a named variant | the `μ` and sum to use | written, as in the core (§14). Named constructors wait for variants (#19). |
| calling a lifetime-generic `fn` | the lifetime argument | a hole (3.2), or `f['x](b)`. |
| `for` threading | whether a free variable is `imm` (copy), `mut` (reborrow) or owned | the threading is syntactic; what the body may do with each variable is checked (Q3). |

## 4. Enforcing the rule

The desugarer runs before the checker and is not trusted (decision 13). Enforcement is in two
places, and neither can make an unsound program pass: they only reject.

**In the desugarer (syntactic).** The surviving-shift tokens (`!` after a name, `.poll`,
`.next`, `.close`, `suspend`) are recognised by the parser, so their position can be checked
without types. Each desugared node also carries its origin (the surface form and span) into the
core AST, where the checker can read it.

**In the checker (typed).** Elided callbacks (borrow, `modify`, fold and `for` blocks, `*v`) are
thunks passed to a known constant or library `def`. The checker confirms at each one that the
thunk is second-class: a constant's callback is consumed by the constant, and a `for` body is
closed. Name resolution confirms that `f(x)` without `!` names a `fn`, a `def` or a constant.

The errors:

```
error[S01]: `let` binds an expression, but its right side forces a live object
  --> count.bcs:6:11
   |  let o = d0.poll;
   |          ^^^^^^^ `.poll` runs one step of the delay `d0`
   = help: bind it with `<-`: `o <- d0.poll;`

error[S02]: a surviving force is nested inside an expression
  --> nats.bcs:5:15
   |  let s = x + t.next;
   |              ^^^^^^ `.next` forces the stream `t`
   = help: bind it first: `(y, t) <- t.next; let s = x + y;`

error[S03]: `f` is a local thunk; calling it goes through a closure
  --> walk.bcs:5:23
   |  for x in iter(xs) { f(c, *x) }
   |                      ^ `f : !{imm 'h C * i32 -> 1}` is a parameter, not a `fn`
   = help: write `f!(c, *x)`

error[S04]: `gen.yield` suspends: its handler receives the continuation
  --> gen.bcs:11:37
   |  walk[Gen](xs, gen, !{ (gen, x) -> gen.yield(x) })
   |                                    ^^^^^^^^^^^^ `Gen.yield` has `k: {1 -> r}` (gen.bcs:2)
   = help: write `suspend gen.yield(x)` as a statement

error[S05]: `suspend` on an operation that returns
  --> log.bcs:8:40
   |  … !{ (log, x) -> suspend log.emit(x) }
   |                   ^^^^^^^ `Log.emit` has no continuation parameter (log.bcs:1)
   = help: remove `suspend`: the call is a direct call

error[S06]: the `for` body consumes `out`, which the loop must hand back each step
  --> copy.bcs:4:30
   |  for x in it { push(out, x) }
   |                     ^^^ `out : mut 'o Buf` is used up by `push`
   = help: reborrow it: `for x in it { reborrow out { 'y, o -> push(o, x) } }`

error[S07]: codata used where data is expected
  --> list.bcs:9:14
   |  let l = unfold step from 0;  …  head(l)
   |                                      ^ `l : {stream i32}`, `head` expects `List`
   = help: materializing a stream allocates; write `collect(l |> take(n))`

error[S08]: `{ … }` needs its type to eta-expand
  --> run.bcs:3:12
   |  let d = { f!(s) };
   |           ^^^^^^^^ the body is a `delay i32` computation, not a function or `F`
   = help: write `loop step from s`, or annotate `{ f!(s) : delay i32 }`
```

S01–S05 and S08 are syntactic. S06 and S07 are typed. S07 is a better message for an ordinary
type error: no sugar ever inserts `collect`, so no sugar can hide a materialization.

## 5. Examples

Each program is the corpus program named, in the core (the file in `corpus/`, header comments
removed), in the proposed surface, and in Rust. The surface programs are not checked (there is
no parser); each was desugared by hand against section 3. The Rust programs compile with rustc
1.97 and print the corpus answer. Lines are non-blank, non-comment lines. Rust's `println!`
line stands for returning the answer from `main`.

### 5.1 Sum over a borrowed list (`corpus/sum-i32.bc`, answer 123)

<details><summary>core, 26 lines</summary>

```
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def plus : i32 * i32 => i32 = unbang host[add32]

-- A_R = 1 + (view 'y (ref i32) * i32) = 1 + (imm 'y i32 * i32); view 'x i32 = i32.
def sum_alg : !(all 'y < top. 1 + (imm 'y i32 * i32) => i32) =
  !thunkv Fun 'y < top. return (thunkv fun (r : 1 + (imm 'y i32 * i32)) ->
    case r {
      inl u -> return i32[0]
    | inr p -> let (b, s) = p;
               n <- return (withload['y, 'x, i32, i32] b
                      (thunkv Fun 'x < dom. return (thunkv fun (v : i32) -> return (boxed['x] v))));
               return (plus (n, s))
    })

def sum_list : !(all 'a < top. imm 'a List => i32) =
  fold_imm[1 + (ref i32 * ref X), 'a, top, i32] sum_alg

def nil : List = roll (inl ())

def cons : i32 * List => List =
  thunkv fun (p : i32 * List) -> return (roll (inr (alloc_s[Node] p)))

main : F i32 =
  l <- return (cons (i32[100], cons (i32[20], cons (i32[3], nil))));
  r <- return (alloc[List] l);
  q <- return (withbor1['x, List, i32] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x List) ->
            n <- return ((unbang sum_list) ['x] b);
            return (boxed['x] n))));
  let (r2, n) = q;
  return n
```
</details>

Surface, 10 lines:

```
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def nil : List = roll inl ()
fn cons(x: i32, t: List) -> List = roll inr alloc_s[Node](x, t)

fn sum<'a>(l: imm 'a List) -> i32 =
  fold_imm l { inl () -> 0 | inr (b, s) -> *b + s }

main -> i32 =
  let r = alloc(cons(100, cons(20, cons(3, nil))));
  let (_, n) = borrow imm r { 'x, b -> sum(b) };
  n
```

Rust, 11 lines:

```rust
enum List { Nil, Cons(Box<(i32, List)>) }
use List::*;

fn cons(x: i32, t: List) -> List { Cons(Box::new((x, t))) }

fn sum(l: &List) -> i32 {
    match l { Nil => 0, Cons(node) => node.0 + sum(&node.1) }
}

fn main() {
    let r = Box::new(cons(100, cons(20, cons(3, Nil))));
    let n = sum(&r);
    println!("{n}");
}
```

Surviving shifts: none. The borrow callback and the fold algebra are second-class blocks, `*b`
is a `withload` with the identity callback, and the cell `_` and its list are dropped by their
destructors. The 14 core lines carrying `<-`, `return`, `thunkv` or `unbang` are all cancelling shifts.

### 5.2 In-place map (`corpus/map-reuse.bc`, answer 642)

<details><summary>core, 44 lines</summary>

```
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def nil : List = roll (inl ())

def cons : i32 * List => List =
  thunkv fun (p : i32 * List) -> return (roll (inr (alloc_s[Node] p)))

-- A″_R = resR R: `ref 1 * R` at the tail. Take the head, put back its successor.
def map_inc_alg : !(1 + ref i32 * (ref 1 * List) => List) =
  !thunkv fun (r : 1 + ref i32 * (ref 1 * List)) ->
    case r {
      inl u -> return (roll (inl u))
    | inr p ->
        let (rn, q) = p;
        cx <- return (swap[i32, 1] rn ());
        let (c, x) = cx;
        cu <- return (swap[1, i32] c ((unbang host[add32]) (x, i32[1])));
        let (c1, u1) = cu;
        let () = u1;
        let (c2, t) = q;
        cu2 <- return (swap[1, List] c2 t);
        let (c3, u2) = cu2;
        let () = u2;
        return (roll (inr (c1, c3)))
    }

def map_inc : List => List = unbang (fold_reuse[1 + ref i32 * ref X, List] map_inc_alg)

-- A′_R = resO R = 1 + ref i32 * i32: free each cell, and read the list as digits, head last.
def digits_alg : !(1 + ref i32 * i32 => i32) =
  !thunkv fun (r : 1 + ref i32 * i32) ->
    case r {
      inl u -> return i32[0]
    | inr p ->
        let (rn, t) = p;
        return ((unbang host[add32]) (free[i32] rn, (unbang host[mul32]) (t, i32[10])))
    }

def digits : List => i32 = unbang (fold_own[1 + ref i32 * ref X, i32] digits_alg)

main : F i32 =
  l <- return (cons (i32[1], cons (i32[3], cons (i32[5], nil))));
  r <- return (alloc[List] l);
  q <- return (withbor2['x, top, List, 1] r
         (thunkv Fun 'x < top. return (thunkv fun (b : mut 'x List) ->
            w <- return (withswap['x, List, 1] b (thunkv fun (k : List) -> return (map_inc k, ())));
            let (b2, u) = w;
            let () = u;
            return (boxed['x] ()))));
  let (r2, u) = q;
  let () = u;
  return (digits (free[List] r2))
```
</details>

Surface, 19 lines:

```
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def nil : List = roll inl ()
fn cons(x: i32, t: List) -> List = roll inr alloc_s[Node](x, t)

fn map_inc(l: List) -> List =
  fold_reuse l {
    inl () -> nil
  | inr (c, (d, t)) ->
      let (c, x) = swap(c, ());
      let (c, ()) = swap(c, x + 1);
      let (d, ()) = swap(d, t);
      roll inr (c, d)
  }

fn digits(l: List) -> i32 =
  fold_own l { inl () -> 0 | inr (c, t) -> free(c) + t * 10 }

main -> i32 =
  let r = alloc(cons(1, cons(3, cons(5, nil))));
  let (r, ()) = borrow mut r { 'x, b -> let _ = modify b { k -> (map_inc(k), ()) }; () };
  digits(free(r))
```

Rust, 17 lines:

```rust
enum List { Nil, Cons(Box<(i32, List)>) }
use List::*;

fn cons(x: i32, t: List) -> List { Cons(Box::new((x, t))) }

fn map_inc(mut l: &mut List) {
    while let Cons(node) = l {
        node.0 += 1;
        l = &mut node.1;
    }
}

fn digits(l: List) -> i32 {
    match l { Nil => 0, Cons(node) => { let (x, t) = *node; x + digits(t) * 10 } }
}

fn main() {
    let mut r = Box::new(cons(1, cons(3, cons(5, Nil))));
    map_inc(&mut r);
    println!("{}", digits(*r));
}
```

Surviving shifts: none. `fold_reuse` hands each node's two cells back emptied (`A″_R`); the arm
refills them, so the map allocates nothing. The algebra's type `A″_R` records this; the checker
fills it in rather than the programmer.
Rust's in-place map walks a `&mut` cursor; ours takes the list out of the borrowed cell with
`modify` and puts the mapped one back.

### 5.3 Family swap (`corpus/family-swap.bc`, answer (500, 9))

<details><summary>core, 19 lines</summary>

```
main : F (i32 * i32) =
  ra <- return (alloc[i32] i32[9]);
  rb <- return (alloc[i32] i32[500]);
  r <- return (withbor_f2_mut['c, 'a, 'b, top, i32, i32, 1] (ra, rb)
         (thunkv Fun 'c < top. return (thunkv fun (m : mut 'c i32 * mut 'c i32) ->
            let (ma, mb) = m;
            q1 <- return (withswap['c, i32, 1] ma (thunkv fun (x : i32) ->
                    q2 <- return (withswap['c, i32, i32] mb (thunkv fun (y : i32) -> return (x, y)));
                    let (mb2, y2) = q2;
                    return (y2, ())));
            let (ma2, u1) = q1;
            let () = u1;
            return (boxed['c] ()))));
  let (s, u) = r;
  let () = u;
  let (ra2, rb2) = s;
  a <- return (free[i32] ra2);
  b <- return (free[i32] rb2);
  return (a, b)
```
</details>

Surface, 7 lines:

```
main -> i32 * i32 =
  let ra = alloc(9);
  let rb = alloc(500);
  let ((ra, rb), ()) = borrow mut (ra, rb) { 'c, (ma, mb) ->
    let _ = modify ma { x -> let (_, y) = modify mb { y -> (x, y) }; (y, ()) };
    () };
  (free(ra), free(rb))
```

Rust, 6 lines:

```rust
fn main() {
    let mut a = Box::new(9);
    let mut b = Box::new(500);
    std::mem::swap(&mut *a, &mut *b);
    println!("{:?}", (*a, *b));
}
```

Surviving shifts: none. The two `modify` blocks are the two `withswap` callbacks; the family's
borrows `_` are dropped by `forget`. A library `swap_cells` would make it as short as
`mem::swap`.

### 5.4 A delay loop (`corpus/count-down.bc`, answer (inl 321, inr ()))

<details><summary>core, 55 lines</summary>

```
def ten : i32 => i32 = thunkv fun (a : i32) -> return ((unbang host[mul32]) (a, i32[10]))

-- The step: `now acc` at n = 0, else `later (n - 1, 10 acc + n)`; close has nothing to free.
-- Both components of `<,>` consume s (withI gives each the whole context).
def cd_step : !U (i32 * i32 -o F (i32 + i32 * i32) & F 1) =
  !thunkv fun (s : i32 * i32) ->
    < let (n, acc) = s;
      case (unbang host[eqz32]) n {
        inl u -> return (inr ((unbang host[sub32]) (n, i32[1]),
                              (unbang host[add32]) (ten acc, n)))
      | inr u -> return (inl acc)
      },
      let (n, acc) = s;
      return () >

main : F ((i32 + 1) * (i32 + 1)) =
  f <- return (unbang (fixd[i32, i32 * i32] cd_step));
  s0 : i32 * i32 <- return (i32[3], i32[0]);
  -- `thunkv (force f s0)` is rejected (section 6.4): eta-expand through the unrolling.
  d0 <- return (thunkv delay_in < (delay_out (force f s0)).1, (delay_out (force f s0)).2 >);
  a : i32 + 1 <-
    (o1 <- (delay_out (force d0)).1;
     case o1 {
       inl a -> return (inl a)
     | inr d1 ->
         o2 <- (delay_out (force d1)).1;
         case o2 {
           inl a -> return (inl a)
         | inr d2 ->
             o3 <- (delay_out (force d2)).1;
             case o3 {
               inl a -> return (inl a)
             | inr d3 ->
                 o4 <- (delay_out (force d3)).1;
                 case o4 {
                   inl a -> return (inl a)
                 | inr d4 ->
                     u <- (delay_out (force d4)).2;
                     return (inr u)
                 }
             }
         }
     });
  g <- return (unbang (fixd[i32, i32 * i32] cd_step));
  t0 : i32 * i32 <- return (i32[5], i32[0]);
  e0 <- return (thunkv delay_in < (delay_out (force g t0)).1, (delay_out (force g t0)).2 >);
  b : i32 + 1 <-
    (o1 <- (delay_out (force e0)).1;
     case o1 {
       inl a -> return (inl a)
     | inr e1 ->
         o2 <- (delay_out (force e1)).1;
         case o2 {
           inl a -> return (inl a)
         | inr e2 ->
             u <- (delay_out (force e2)).2;
             return (inr u)
         }
     });
  return (a, b)
```
</details>

Surface, 21 lines:

```
fn cd_step(s: i32 * i32) -> F (i32 + i32 * i32) & F 1 =
  let (n, acc) = s;
  < if n == 0 then inl acc else inr (n - 1, acc * 10 + n), () >

main -> (i32 + 1) * (i32 + 1) =
  let d0 = loop cd_step from (3, 0);
  a <- match d0.poll {
    inl a -> inl a
  | inr d1 -> match d1.poll {
    inl a -> inl a
  | inr d2 -> match d2.poll {
    inl a -> inl a
  | inr d3 -> match d3.poll {
    inl a -> inl a
  | inr d4 -> u <- d4.close; inr u } } } };
  let e0 = loop cd_step from (5, 0);
  b <- match e0.poll {
    inl a -> inl a
  | inr e1 -> match e1.poll {
    inl a -> inl a
  | inr e2 -> u <- e2.close; inr u } };
  (a, b)
```

Rust, 12 lines:

```rust
fn cd_step((n, acc): (i32, i32)) -> Result<i32, (i32, i32)> {
    if n == 0 { Ok(acc) } else { Err((n - 1, acc * 10 + n)) }
}

fn drive(mut s: (i32, i32), fuel: u32) -> Option<i32> {
    for _ in 0..fuel {
        match cd_step(s) { Ok(a) => return Some(a), Err(t) => s = t }
    }
    None
}

fn main() {
    println!("{:?}", (drive((3, 0), 4), drive((5, 0), 2)));
}
```

Surviving shifts, all visible: two `loop … from` (each allocates a delay's state), six `.poll`
and two `.close` (each runs one step), each on a `<-` or `match` head. The driver is written out
to the depth wanted, as in the core (§10: no meta-recursion). Rust's `drive` is a bounded loop;
a zoo consumer (`nth`, `take`, #48) would do the same here and bring the surface to about 6
lines.

### 5.5 A stream pipeline with take and sum (adapted from `corpus/nats-sum.bc`, answer 51)

The corpus program combines three elements as digits; this one sums them, which is the
pipeline #17 names. The core version is `nats-sum.bc` with `plus` in place of `hundred`.

<details><summary>core, 16 lines</summary>

```
def nats_step : !U (i32 -o F (i32 * i32) & F 1) =
  !thunkv fun (s : i32) ->
    < return (s, (unbang host[add32]) (s, i32[10])),
      return () >

def plus : i32 * i32 => i32 = unbang host[add32]

main : F i32 =
  f <- return (unbang (unfold_s[i32, i32] nats_step));
  z : i32 <- return i32[7];
  t0 <- return (thunkv stream_in < (stream_out (force f z)).1, (stream_out (force f z)).2 >);
  p1 <- (stream_out (force t0)).1;
  let (x1, t1) = p1;
  p2 <- (stream_out (force t1)).1;
  let (x2, t2) = p2;
  p3 <- (stream_out (force t2)).1;
  let (x3, t3) = p3;
  return (plus (plus (x1, x2), x3))
```
</details>

Surface with the zoo (#48: `take`, `sum`, not yet written), 2 lines:

```
fn nats_step(s: i32) -> F (i32 * i32) & F 1 = < (s, s + 10), () >

main -> i32 = unfold nats_step from 7 |> take(3) |> sum
```

Surface without the zoo, 7 lines:

```
fn nats_step(s: i32) -> F (i32 * i32) & F 1 = < (s, s + 10), () >

main -> i32 =
  let t = unfold nats_step from 7;
  (x1, t) <- t.next;
  (x2, t) <- t.next;
  (x3, t) <- t.next;
  x1 + x2 + x3
```

Rust, 4 lines:

```rust
fn main() {
    let s: i32 = std::iter::successors(Some(7), |s| Some(s + 10)).take(3).sum();
    println!("{s}");
}
```

Surviving shifts: `unfold … from` (the stream's state), and in the second version three `.next`
on `<-` lines. In the pipeline they are inside `take` and `sum`, library code over codata whose
types say `stream`. After fusion (C1) the pipeline is one loop.

### 5.6 Implicit drops (`corpus/implicit-drops.bc`, answer 6047)

<details><summary>core, 43 lines</summary>

```
type B = 1 + 1
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def plus : i32 * i32 => i32 = unbang host[add32]

def nil : List = roll (inl ())

def cons : i32 * List => List =
  thunkv fun (p : i32 * List) -> return (roll (inr (alloc_s[Node] p)))

-- The first element, or 0. The tail `t` is dropped.
def head : List => i32 =
  thunkv fun (l : List) ->
    case (unroll l) {
      inl u -> return i32[0]
    | inr p -> let (c, t) = p; return (free[i32] c)
    }

-- Emit the cell's value and store the next one; the close drops the cell.
def cell_step : !U (ref i32 -o F (i32 * ref i32) & F 1) =
  !thunkv fun (s : ref i32) ->
    < cx <- return (swap[i32, 1] s ());
      let (c, x) = cx;
      cu <- return (swap[1, i32] c ((unbang host[add32]) (x, i32[10])));
      let (c1, u1) = cu;
      return (x, c1),
      return () >

main : F i32 =
  r <- return (alloc[B] (inl ()));
  l <- return (cons (i32[7], cons (i32[30], nil)));
  c <- return (inr () : B);
  n <- case c {
         inl u -> return i32[1000]
       | inr u -> return (head l)
       };
  k <- return (cons (i32[9], nil));
  d <- return (inl () : B);
  m <- case d {
         inl u -> return i32[1000]
       | inr u -> return (head k)
       };
  f <- return (unbang (unfold_s[i32, ref i32] cell_step));
  z <- return (alloc[i32] i32[5000]);
  t0 <- return (thunkv stream_in < (stream_out (force f z)).1, (stream_out (force f z)).2 >);
  p1 <- (stream_out (force t0)).1;
  let (x1, t1) = p1;
  linear q <- return (alloc[i32] i32[40]);
  v <- return (free[i32] q);
  return (plus (plus (plus (n, m), x1), v))
```
</details>

Surface, 22 lines:

```
type B = 1 + 1
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def nil : List = roll inl ()
fn cons(x: i32, t: List) -> List = roll inr alloc_s[Node](x, t)

fn head(l: List) -> i32 = match unroll l { inl () -> 0 | inr (c, _) -> free(c) }

fn cell_step(s: ref i32) -> F (i32 * ref i32) & F 1 =
  < let (c, x) = swap(s, ());
    let (c, ()) = swap(c, x + 10);
    (x, c),
    () >

main -> i32 =
  let r = alloc(inl () : B);
  let l = cons(7, cons(30, nil));
  let n = match (inr () : B) { inl () -> 1000 | inr () -> head(l) };
  let k = cons(9, nil);
  let m = match (inl () : B) { inl () -> 1000 | inr () -> head(k) };
  let t = unfold cell_step from alloc(5000);
  (x1, t) <- t.next;
  linear let q = alloc(40);
  let v = free(q);
  n + m + x1 + v
```

Rust, 17 lines:

```rust
enum List { Nil, Cons(Box<(i32, List)>) }
use List::*;

fn cons(x: i32, t: List) -> List { Cons(Box::new((x, t))) }

fn head(l: List) -> i32 { match l { Nil => 0, Cons(node) => node.0 } }

fn main() {
    let _r = Box::new(false);
    let l = cons(7, cons(30, Nil));
    let n = if true { head(l) } else { 1000 };
    let k = cons(9, Nil);
    let m = if false { head(k) } else { 1000 };
    let mut cell = Box::new(5000);
    let mut t = std::iter::from_fn(move || { let x = *cell; *cell = x + 10; Some(x) });
    let x1 = t.next().unwrap();
    let q = Box::new(40);
    let v = *q;
    println!("{}", n + m + x1 + v);
}
```

Surviving shifts: `unfold … from` and one `.next`. The drops are the core's: `r`, the list not
taken by each `match`, `head`'s tail `_`, and the stream `t` (its `close` frees the cell). Rust
has no `linear`; `q` is an ordinary `Box`.

### 5.7 Effects as capabilities (sketch against #18; no core version)

A generic `walk` is used with a returning callback (`report`, logging) and with a suspending
callback (`produce`, a generator). Nothing here type-checks yet; the forms are those of 2.11.

Surface, 11 lines:

```
cap Log { emit(x: i32) -> 1 }
cap Gen { yield(x: i32, k: {1 -> r}) -> r }

fn walk[C]<'l, 'h>(xs: imm 'l List, c: imm 'h C, f: !{imm 'h C * i32 -> 1}) -> 1 =
  for x in iter(xs) { f!(c, *x) }

fn report<'l, 'h>(xs: imm 'l List, log: imm 'h Log) -> 1 =
  walk[Log](xs, log, !{ (log, x) -> log.emit(x) })

fn produce<'l, 'h>(xs: imm 'l List, gen: imm 'h Gen) -> 1 =
  walk[Gen](xs, gen, !{ (gen, x) -> suspend gen.yield(x) })

fn logged<'l, 'o>(xs: imm 'l List, out: mut 'o Buf) -> 1 =
  handle Log { emit(x) -> push(out, x) } in { log -> report(xs, log) }

fn total<'l>(xs: imm 'l List) -> i32 = generate { gen -> produce(xs, gen) } |> sum
```

Rust, 6 lines:

```rust
fn walk(xs: &[i32], mut f: impl FnMut(i32)) {
    for x in xs { f(*x) }
}

fn report(xs: &[i32], log: &mut Vec<i32>) { walk(xs, |x| log.push(x)) }

// `walk` cannot suspend on stable Rust: the producer is a separate iterator.
fn produce(xs: &[i32]) -> impl Iterator<Item = i32> + '_ { xs.iter().copied() }

fn total(xs: &[i32]) -> i32 { produce(xs).sum() }
```

`walk` is written once and carries no mark. Its instantiation in `report` is a loop of direct
calls (the `Log` handler answers `emit` by calling `push`). Its instantiation in `produce`
contains a suspension point, so `generate` compiles it to a stackless state machine whose
state is the reified continuation (decision 25). The visible costs are `suspend` (the
continuation) and `generate { … }` (the state machine). Rust needs two shapes: `walk` cannot
suspend on stable Rust, so the producer is a separate iterator, and an `async` version of
`walk` would be a third function.

### 5.8 What the counts say

- The surface is 40% of the core (81 against 203 lines) and 121% of Rust (81 against 67). Most
  of the gap to Rust is in 5.4 (the driver written out, 9 lines) and 5.6 (type and shape
  declarations that Rust folds into one `enum`, and the step's two `swap`s where Rust assigns
  through a `Box`, 5 lines).
- Every surviving shift in the surface examples is on a line with `<-`, `.poll`/`.next`/
  `.close`, `!`, `loop`, `unfold`, `generate` or `suspend`, and each such token marks one. The
  one token that can mark a shift that cancels is `!{ … }` passed to `walk` in 5.7: closed code,
  whose force cancels once `walk` is specialized (Q2, Q4). That is the success condition of
  #54, checked by hand here and to be checked cold in step 4.

## 6. Prior art

Entries marked *(unverified)* are from memory and have not been checked against the source.

- **Levy's call-by-push-value.** P. B. Levy, "Call-by-Push-Value: A Subsuming Paradigm", TLCA
  1999, LNCS 1581; *Call-By-Push-Value: A Functional/Imperative Synthesis*, Semantic Structures
  in Computation 2, Springer, 2003. The source of the value/computation split, `U`/`F`, and
  `M to x. N` (our `x <- M; N`). Levy's term syntax writes application operand-first (`V'M`)
  and every `thunk`/`force` explicitly *(unverified: the exact notation)*. We take the split
  and the cancellation equations; we avoid the operand-first spine and the explicit forces,
  which are what makes the core long.
- **Frank.** S. Lindley, C. McBride, C. McLaughlin, "Do Be Do Be Do", POPL 2017
  (arXiv:1611.09259). A CBPV-inspired language in which `{ … }` is a suspended computation,
  `!` forces a nullary one, application forces implicitly, and handlers are n-ary operators
  that pattern-match on commands. Effect variables are implicit through an ambient ability
  *(unverified: the details of ability inference)*. We take braces and `!`, and implicit
  forcing when calling. We avoid the ambient ability, which still puts effects in types: our
  effects are arguments (#18).
- **Effekt.** J. I. Brachthäuser, P. Schuster, K. Ostermann, "Effects as Capabilities: Effect
  Handlers and Lightweight Effect Polymorphism", OOPSLA 2020; J. I. Brachthäuser, P. Schuster,
  E. Lee, A. Boruch-Gruszecki, "Effects, Capabilities, and Boxes", OOPSLA 2022 (System C);
  P. Schuster, J. I. Brachthäuser, K. Ostermann, "Compiling Effect Handlers in
  Capability-Passing Style", ICFP 2020. Capabilities are passed as arguments, blocks
  (functions) are second-class by default, and `box` makes one first-class with a capture set
  *(unverified: the capture-set syntax)*. This is the closest design. Our second-class blocks
  are the keyword-attached ones of 2.6–2.9, our first-class ones are expression-position
  `{ … }`, and our capture discipline is borrow lifetimes rather than capture sets. We take
  capability passing and the second-class default; we avoid a separate capture-set language,
  since lifetimes already bound what a borrowed capability can reach.
- **Koka.** D. Leijen, "Type Directed Compilation of Row-Typed Algebraic Effects", POPL 2017;
  N. Xie, J. I. Brachthäuser, D. Hillerström, P. Schuster, D. Leijen, "Effect Handlers,
  Evidently", ICFP 2020; N. Xie, D. Leijen, "Generalized Evidence Passing for Effect
  Handlers", ICFP 2021. Effects are row-typed; operations are declared `fun` (tail-resumptive,
  run in place) or `ctl` (general control) *(unverified: the current keyword set)*; dot-call
  `x.f(y)` and trailing lambdas make pipelines read well. We take the cost model (a
  tail-resumptive operation is a call, dream property C5) and the pipeline ergonomics (`|>`).
  We avoid effect rows, which colour every signature, and the `fun`/`ctl` keyword, which we
  read off polarity instead (#52).
- **Polarized languages.** P. Downen, Z. M. Ariola, "A Tutorial on Computational Classical
  Logic and the Sequent Calculus", JFP 28, 2018; "Compiling with Classical Connectives", LMCS
  16(3), 2020; P. Downen, Z. Sullivan, Z. M. Ariola, S. Peyton Jones, "Codata in Action", ESOP
  2019; N. Zeilberger, *The Logical Basis of Evaluation Order and Pattern-Matching*, PhD
  thesis, CMU, 2009. Polarity and shifts as the account of evaluation order, and codata as a
  programming abstraction observed by projection. We take shifts as the carriers of cost and
  codata observation as `.next`/`.close`. We avoid a sequent-calculus surface (`μ`/`μ̃`) and
  first-class continuations as a user form: a continuation appears only as a handler's `k`.
- **Copatterns.** A. Abel, B. Pientka, D. Thibodeau, A. Setzer, "Copatterns: Programming
  Infinite Structures by Observations", POPL 2013. Codata defined by what each observation
  returns, which is our `< next, close >` step. We do not adopt copattern definitions; a step
  function over explicit state (decision 24) is enough.
- **Function colouring.** B. Nystrom, "What Color is Your Function?", 2015 (blog). Rust's
  `async fn`/`.await` and Kotlin's `suspend fun` mark functions; OCaml 5 avoids colouring
  with stackful fibers (K. C. Sivaramakrishnan et al., "Retrofitting Effect Handlers onto
  OCaml", PLDI 2021). Stackful fibers are ruled out by decision 25, so we avoid colouring by
  capability arguments and monomorphization, and mark only the operation call.

## 7. Open questions

- **Q1. Hole filling (3.2).** The surface is pleasant only if the checker fills bracket
  arguments, `fun` binder types, lifetime arguments and fold algebra types. Which holes are
  always fillable by synthesis, and which need an ascription, is not worked out rule by rule.
  It is a core-syntax draft 2 item.
- **Q2. Do expression braces need a cost mark?** A keyword-attached block never allocates. An
  expression `{ … }` allocates only if it captures and escapes, which C2 decides after
  specialization. Should the surface distinguish a known non-escaping `{ … }` from an escaping
  one (like Rust's `move`, or Effekt's `box`), or should a tool report it?
- **Q3. `imm` variables in loop bodies.** A `for` body that uses an `imm` borrow must thread it
  and hand it back, which needs `copy` at each use. The pleasant form needs the checker to
  insert `copy` for `imm` variables, as it inserts destructors (SPEC §12). That would be a
  spec entry ("implicit copies"), not sugar. Capabilities passed as `imm` borrows (2.11) depend
  on it.
- **Q4. `!` on calls through parameters of macro-expanded defs.** `f!(c, *x)` in `walk` is
  marked, but every use of `walk` is re-checked with `f` a known literal (§10), so the force
  cancels. The mark is conservative. Is it noise?
- **Q5. Integer widths.** Operators are `i32`. Overloading by width needs the checker to
  resolve it (a typed elaboration, like holes).
- **Q6. Implicit `close`.** An implicit drop of codata forces it and runs `close`, a surviving
  force the programmer did not write. SPEC §12 places it at the end of the path. Should the
  surface mark scopes that end with a codata drop?
- **Q7. The effect forms.** `cap`, `handle`, `suspend` and `generate` (2.11) are a sketch. Their
  core is #18 (shallow handlers on general `ν`, one-shot continuations with a `close` path).
  Whether a handler-side signature with a continuation parameter is the whole polarity story,
  and how a capability-polymorphic call through unknown code is represented (#52: the general
  representation, visible in types), are open.
- **Q8. `let` against `<-`.** This draft makes `<-` mean "forces a live object" and warns
  elsewhere. Step 4's cold review should say whether readers use that signal, or whether one
  binder is simpler.
- **Q9. Named constructors and nested patterns.** `inl ()`/`inr (c, t)` are the core's sums.
  Named variants (#19) and match compilation would shorten every fold and `match`; the latter
  must keep §7's per-arm consumption visible.
- **Q10. Where `|>` puts the piped value.** Last argument (#17). Koka's dot-call puts it first
  *(unverified)*. The zoo's argument order (#48) should be fixed with it.
