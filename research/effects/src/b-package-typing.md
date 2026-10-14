# B on paper: typing the package construct against its programs

This is a paper exercise, not a proof. Nothing here is proved in Lean. It asks one question before
anyone proves the fundamental property over a new lifetime carrier: **does the package construct
of problem B ([tier 2 problems](tier2-problems.md), B) express the programs it is for?**

What was run, as opposed to written:

- the checker census of §3, a local diagnostic build of `bcc`, not committed;
- two hand-segmented programs (P5, P6 below), checked and run by today's `bcc`;
- two checks that a stored generator can be returned from a function but cannot leave a borrow
  block (P3).

Everything else, including every derivation over the new rules, is checked by hand only.

Notation: `[TR]`'s, with Core's constants as in `Core/Types.lean` and `Core/Fundamental.lean`.
`S(b)` is the parent set a bound `@b` names (below). Every rule marked **NEW** is not in Core
today. Every **ADD-n** is something the construct as briefed does not contain, with its reason.

## 1. The rules

### 1.1 The lifetime context as a partial order

A context `Δ` is Core's list of entries `'x ⊏ @b`, unchanged in syntax. It is read as **parent
sets**:

- `@b` is `⊤` or a meet `'s₁ ⊓ … ⊓ 'sₙ` of variables already in `Δ`;
- `S(b) = {s₁, …, sₙ}` are the parents of `'x`, with `S(⊤) = ∅`;
- `⟦Δ⟧` is the set of readings `δ` of `dom Δ` into a partial order with `⊤` and no infinite
  ascending chain (Nominal's free order of atoms is one), with `δ(x) < δ(s)` for every
  `s ∈ S(Δ(x))`.

Lifetime expressions are read in two ways, as in Nominal's `LtLifeN`/`interpN`:

- **Bound positions** (a `∀` bound, a `Δ` entry, `withbor`'s `⊓Δ`). `α ⊏ s₁ ⊓ … ⊓ sₙ` means
  `α` is beneath every `sᵢ`. No greatest lower bound is needed.
- **Value positions** (the lifetime of `Imm @a`, `Mut @a`, `[@a]`, the instantiation of `∀E`, the
  target of `immSub`/`mutSub`). A variable or `⊤`, or a meet or join only of components that `Δ`
  makes comparable, where it denotes the shorter or the longer. Otherwise it is undefined:
  `Δ ⊨ @a` fails.

`Δ ⊨ @a ⊏ @b` and `Δ ⊨ @a ⊑ @b` quantify over these readings.

### 1.2 Existing Core rules that change

| rule | today | over parent sets | kind |
|---|---|---|---|
| `LifeCtx.Models`, `EntailsLt`, `EntailsLe`, `Defines` | `ℕ`-valued readings (a chain) | the readings of §1.1; a meet or join at a value position is defined only on comparable components | changed meaning, same syntax |
| checker `ordB` | two strict rules valid on chains only: `@a ⊏ @b₁ ⊓ @b₂` from both, `@a₁ ⊔ @a₂ ⊏ @b` from both | both dropped where the meet or join is a value. At a bound, the first is the definition of the bound reading and stays | changed. §3: no corpus program uses either |
| `withbor1/2/3`, `withload`, `sliceBorrowM/I` and their unwinding forms | `'x ⊏ @(⊓Δ)` | `'x` beneath every lifetime of `Δ` | same text, bound reading |
| `allE`, `allEV`, `immSub`, `mutSub` | premise over `ℕ` | premise over the readings of §1.1 | same text |
| `VOutlivesR` (`⊐` and `⊒`), so `boxI`'s `CtxOutlives` and `withbor2`'s side condition | no case for the package | one new case, §1.3 | **NEW** case |
| `VTy.immReborrow` | — | `Imm̲` of a package is `Unk` | **NEW** case, ADD-7 |
| `HasDtor` (§12) | — | a package has a destructor | **NEW** case, ADD-3 |
| `Persistent` | — | a package is never persistent | no case |
| elaboration of `dom` as an instantiation value (§15, §23) | the meet of the lifetimes in scope | undefined when they are incomparable, as inside an open, ADD-6 | elaboration |

The model side (strata indexed by sets, the two readings of `[α]`, `○` at comparable `mut`
cells) is the Nominal port map (`experiments/Nominal/README.md` §6), not repeated here.

### 1.3 New: the package

**Lend kinds.** A package owns one place and lends it at each opening. Each lend kind is a
borrow constant Core already has:

| `κ` | owned place `Src_κ A` | lend at `'x`, `Lend_κ('x, A)` | mirrors |
|---|---|---|---|
| `imm` | `Ref A` | `Imm 'x A` | `withbor1` |
| `mut` | `Ref A` | `Mut 'x A` | `withbor2` |
| `imm[]` | `Array A` | `ArrayImm 'x A` | `slice_borrow_imm` |
| `mut[]` | `Array A` | `ArrayMut 'x A` | `slice_borrow_mut` |

Nominal's semantic package (`Pkg`, `Pkg.Opens`) has one `mut` cell. The other three kinds are
**ADD-4**: they mirror existing constants, but they are not modelled. P1, P3, P4 and P6′ need a
family kind.

**Types (NEW).**

    ∃'x ⊏ @b. ⟨κ A⟩ T      the package: owns a place Src_κ A; its contents are typed T in 'x
    ⌈'x⌉ T                  closable contents: a value of T that may be stored when 'x ends

Well-formedness of the package:

- `Δ ⊨ @b`, with `@b` of the form of §1.1;
- `'x` is bound in `T` only, and is free in neither `A` nor `@b`;
- `FV(T) ⊆ dom Δ ∪ {'x}`.

`⌈'x⌉ T` occurs only as the result of a package constant's callback.

**Two outlives judgments relative to a parent set.** They are `VOutlivesR` at predicates (so
neither descends into `U`, `⊸` or `∀`, which have no outlives rule, nor into a borrow's
payload):

    Δ ⊢ A ⊒ S        ≜ VOutlivesR P P A,     P(ℓ)  ≜ ∃ s ∈ S. Δ ⊨ @s ⊑ @ℓ
    Δ ⊢ Γ ⊒ₓ S       ≜ every live slot of Γ satisfies VOutlivesR Pₓ Pₓ,
                         Pₓ(ℓ) ≜ ℓ ≡ 'x ∨ ∃ s ∈ S. Δ ⊨ @s ⊑ @ℓ

With `S = ∅`, `A ⊒ ∅` says that `A` mentions no lifetime at a borrow or box.

**Constants (NEW)**, each at a dead context, CBV as `[TR]` p. 3's table:

    pkg_new_κ : Src_κ A ⊸ (∀'x ⊏ @b. Lend_κ('x, A) ⊸ ⌈'x⌉ T) ⊸ ∃'x ⊏ @b. ⟨κ A⟩ T
    pkg_use_κ : (∃'x ⊏ @b. ⟨κ A⟩ T) ⊸ (∀'x ⊏ @b. T ⊸ ⌈'x⌉ T′ ⊗ ['x] B) ⊸ (∃'x ⊏ @b. ⟨κ A⟩ T′) ⊗ B
    pkg_end_κ : (∃'x ⊏ @b. ⟨κ A⟩ T) ⊸ (∀'x ⊏ @b. T ⊸ ['x] B) ⊸ Src_κ A ⊗ B          (ADD-2)

Side conditions:

| | `pkg_new_κ` | `pkg_use_κ` | `pkg_end_κ` |
|---|---|---|---|
| bound | `@b` chosen by the creator, `Δ ⊨ @b` | the package's `@b` | the package's `@b` |
| freshness | `Δ.find? 'x = none` | same | same |
| payload | `Δ ⊢ A ⊒ S(b)`; at `imm`, `VScoped Δ A` | — | — |
| free variables | `'x ∉ FV(A)`, `FV(T) ⊆ dom Δ ∪ {'x}` | `'x ∉ FV(B)`, `FV(T′) ⊆ dom Δ ∪ {'x}` | `'x ∉ FV(B)` |

The terms are `withbor`'s, with no new machine step. A package value is the pair of the place's
handle and the contents.

- `pkg_new = λs. λg. (s, g () s)`, which is `withbor`'s own term.
- `pkg_use = λp. λg. let (s, w) = p in let (w′, r) = g () w in ((s, w′), r)`.
- `pkg_end = λp. λg. let (s, w) = p in (s, g () w)`.

**Open is nominal.** Each callback's binder is `∀'x ⊏ @b`, with the package's own `@b`. `withbor`
uses `⊓Δ`, which would put the new `'x` beneath the opener's lifetimes: the positional re-make
that probes 3–6 refuted. The semantics instantiates `'x` at a fresh atom with parents `S(b)`
(Nominal's `reopen_swap`). The opener's lifetimes stay incomparable to it. Borrows made inside
the callback take `'y ⊏ ⊓Δ′` over `Δ′ = Δ, 'x ⊏ @b`, so they lie beneath both.

**`pkg_use` may change the contents' type** (`T` to `T′`). This is a choice within close and
open, not an addition: the closed package is typed at whatever its close typed it at, and
equivariance does not look at `T`. Segmenting a body at several stops (P3) uses it.

**Close (NEW): `[closeI]`, its premise ADD-1.**

    Δ; Γ ⊢ e : T        Δ(x) = @b        Δ ⊢ Γ ⊒ₓ S(b)
    ────────────────────────────────────────────────── [closeI]   (same term, as []I)
    Δ; Γ ⊢ e : ⌈'x⌉ T

> **ADD-1.** The brief's close asks only that every borrow at `'x` has ended, `boxE`: the
> contents keep no cell at or beneath `'x`. That does not justify the storage rule below.
>
> - Open an owned package (`S = ∅`) whose contents hold a closure `U(F i32)`.
> - Inside the open, replace the closure with one that reads a local `z` through `Imm 'r i32`,
>   where `'r` belongs to the opener and is incomparable to `'x`.
> - Close. The new closure's cell is at `'r`, which is not at or beneath `'x`, so `boxE` holds.
> - The package type mentions no `'r` and outlives everything, so it can be returned past `'r`'s
>   end and `z` freed.
> - The next opening calls the closure, which reads freed memory.
>
> So close must check where every cell of the contents lies, not just that `'x`'s have ended.
> The check is on the **context** the contents are built from, as `[]I`'s is, because a closure's
> type hides what it captures. `'x` itself is allowed: the only cells at `'x` are the lend and its
> copies, since `withbor3` and `withload` make fresh lifetimes strictly beneath `'x` and
> `immSub`/`mutSub` only shorten. For contents with no `U`, `⊸` or `∀` in them, typing `e : T` at
> the package's `T` already implies the premise.

**Outlives (NEW case of `VOutlivesR`), the brief's storage rule.**

    ∀ s ∈ S(b). Rr(s)        VOutlivesR Rb Rr A
    ──────────────────────────────────────────────────
    VOutlivesR Rb Rr (∃'x ⊏ @b. ⟨κ A⟩ T)

With `Rr = (Δ ⊨ @a ⊏ ·)` this gives `Δ ⊢ ∃…  ⊐ @a`; with `⊑`, the `⊒` form.

- `S = ∅`: the package outlives every lifetime. It borrows only its own place, so it is an owned
  value.
- `S ≠ ∅`: every parent must outlive `@a`. This is Rust's `T: 'q`.

`T` is not inspected. ADD-1 is what makes that sound: every cell of the contents other than the
lend lies at or above some parent. This mirrors Nominal's `closed_inStratum` and
`vN_store_captured_iff`.

**ADD-7.** `Imm̲` of a package is `Unk`. If a package behind an `Imm` borrow could be opened, two
readers could hold lends at `'x′` and `'x″` of one cell, and at `κ = mut` both would be `mut`.

**ADD-3: the destructor (§12).** A package has a destructor when `Src_κ A` has one and the
contents drop at `'x`. It is `pkg_end` with a callback that forgets the contents' borrows and
destroys what they own, followed by `Src`'s destructor. This is needed whenever a package is held
across an affine operation (drop glue, §19's `[then]`) or dropped implicitly.

**Unwinding forms (NEW, by §19's pattern).** `pkg_new_κU`, `pkg_use_κU` and `pkg_end_κU` take a
callback at `F_Σ(…)` with `Row.Unwind 'x`, wrapped in `ubind`. On unwind, the contents are
abandoned by the callback's own drop glue, and the place's destructor runs. The package is lost.
No program below uses them.

### 1.4 How the package meets the rest of Core

| feature | interaction |
|---|---|
| `withbor1/2/3`, `withload`, slice borrows inside an open | unchanged constants. The fresh `'y ⊏ ⊓Δ′` lies beneath the package's `'x` and the opener's lifetimes. Its result is `['y] B`, so a `'y` cell never reaches a `[closeI]` context (where `Pₓ('y)` would fail anyway) |
| reborrow out of the package (C) | none. A borrow derived from the contents leaves the callback only in `['x] B`, which refuses anything at `'x` |
| outlives, `[]I` | the new `VOutlivesR` case. `[@a] (∃…)` by `[]I` when the context outlives `@a` |
| `U`, thunks | a thunk **formed** inside the callback is closable when its captures pass `⊒ₓ`. A `U` value **received** as a slot is not closable (no outlives rule for `U`, as `[]I` today). See P2b |
| `∀` over lifetimes | callbacks are ordinary `∀'x ⊏ @b` values (`allI` unchanged, its `hΓx` met). `allE` instantiates a function at the package's `'x′` when `'x′` is beneath its bound, e.g. `∀'a ⊏ ⊤` |
| `perform`/`handle` | unchanged. A resuming operation may not occur in a package callback (`Row.Unwind`): T1 stays. A suspension holds a **closed** package across the stop, which is an owned value with a destructor (ADD-3) |
| stored continuations | a `κ` holding a closed package is an ordinary `U` value: returned from functions, stored, resumed. Like every `U` value, it cannot leave a borrow block (P3) |
| cancellation | cancelling a `κ` that holds a closed package runs the package's destructor. No lend is live, so none has to end |

### 1.5 Elaboration (frontend only)

**ADD-5: segmenting a borrow block at a resuming operation.** A borrow block of a place the
suspending body owns, whose body performs a resuming operation (`yield`, an `await`), is split at
each such operation into segments. The operation runs between segments, outside every lend.

- When the only value crossing the operation whose type mentions `'x` is the lend itself, each
  segment is an ordinary `withbor`. **No package, no kernel change.** This is how §14's
  `LoopLend` already re-lends at each observation.
- When derived values cross it (a leaf view, a reborrowed part, a closure over the borrow), the
  block becomes `pkg_new`, one `pkg_use` per segment, and `pkg_end`. The contents are those
  values.
- A `match` spanning a stop needs the contents to carry the branch, with an unreachable arm after
  the stop (the state-machine union of §14).

This is `LoopLend`'s mechanism moved from an observation boundary to a resuming operation.
`LoopLend` reports *"a stretch before the loop that hands on something with `'x` in its type"*:
the package is the construct that case lacks.

**ADD-6: `dom` inside an open.** The meet of the lifetimes in scope is not a value when the
package's `'x′` is incomparable to the opener's. A call inside an open that leaves a lifetime
argument undetermined has nothing to instantiate. It would need a fresh lifetime beneath both
(§23 Open, *a lifetime without a cell*). None of P1–P7 as written needs it.

## 2. The programs

The surface for packages does not exist. Surface marked *hypothetical* is a sketch. The
elaborations are in Core's text with the new constants. `Δ` is listed at each step, and each
side condition is checked against it.

### P1. A struct owning a buffer and a borrow into it, built in a function, returned, read

*Hypothetical surface:*

    type Line = exists 's. own array i32 => imm 's i32 + 1    -- a buffer and a view into it
    fn tab(i: i32) -> i32 = i * 10
    fn build() -> Line =
      let a = array_new[i32] (5, tab);
      pack a as 's { v ->                                  -- v : array_imm 's i32
        let (v1, v2) = array_copy['s, i32] v;
        let _ = array_forget['s, i32] v1;
        array_get['s, i32] (v2, 3) }                       -- the contents: a view of a[3]
    fn peek(l: Line) -> Line * i32 =
      open l as 's { e -> match e {
        inl g -> let (g1, g2) = copy['s, i32] g; (inl g1, *g2)
      | inr u -> (inr u, 0) } }
    main -> i32 =
      let l = build();
      let (l, x) = peek(l);
      let (l, y) = peek(l);
      x + y                                                -- l dropped: 60, live 0

*Elaboration.* `Line ≜ ∃'x ⊏ ⊤. ⟨imm[] i32⟩ (Imm 'x i32 ⊕ 1)`.

    build = a ← array_new (5, tab);
            pkg_new_imm[] [⊤] a (Λ'x. λv. (v1, v2) ← array_copy['x] v; array_forget['x] v1;
                                         g ← array_get['x] (v2, 3); return g)
    peek  = λl. pkg_use_imm[] l (Λ'x. λe. case e {
              inl g → (g1, g2) ← copy['x] g; n ← read['x] g2; return (inl g1, n)
            | inr u → return (inr u, 0) })
    drop l = pkg_end_imm[] l (Λ'x. λe. case e { inl g → forget g | inr _ → () }; return ());
             then array_free on the array that comes back

*Derivation.*

1. `build`, `Δ = ∅`: `build` has no lifetime parameters and does not name `'main`.
   - `arrNew` gives `a : Array i32`.
   - `pkg_new_imm[]` at `@b = ⊤`: `Δ ⊨ ⊤` ✓, `S = ∅`, `'x` fresh ✓, payload `Δ ⊢ i32 ⊒ ∅` by
     `VOutlivesR.int` ✓, `'x ∉ FV(i32)` ✓, `FV(T) = {'x}` ✓.
   - The callback, by `allI` at `Δ′ = ('x ⊏ ⊤)`: `hbx`, `hΔx` ✓, and its context is dead ✓.
     `lam` gives `v : ArrayImm 'x i32`.
   - `arrCopy`, `arrForget` and `arrGet` at `@a = 'x`. Each is a constant at any lifetime, and
     `array_get` hands out a leaf at the family's own lifetime (§9).
   - `[closeI]` on `g`, context `{g : Imm 'x i32 ⊕ 1}`: `VOutlivesR Pₓ Pₓ` at `⊕`, then `imm 'x`:
     `Pₓ('x)` by `ℓ ≡ 'x` ✓.
2. `peek`, `Δ = ∅`.
   - `pkg_use_imm[]`: the bound is the package's `⊤`, `'x` fresh ✓, `B = i32` and `'x ∉ FV(B)` ✓,
     `T′ = T`.
   - In the callback, `Δ′ = ('x ⊏ ⊤)`.
   - `sumE` on `e`; `copy` at `'x` ✓.
   - `read['x] g2` is `withload['x, 'w, i32, i32] g2 (Fun 'w < dom …)`: `'w ⊏ ⊓Δ′`, a bound, so
     `'w` is beneath `'x` ✓. Its result is `boxed['w] n` with `n : i32` ✓.
   - `[closeI]` on `inl g1`, context `{g1 : Imm 'x i32}` ✓.
   - `boxed['x] n` by `[]I`: `i32 ⊐ 'x` ✓.
3. The drop, by `pkg_end_imm[]`: `forgetImm` at `'x` ✓, `boxed['x] ()` ✓. The array comes back
   and `arrFree` frees it.
4. Returning `Line` from `build` needs nothing: a function result has no outlives premise, and
   `Line` has no free lifetime.
5. Had `peek` run where the opener has lifetimes, for example `'r`, the new `'x′ ⊏ ⊤` is
   incomparable to `'r`. `withload`'s `'w ⊏ 'x′ ⊓ 'r ⊓ …` is still a bound: beneath both ✓.

**Verdict: TYPES WITH ADDITIONS:** ADD-4 (`imm[]`), and ADD-2 or ADD-3 for the drop.
**Needs besides B:** nothing; no effects.

*Today, without the package:* store the index `3` and borrow again at each read. The package
matters when the view comes from a computation the program does not want to repeat, such as a
search.

### P2. A closure owning a cell and a borrow of it, returned, called twice

**Qualifier: affine.** `Aff^c` (§22) can be called any number of times and then closed. A linear
`U(A ⊸ F B)` could be called once.

*Hypothetical surface:*

    type Counter = exists 's. own mut i32 => mut 's i32
    fn counter<'c>(start: i32) -> box 'c Aff[i32, i32]<'c> =
      let p : Counter = pack alloc(start) as 's { m -> m };
      aff_new_boxed[Counter, i32, i32]['c](p, !thunkv fun (p : Counter) ->
        < fun (a : i32) ->
            let (p, t) = open p as 's { m ->
              let (m, r) = withswap['s, i32, i32] m (fun (i : i32) -> (i + a, i + a));
              (m, r) };
            return (t, p),
          let (c, _) = unpack p as 's { m -> forget m };  let _ = free(c); return () >)
    main -> i32 =                                          -- as corpus/aff-counter.bc
      let c = alloc(counter(10));
      let t = borrow mut c { 'w, m ->
        let (m, x) = aff_call_mut(m, 1); let (m, y) = aff_call_mut(m, 2); x + y };
      let k = free(c); aff_close(k); t                      -- 24, live 0

*Derivation.* `Counter ≜ ∃'x ⊏ ⊤. ⟨mut i32⟩ Mut 'x i32`.

1. `pkg_new_mut`, in `counter`'s `Δ = ('c ⊏ ⊤)`.
   - The creator picks `@b = ⊤`, so `S = ∅` and `'x` is incomparable to `'c`.
   - `Δ ⊨ ⊤` ✓; `i32 ⊒ ∅` ✓; `'x` fresh ✓.
   - `[closeI]` on `m`, context `{m : Mut 'x i32}`: `Pₓ('x)` ✓.
2. `aff_new_boxed[Counter, i32, i32]['c]`, a template instance.
   - Its bound `where S: 'c` adds the lifetimes `Counter` mentions, and there are none (`'x` is
     bound). So `'c ⊏ ⊤` is unchanged.
   - Its `boxed['c] aff_new(s, step)` is `[]I` with context `{s : Counter, step : !U…}`.
     `Counter ⊐ 'c` by the new case: `S = ∅` is vacuous and `i32 ⊐ 'c` ✓. `!` ✓.
   - Its `boxed['c] s1` on the rest's state passes the same way ✓.
3. The step's `call` branch: `pkg_use_mut` at the package's `⊤`, `'x` fresh ✓, `B = i32` ✓.
   - `withswap['x, i32, i32]` has no lifetime premise ✓.
   - `[closeI]` on `m` ✓; `boxed['x] r` ✓.
4. The step's `close` branch: `pkg_end_mut`, `forgetMut` at `'x` ✓, then `free` the `Ref i32` ✓.
5. `main` is `corpus/aff-counter.bc`'s, unchanged.

**Verdict: TYPES WITH ADDITION** ADD-2 (ADD-3 if dropped implicitly). **Needs besides B:**
nothing.

*Degenerate.* The contents are the lend itself, and `corpus/aff-counter.bc` already writes this
closure today with state `Ref i32`, borrowing again at each call. P2 as specified does not need
the package. A closure that owns an array and a leaf view chosen when it is built has
non-degenerate contents and types the same way, at `imm[]`.

### P2b. The same closure as the package's contents (`T` a closure type)

Let the contents be the closure itself:

    ∃'x ⊏ ⊤. ⟨mut i32⟩ U(νX. (i32 ⊸ F(i32 ⊗ U X)) & F 1)

The closure is formed in `pkg_new`'s callback over `m : Mut 'x i32`, and `[closeI]` passes
(`Pₓ('x)`). The first call opens it and takes the rest `r : U X` from the observation. Re-closing
needs `[closeI]` on a context containing `r : U(…)`, and `VOutlivesR` has no case for `U`.

**Verdict: DOES NOT TYPE.** The failing side condition is `Δ ⊢ Γ ⊒ₓ S` at the slot of the
observed rest.

The construct closes a closure only where it is formed. This is the same reason
`corpus/reject/lend-iter-borrow.bc` (an iterator holding the borrow) stays rejected with the
package. What it would take is a closable rest, `⌈'x⌉ U X` inside a `ν` body, the analogue of
`Aff`'s `[@c] U X`. That is not adopted here, and it would be a further addition.

### P3. A generator holding a borrow of its own local across a yield, stored, returned, resumed elsewhere

*Surface (today's, plus the self-borrow):*

    include yield
    fn tab(i: i32) -> i32 = i * 10
    fn gen() -> 1 with Yield[i32] =
      let a = array_new[i32] (5, tab);
      borrow imm a { 'x, v ->
        let (v1, v2) = array_copy['x, i32] v;
        let _ = array_forget['x, i32] v1;
        match array_get['x, i32] (v2, 3) {
          inl g -> let (g1, g2) = copy['x, i32] g;
                   yield(*g1);              -- g2 : imm 'x i32 is live across this yield
                   yield(*g2 + 1)
        | inr _ -> ()
        } }
    fn make() -> U (pull i32 1 1) =
      let g : U (pull i32 1 1) = gen();     -- stored
      g                                     -- returned from the function that created it
    main -> i32 =
      let g = make();
      let mut acc = 0;
      for x in g { acc = acc + x };         -- resumed elsewhere, consumed by for: 61, live 0

*Elaboration (ADD-5).* `P ≜ ∃'x ⊏ ⊤. ⟨imm[] i32⟩ (Imm 'x i32 ⊕ 1)`. `gen`'s body at row
`Yield[i32]` with the threaded `w`:

    a ← array_new (5, tab);
    p ← pkg_new_imm[] [⊤] a (Λ'x. λv. (v1, v2) ← array_copy v; array_forget v1;
                                    e ← array_get (v2, 3); return e);
    (p, s) ← pkg_use p (Λ'x. λe. case e {
                 inl g → (g1, g2) ← copy g; n ← read g1; return (inl g2, inl n)
               | inr u → return (inr u, inr ()) });
    case s {
      inl n → w ← perform yield (n, w)          -- [then] … unwind drop p
              (p, m) ← pkg_use p (Λ'x. λe. case e {
                           inl g2 → n2 ← read g2; return (inr (), n2 + 1)
                         | inr u → return (inr u, 0) });          -- unreachable arm
              w ← perform yield (m, w)          -- [then] … unwind drop p
              drop p
    | inr () → drop p }

*Derivation.*

1. `pkg_new_imm[]` as in P1.1. Here `Δ_gen = ∅`, and ADD-5 takes `@b := ⊓Δ = ⊤`, as `withbor`
   would.
2. The first `pkg_use`.
   - `[closeI]` on `inl g2`, context `{g2 : Imm 'x i32}` ✓.
   - The second component, `inl n : i32 ⊕ 1`, is boxed at `'x` by `[]I` ✓, and `'x ∉ FV(i32 ⊕ 1)`
     ✓.
3. `perform yield (n, w)`.
   - `effPerform`: `yield : i32 ⊗ W ↠ W`, affine, not abortive ✓.
   - The `perform` is in no package callback and no borrow callback, so `Row.Unwind` is not asked:
     **T1 is not involved**.
   - The rest of the body holds `p`, which is owned, so the `[let]` side condition (`Γ₂` drops)
     fails and the elaborator's drop glue is `effThen` with `D = drop p : F 1`. `drop p` is
     `pkg_end` plus `arrFree`, which is ADD-3. `effThen`'s `NZ`/`Uniq` hold ✓, and `D` is at the
     pure row ✓.
4. The second `pkg_use`: contents `T → T` ✓; the closed contents `inr ()` have an empty context ✓.
5. The stored generator.
   - §15's handler site whose clause does not resume:
     `thunkv nu_in ⟨(force k).1 (), (force k).2⟩`.
   - `k` is the affine continuation holding the closed `p`.
   - `make` returns `F (U (pull i32 1 1))`, with no outlives premise.
   - `main`'s `for` over a stored generator is §15's.
   - An early `break` cancels `k`, whose finaliser drops `p`. No lend is live.

**Verdict: TYPES WITH ADDITIONS:** ADD-2/3, ADD-4 (`imm[]`), ADD-5. **Needs besides B:** not A
(T1 stays), not E (no capability crosses the yield), not #161.

**Checked with today's `bcc`.**

- A stored generator made in a function and returned, then consumed by `for` elsewhere, is
  accepted and runs (`gen-cell`'s `counter` wrapped in `make`: `i32[10]`, `live 0`).
- The same stored generator, made inside a borrow block and returned out of it, is rejected:
  *"`boxed['x]`: `g`, of type `U (pull i32 1 1)`, is used inside, and it cannot be shown to
  outlive `'x`"*.

So if "the scope that created it" is a **borrow block**, P3 **DOES NOT TYPE**, package or not.
The failing side condition is `[]I`'s `CtxOutlives` at a `U` slot, which is
`corpus/reject/gen-escape.bc`'s failure. That is not a B question. It needs either a stored
generator built as a `ν` state machine with a boxed rest, as `Aff` is (as P4's tasks are), or an
outlives rule for some `U` values.

### P4. Two interleaved tasks under a `Mut 'q` task queue

`async` is not built (#52). Tasks are written as the `ν` state machines §14 would make of an
`async fn`: one observation per stretch between `await`s, the state holding the package.

**Tasks cannot be stored continuations.** A `κ` from `handle` is a `U` slot, and nothing makes it
`[@d]`. With no outlives rule for `U`, no handler-captured task can enter a queue whose type must
outlive `'q`, package or not. The queue holds boxed codata, as `Aff` does:

    Task^d ≜ νX. F(i32 ⊕ (i32 ⊗ [@d] U X)) & F 1     -- step: done with a value, or a value and the rest
    E^d    ≜ [@d] U(Task^d)                            -- one queue element
    L^d    ≜ μX. 1 ⊕ (E^d ⊗ Ref X)                     -- the queue

**Task 1 owns its array** and keeps a leaf view across its `await`:

    P_own ≜ ∃'x ⊏ ⊤. ⟨imm[] i32⟩ (Imm 'x i32 ⊕ 1)

- step 1: open, read the view (10), close, `await`;
- step 2: `pkg_end`, read the view, finish with `+100` (110), free the array.

**Task 2 captures an outside borrow** `k : Imm 'r i32` of `cfg = 42` and owns a counter cell:

    P_cap ≜ ∃'x ⊏ 'r. ⟨mut i32⟩ (Mut 'x i32 ⊗ Imm 'r i32)

- step 1: open, add `*k` to its cell through `Mut 'x`, close, `await` (value 0);
- step 2: `pkg_end`, read its cell (42), free it.

*Hypothetical surface:*

    main -> i32 =
      let cfg = alloc(42);
      borrow imm cfg { 'r, k ->
        let u = alloc(());
        borrow mut u { 'd, _ ->                          -- a lifetime for the queue's box, as aff-capture's 'w
          let q = alloc(nil[E^d]);
          push(q, mk_own['d]());  push(q, mk_cap['r]['d](k));
          let n = borrow mut q { 'q, mq -> count_fold(round, (0, 2, (mq, 0))) };  -- 2 rounds
          drop_queue(q); n } }                           -- 10 + 0 + 110 + 42 = 162

*Change to the program, flagged.* The scheduler runs a fixed number of rounds (`count_fold`)
instead of "until the queue is empty". Run-until-empty is a div loop in a borrow block, which
`LoopLend` handles by re-lending the queue owner at each observation. That route was not derived
here.

*Derivation.*

1. **The contexts.**
   - `withbor1` on `cfg`: `'r ⊏ ⊤`.
   - `withbor2` on `u`: `'d ⊏ ⊓Δ = 'r`.
   - So `Δ₂ = ('d ⊏ 'r), ('r ⊏ ⊤)`.
2. **`mk_own<'d>`**, `Δ = ('d ⊏ ⊤)`.
   - `pkg_new_imm[]` at `⊤`, as in P1.1 ✓.
   - The state is a two-state sum `P_own ⊕ P_own`. The step is `unfold`'s, at `C[S/X]`.
   - Step 1 ends in `return inr (n, boxed['d] (inr p))`. `[]I`: `P_own ⊐ 'd` by the new case,
     `S = ∅` ✓.
   - The task thunk is boxed at `'d` over `{f : !…, s₀}` as in `aff_new_boxed` ✓.
   - Inside `pkg_use`, `'x′ ⊏ ⊤` is incomparable to `'d`. Nothing compares them ✓.
3. **`mk_cap`**, with the binders `all 'r < top. all 'd < 'r.` (§23, lifetime bounds), so
   `Δ = ('d ⊏ 'r), ('r ⊏ ⊤)`.
   - `pkg_new_mut` at `@b = 'r`: `Δ ⊨ 'r` ✓, `S = {'r}`, `i32 ⊒ {'r}` ✓, and
     `FV(T) = {'x, 'r}` ✓.
   - `[closeI]` on `(m, k)`, context `{m : Mut 'x i32, k : Imm 'r i32}`: `Pₓ('x)` ✓, and
     `Pₓ('r)` by `'r ⊑ 'r` ✓.
   - Step 1's `pkg_use`.
     - `copy['r] k`.
     - `withload['r, 'w] k₂`, with `'w ⊏ 'x ⊓ 'r ⊓ 'd`, a bound ✓.
     - `withswap['x]` adds the value read ✓.
     - `[closeI]` on `(m, k₁)` ✓.
   - `boxed['d] (inr p)`: `P_cap ⊐ 'd` by the new case, `Δ ⊨ 'd ⊏ 'r` ✓, and the payload `i32`
     ✓.
4. **`main`'s instantiation** `mk_cap['r]['d] k`: `allE`'s premises are `Δ₂ ⊨ 'r ⊏ ⊤` ✓ and
   `Δ₂ ⊨ 'd ⊏ 'r` (from `'d`'s bound) ✓.
5. **The queue under `Mut 'q`.**
   - `withbor2['q, L^d, i32] q`. Its side condition is `∃b. Δ₂ ⊨ @b ∧ Δ₂ ⊢ L^d ⊒ @b`. Take
     `b = 'd`: `μ`, `⊕`, `⊗` and `Ref X` pass through, and `E^d`'s box needs `'d ⊑ 'd` ✓.
   - `'q ⊏ 'd ⊓ 'r`.
6. **One round.**
   - `withswap['q] mq` takes the list and pops a task. `unbox`, then observation 1 runs the
     task's step, which opens and closes its own package inside. The rest is pushed back.
   - Each task's lend is ended before its step returns. Two lends never overlap.
   - The sequence is task 1 at `'x₁ ⊏ ⊤`, task 2 at `'x₂ ⊏ 'r`, task 1 at a fresh `'x₁′`, task 2
     at `'x₂′`.
   - [Tier 2 problems](tier2-problems.md) describes `'x₁` ending while `'x₂` is live. Under close
     and re-make that does not happen: nothing is live across an `await`.
7. **After.** The block's result `['q] i32` ✓. `drop_queue` closes any remaining task, by §22's
   destructor class 2, and frees the cells. `'d`'s block ends after `q` is freed.

**Variant to be rejected.** A task capturing a borrow made inside `'q`'s scope:

    borrow mut q { 'q, mq -> let z = alloc(7);
      borrow imm z { 'r2, k2 -> push(mq, mk_cap['r2]['d](k2)) } }

Here `'r2 ⊏ 'q ⊓ 'd ⊓ 'r`, beneath `'d`.

- `mk_cap['r2]['d]`: `allE` asks for `Δ ⊨ 'd ⊏ 'r2`. `'d`'s only parent is `'r`, and `'r2` is
  beneath `'d`, so `ordB` finds no derivation. **Rejected at `allE`.**
- `mk_cap['r2]['e]` at some `'e ⊏ 'r2` makes an `E^e`, which is not `E^d`. **Rejected:** the type
  of `withswap`'s callback does not match.
- Building the package by hand to get round it fails each way:
  - `S = ∅`: `[closeI]` at `k2 : Imm 'r2 i32` needs `Pₓ('r2)`, and there is no parent. **Rejected
    at `[closeI]`.**
  - `S = {'d}`: `Δ ⊨ 'd ⊑ 'r2` fails. **Rejected at `[closeI]`.**
  - `S = {'r2}`: `boxed['d]` needs `P_cap['r2] ⊐ 'd`, that is `Δ ⊨ 'd ⊏ 'r2`, which fails.
    **Rejected at `[]I`** (new outlives case).

It is rejected, by the rule that should reject it.

*The brief's form, directly.* A homogeneous queue of packages, `Ref (List (P_cap ⊗ …))` with no
closure, lent `mut` at `'q`:

- `withbor2`'s side condition `P_cap ⊒ @b` needs `@b ⊑ 'r`, and `'q ⊏ ⊓Δ` puts `'q` beneath it.
  That is `S ⊐ 'q`.
- A package made inside `'q`'s scope with `S = {'r2}` has a different type and cannot be pushed.

**Verdict: TYPES WITH ADDITIONS:** ADD-2/3, ADD-4 (`imm[]`). The rejected variant is
**REJECTED**, as required. **Needs besides B:**

- the `async` surface and its elaboration to `ν` state machines with boxed rests (#52);
- a scope only to name `'d`, as `aff-capture.bc` does;
- no A: there is no borrow live across an `await`;
- no E: the tasks hold no capability.

### P5. `corpus/reject/gen-self-borrow.bc` as written (A at `imm`)

Today it is rejected: *"this borrow block's body performs the operation 1.0, which resumes …
(T1, #172)"*. The `yield` sits inside `withbor1`'s callback, whose row must be `Row.Unwind`.

**The package is not what it needs, and neither is A's frame route.** The only value at a type
mentioning `'x` that is live across the `yield` is the lend `b` itself. ADD-5's degenerate case
ends the borrow before the `yield` and borrows again after it, with two ordinary `withbor1`s.
Between them the generator holds the owned `c` across the `yield` with drop glue, exactly as
`corpus/gen-cell.bc` does.

**Checked.** Today's `bcc` accepts the hand-segmented program and runs it to `i32[5]`, `live 0`:

    fn selfref() -> 1 with Yield[i32] =
      let c = alloc(5);
      let v = borrow imm c { 'x, b -> *b };
      yield(v);
      let u = borrow imm c { 'x, b -> () };
      let _ = free(c);
      ()

The same elaboration with a package (`P = ∃'x ⊏ ⊤. ⟨imm i32⟩ Imm 'x i32`) also types, as P3. The
package is the degenerate one, whose contents are the lend.

A's frame route, keeping the borrow live across the `yield` with T1 lifted for continuations that
stay inside the scope, would also type it. This program does not need that route.

**Verdict:** DOES NOT TYPE in today's elaboration (T1); **TYPES WITH ADD-5**, with no kernel
change and no package. **Needs besides B:** nothing.

### P6. The `mut` variant (A at `mut`)

    fn selfmut() -> 1 with Yield[i32] =
      let c = alloc(5);
      borrow mut c { 'x, m ->
        let v = modify m { i -> (i, i) };
        yield(v);                                -- m live across the yield
        let w = modify m { i -> (7, 7) };        -- write through the borrow after the yield
        yield(w);
        () };
      let _ = free(c);
      ()

As written, today's `bcc` rejects it at the block (T1, the same message as P5).

**Is close-at-the-stop plus a same-parents re-open the end-and-remake mechanism? Yes.**

- At each `yield`, the `mut` cell at `'x` is ended: `c` is back to `own`. The stop then holds no
  newly created `mut` cell, which is exactly what Core's `wp` requires.
- After the `yield`, a fresh lend is made. This is GhostEnd's `Relend` in typed form.
- In this program the contents are the lend itself, so it is ADD-5's degenerate case: one
  `withbor2` per segment. Whether the fresh lifetime gets the old parents or sits beneath the
  resumer does not matter here, because nothing typed at the old `'x` is carried over.

**Checked.** Today's `bcc` accepts the hand-segmented program and runs it to `i32[12]`,
`live 0`. It is the program above with the block cut at each `yield` into `borrow mut c { 'x, m ->
let r = modify m { … }; r }`.

**P6′, non-degenerate.** The generator owns an array, takes `slice_get_mut`'s leaf
`Mut 'x i32` before the `yield`, and writes through that leaf after it. The leaf is derived, so
ADD-5 makes it a package:

    P ≜ ∃'x ⊏ ⊤. ⟨mut[] i32⟩ (Mut 'x i32 ⊕ 1)

- `[closeI]` on the leaf ✓ (`Pₓ('x)`).
- The package is held across the `yield` with drop glue (ADD-3).
- The second segment's `pkg_use` re-types the leaf at `'x′`.

**Verdict:** P6 **TYPES WITH ADD-5** (no package). P6′ **TYPES WITH ADDITIONS:** ADD-2/3, ADD-4
(`mut[]`), ADD-5.

So **one construct covers A at `mut` and B**, for borrows of places the suspending computation
owns. It does not cover:

- a borrow whose place belongs to someone else, with derived state crossing the stop. That needs
  a reborrow lend kind (source `Mut @a A`, mirroring `withbor3`), a further ADD-4 kind that is
  not worked out;
- A's programs in which *other* computations hold copies of the borrow across the stop. In
  `corpus/pending/async-borrow.bc` two tasks hold `b1`, `b2` across the `await` while `main`'s
  block is open. Closing would need the tasks, which are `U` values not formed in the `[closeI]`
  context, to be closable. They are not, as in P2b, so that program needs A's frame route.

### P7. A lending iterator (problem C)

A generator owning `buf` yields `&self.buf[i]`, an `Imm 'x i32` derived from its lend.

**Verdict: DOES NOT TYPE.** Every placement of the `yield` fails a named side condition:

- **Inside `pkg_use`'s callback.** The callback may perform only abortive operations
  (`Row.Unwind 'x` at the unwinding form, the pure row otherwise). `yield` resumes: T1 at the
  package.
- **After the close.** The view must leave the callback in `['x] B`. Its type mentions `'x`, so
  `'x ∉ FV(B)` fails. If it is hidden in a closure, `[]I`'s `CtxOutlives` at `Imm 'x i32 ⊐ 'x`
  fails.
- **In the signature.** Independently, *operation types are closed in lifetimes* (§19), so
  `Yield[Imm 'x i32]` cannot name the open's lifetime.

**What C needs beyond B:**

1. A at the package's scope: a resuming operation inside `pkg_use`'s callback, whose continuation
   is resumed before the callback returns.
2. Operation signatures that take a lifetime: `yield : ∀'y. Imm 'y A ↠ 1`, with a clause
   polymorphic in `'y` that cannot keep the payload past resuming (a `['y]`-boxed clause result).
3. The reborrow rule at a package: the consumer's view ends before the generator resumes.

### P8. Programs that would be unsound if accepted

| attempt | what goes wrong | rejected by |
|---|---|---|
| open one package twice, getting `mut` lends at `'x′` and `'x″` of one cell | aliasing `mut` | linearity: `pkg_use` consumes the package, and `Ctx.SplitP` gives the slot to one use. There is no `copy` axiom at a package, and `!` needs a persistent context, which a package is not |
| open a package through `Imm 'a` by two readers | the same, through sharing | ADD-7: `Imm̲` of a package is `Unk`, and no package constant takes a borrowed package. Through `Mut 'a`, `withswap` takes it out exclusively, which is sound |
| open the same package again inside its own open | nested lends of one cell | impossible: inside the callback there is no package value, only its contents |
| close while a borrow at `'x` escapes in the returned value, e.g. `copy` the `imm` lend, close one copy, return the other | dangling view | `pkg_use`'s `'x ∉ FV(B)`, and `[]I` at `['x] B`: `Imm 'x A ⊐ 'x` needs `'x ⊏ 'x` |
| the same, hidden in a returned closure `U(…)` over `m : Mut 'x A` | dangling `mut` | `[]I`'s `CtxOutlives`: the closure's context has `Mut 'x A`, and `'x ⊏ 'x` fails |
| close while a reborrow at `'y ⊏ 'x` is in the contents | a cell beneath `'x` survives the close | `[closeI]`: `Pₓ('y)` fails, since `'y` is not `'x` and lies above no parent. Lexically, `'y`'s callback has returned anyway |
| close with an opener's borrow `Imm 'r′ A`, `'r′` incomparable to `'x`, in the contents or captured by a closure in them | ADD-1's counterexample | `[closeI]`: `Pₓ('r′)` fails |
| re-open beneath the opener (extra parents) | the positional re-make, refuted (`kU_convention`) | not expressible: the callback's binder is the package's `@b` |
| store a package with `S = {'r}` under `Mut 'q` for `'q` not beneath `'r`, or return it past `'r` | captured borrow outlived | the new outlives case (`Δ ⊨ @q ⊏ 'r`), or `'r ∉ FV(B)` at `'r`'s own block |
| build a package that captures a borrow but claims `S = ∅` | an owned-looking package holding a borrow | `[closeI]` with `S = ∅` admits only `'x` and lifetime-free slots |

Each rejection is by a rule of §1. None is machine-checked: the rules are not implemented.

## 3. Checker entailment on a partial order

**`ordB`** (`Frontend/Check/Decide.lean`) decides `Δ ⊨ @a ⊏ @b` (`ltB`) and `⊑` (`leB`). On a
partial order, two of its strict rules fail (`PartialLife`'s `checker_meet_not_partial`,
`checker_join_not_partial`):

- `@a ⊏ @b₁ ⊓ @b₂` from both;
- `@a₁ ⊔ @a₂ ⊏ @b` from both.

**Method.** A local diagnostic build of `bcc`, reverted afterwards and not committed.

- `ordBX` is `ordB` with either rule switched off.
- `ltB` traces every call whose result changes when either rule is off.
- `ltB` and `leB` also trace every call with its arguments and `Δ`.
- `bcc check` was run over all 248 files of `corpus/*.bc`, `corpus/surface/`, `corpus/axes/`,
  `corpus/reject/` and `corpus/pending/`. A script then parsed the traces.
- For every *successful* entailment whose sides contain a meet or join, it tested whether the
  components are comparable under `Δ`'s parent edges, read as in §1.1.
- `make gate` was **not** run.

**Results.**

| | count |
|---|---|
| files run | 248 |
| files that reach at least one entailment (pending and reject files stop at their error) | 119 |
| `ltB` calls / successful | 37,467 / 34,151 |
| `leB` calls / successful | 159 / 108 |
| successful `ltB` that **need** the strict right-`⊓` rule | **0** |
| successful `ltB` that **need** the strict left-`⊔` rule | **0** |
| joins in any successful entailment | 0 |
| successful calls with a meet among their arguments | 122 trace lines: 32 `⊏` with a meet on the left, 39 `⊑` with a meet on the left, 51 `⊑` with a meet on the right, some lines counted twice |
| … of which a meet of components `Δ` does not make comparable | **0** |

**Where the meets are.**

- **Files:** seven, `aff-capture`, `aff-coerce`, `aff-counter`, `aff-depth`, `aff-drop`,
  `aff-higher` and `borrow-in-scope`.
- **What they are:** the elaborated `dom` (`'w /\ 'x /\ 'main /\ top`) and the meets §15's
  lifetime filling makes. Each is a chain under `Δ`, each new lifetime beneath the ones before it.
  On a partial order it denotes its shortest member.
- **Sibling lifetimes:** function parameters `'a, 'b < top` are incomparable in the partial
  reading. No successful entailment relates two of them, since `ordB` has no rule that could.

**Answer: no corpus program relies on the two chain-only rules, or on any two lifetimes being
comparable beyond what `Δ`'s parent edges give.** Dropping both rules where the meet or join is a
value changes no verdict on the corpus.

**Not covered by the census:**

- `Defines` checks of meet values (`Life.wf`), which were not instrumented;
- the 41 kernel programs (`bcc kernel list`), which are typed by Lean derivations, not by `ordB`.
  By grep, their borrow constants are at `Δ = ∅`. Not instrumented;
- pending and reject programs past their first error;
- programs inside a package open, which do not exist. There the opener's lifetimes and `'x′` are
  incomparable, and `dom` as a value is undefined (ADD-6).

## 4. Summary

| program | verdict | additions | other dependencies |
|---|---|---|---|
| P1 struct: buffer and view | TYPES WITH ADDITIONS | ADD-2 or ADD-3, ADD-4 (`imm[]`) | none |
| P2 closure: cell and its borrow, called twice (affine, `Aff` over a package) | TYPES WITH ADDITIONS | ADD-2 | none. Degenerate: types today without the package (`corpus/aff-counter.bc`) |
| P2b the closure as the contents | DOES NOT TYPE | — | `[closeI]` at an observed `U` rest. Needs a closable-rest modality (not adopted) |
| P3 stored generator with a self-borrow across `yield`, returned from a function, resumed by `for` | TYPES WITH ADDITIONS | ADD-2/3, ADD-4 (`imm[]`), ADD-5 | no A, no E, no #161. Out of a borrow block: DOES NOT TYPE (`U` has no outlives rule; checked), independent of B |
| P4 two tasks, queue under `Mut 'q`, one task capturing `imm 'r` | TYPES WITH ADDITIONS | ADD-2/3, ADD-4 (`imm[]`) | `async` (#52) elaborated to `ν` state machines with boxed rests; a scope naming `'d`; fixed rounds (changed, flagged) |
| P4 rejected variant (captured `'r2` beneath `'q`) | REJECTED, as required | — | `allE` (`'d ⊏ 'r2`), or `[closeI]`, or `[]I` |
| P5 `gen-self-borrow` (A, `imm`) | DOES NOT TYPE today (T1); TYPES WITH ADD-5, no package | ADD-5 | none. Hand-segmented form checked: `i32[5]`, `live 0` |
| P6 its `mut` variant (A, `mut`) | DOES NOT TYPE today (T1, checked); TYPES WITH ADD-5, no package | ADD-5 | none. Hand-segmented form checked: `i32[12]`, `live 0` |
| P6′ `mut` leaf derived from the lend, across `yield` | TYPES WITH ADDITIONS | ADD-2/3, ADD-4 (`mut[]`), ADD-5 | none |
| P7 lending iterator (C) | DOES NOT TYPE | — | A at the package's scope; lifetime-taking operation signatures; reborrow at a package |
| P8 the ten unsound attempts | each REJECTED | ADD-1, ADD-7 needed for two of them | — |

**Does the package construct express the B programs?** Yes, with additions, for P1, P2, P3 and
P4. Two of the additions change what was briefed:

- **ADD-1:** close must check the contents' context against the parent set, not only that the
  borrows at `'x` have ended. Without it the storage rule `S ⊐ 'q` admits a dangling closure.
- **ADD-2:** an elimination that gives the place back.

The others are a schema of lend kinds beyond the one modelled `mut` cell (ADD-4), a destructor
(ADD-3), `Imm̲` to `Unk` (ADD-7), and two elaboration points (ADD-5, ADD-6).

Two things it does not express:

- a package whose contents are a closure *observed* from the contents (P2b). Closing works only
  where the closure is formed;
- a stored continuation that must outlive a scope (P3 out of a borrow block, P4's tasks as
  continuations), because `U` has no outlives rule. That is not B's question. Storable
  suspensions have to be boxed `ν` state machines, as `Aff` is.

**Does it also cover A at `mut` (P6)?** Yes, for places the suspended computation owns:
close-at-the-stop plus re-open is the end-and-remake that Core's `wp` requires. But P5 and P6 as
written are its degenerate case, where the contents are just the lend. They need no package and
no kernel change, only ADD-5 segmenting, which is `LoopLend`'s re-lend moved to a resuming
operation. Today's checker accepts both hand-segmented programs. The package is needed when
derived state crosses the stop (P6′). A's frame route is still needed for borrows held by
*other* computations across a stop (`async-borrow`).

**What it would unblock today:**

- **`corpus/pending/`:** nothing.
  - `async-borrow` needs #52 and A.
  - `gen-lazy`, `gen-digits`, `gen-adapters-io` and `gen-lines` need E.
  - `yield-callback`, `effects-hof-two-rows`, `effects-sum-gen` and `effects-tunnel` need #161.
  - `print-borrowed-list` needs a list iterator. A lending one is C.
  - The rest are unrelated.
- **`corpus/reject/`:**
  - `gen-self-borrow.bc` would be accepted with ADD-5 alone, no package.
  - `lend-escape.bc` would be accepted by a package-aware `LoopLend`. Its loop keeps `b2`, which
    is the lend.
  - `lend-iter-borrow.bc` stays rejected (P2b's reason).
  - `gen-escape.bc` stays rejected, correctly: the borrow is of outside data.

**Not determined:**

- the soundness of any new rule. Nothing is proved. The `imm`, `imm[]` and `mut[]` lend kinds are
  not modelled (Nominal's `Pkg` is one `mut` cell), and ADD-1's sufficiency is argued, not
  proved;
- positivity (`NuOk`) of `Task^d = νX. F(i32 ⊕ (i32 ⊗ [@d] U X)) & F 1`, believed by analogy
  with `Aff`;
- whether ADD-5 can segment at every resuming operation (inside loops, nested matches, calls).
  Only straight-line code and one `match` are sketched;
- whether real programs need `dom` as a value inside an open (ADD-6);
- a run-until-empty scheduler through `LoopLend`;
- A at `mut` for places the suspension does not own, with derived state (a reborrow lend kind);
- the reader-object and cancellation test programs of A, beyond the observation that cancelling a
  continuation holding a closed package runs only the package's destructor;
- the census's coverage of `Defines`, the kernel programs, and code past a file's first error.
