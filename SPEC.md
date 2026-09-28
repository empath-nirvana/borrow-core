# Borrow core — specification

Version 0.10 · 2026-09-27

The library — `Paper/`, `Support/`, `Examples/`, `Core/` — implements this document and nothing else. A
change to the language is a new entry here, written before any code; the library then
implements it, and code an entry adds or changes is tagged `[spec §N]`. Experiments live
in `experiments/`, which the library never imports; work from one lands in the library only
after its entry is written.

Notation follows Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(PACMPL 9:OOPSLA2:415, 2025): `[CONF]` is the paper, `[TR]` its supplement.

---

## 1. Baseline

The calculus is BoCa with the logic BoLo, as mechanized in *bolo-formalization*
(github.com/empath-nirvana/bolo-formalization, commit `1658da9`). This repository starts from
that commit's `Paper/`, `Support/` and `docs/`: `Paper/INDEX.md` indexes the paper's results and
definitions, and `docs/adjudications.md` records every departure from the printed text. That
fixes:

- **Syntax** — `[TR]` §1: values, expressions, types `1`, `⊕`, `⊗`, `⊸`, `Ref`, `Imm @a`,
  `Mut @a`, `[@a]`, `∀'a ⊏ @b`, `Unk`. `Prim` also has the integer literals `lit` and the host
  operations `host` of §8.
- **Typing** — `[TR]` p. 2's rules and p. 3's axiom table, read under p. 2's presuppositions
  (`DerivesWf`).
- **Machine** — `[TR]` §3 with the frames `K; e` and `injᵢ K` (`BoLo.Steps`), plus one host
  step `(μ, host op v) ↦ (μ, r)` when `Host.call op v = some r` (§8). The machine is parameterized
  by a host `ℍ` (`{ℍ : Host} [HostIs ℍ]`) and is deterministic for each host.
- **Semantics** — the typed world: `[TR]` §§4–6 with the definition changes recorded in
  bolo-formalization's `docs/adjudications.md` §12.66–§12.73 (`vX`, `wpTS`, `SemX`).

Baseline theorems, which every later entry must preserve (each holds for every host `ℍ`):

- **Fundamental Property** — `DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T`.
- **Adequacy** — `DerivesWf ∅ [] e 1 → Steps ∅ e ∅ ()`: a closed program typed at `1` has a
  run to `()` that leaves memory empty.

---

## 2. Entry 1 — the exponential, `!T`

### Motivation

`Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` and `Imm̲ 'b (∀'a ⊏ @b. T) ≜ Unk` (`[CONF]` Fig. 8 clauses (4), (8)):
an immutably borrowed function can only be forgotten, because it may capture linear
resources. With closure conversion a closure is a pair of its environment and code. The
environment is data, which `Imm̲` already views correctly; what is missing is a way to say the
code captures nothing, so that a borrow can keep it whole.

The paper names the construct: *"Linear type systems are often presented with an exponential
modality, `!T` … Exponentials are therefore an orthogonal extension that we will not develop
in this paper, though they are completely compatible with our type system"* (`[CONF]` 415:4).
BoLo has the matching connective, `!P ≜ emp ∧ P` (`[TR]` p. 6; definition row 5.38).

### Types

    T ::= … | !T

Scoping, well-formedness, lifetime substitution and `TyEq` treat `!T` as a unary former over
`T`.

### Metafunction and outlives

    Imm̲ 'b (!T) ≜ !T
    ─────────────
    Δ ⊢ !T ⊐ @a            (at every @a)

### Typing

`!Γ` means every live slot of `Γ` has a `!`-type (`Ctx.Persistent`).

    !Γ    Δ ⊢ T₁    Δ; x : T₁, Γ ⊢ e : T₂
    ─────────────────────────────────────  !I-λ
        Δ; Γ ⊢ λx.e : !(T₁ ⊸ T₂)

    !Γ    'a ∉ dom(Δ)    Δ ⊧ @b    Δ, 'a ⊏ @b; Γ ⊢ e : T
    ────────────────────────────────────────────────────  !I-Λ
             Δ; Γ ⊢ Λ.e : !(∀'a ⊏ @b. T)

    Δ; Γ ⊢ e : !T
    ─────────────  !E
    Δ; Γ ⊢ e : T

Axioms, at a dead context:

    copy   : !T ⊸ !T ⊗ !T
    forget : !T ⊸ 1

Promotion is for `λ` and `Λ` only: an arbitrary term can allocate (`alloc ()` in an empty
context must not have type `!(Ref 1)`). No new terms and no new machine rules.

### Semantics

- Literal relation: `𝒱⟦!T⟧δ(v) ≜ !𝒱⟦T⟧δ(v)`, that is `𝒱⟦T⟧δ(v)` at resource `∅`.
- Typed world: `vX b (!T) ls δ v ρ ≜ ρ = ∅ ∧ vX true T ls δ v ρ`, in **both** modes: the
  observable view does not relax `!T` (it relaxes `⊸` and `∀`, §12.69).
- Shape: `vShape (!T) ≜ emp`. `tyLife (!T) ≜ free`.

### Retired

The literal-relation Fundamental Property (`[TR]` 6.151 at `Sem` under `WithloadEscrow`, and
`ViewWitness.fundamentalProperty_refused`) is not carried: it quantifies over `DerivesWf`, which
now includes the `!` rules. `Sem` at a `withload` node (`ViewWitness.withloadSem_refused`) and
the other literal readings in `Paper/LiteralReadings/` are kept.

### Obligations

1. The Fundamental Property and adequacy of §1 over the extended judgment —
   `Fig16.LogRel.Typed.fundamentalProperty`, `adequacy`; the new cases are `bangLamI_compatX`,
   `bangAllI_compatX`, `bangE_compatX`, `copyBang_compatX`, `forgetBang_compatX`
   (`Support/TypedWorld/Compatibility.lean`), over `gSepX_persistent` (`!Γ` holds `∅`).
2. `[TR]` 6.60 at `!T` (`vDen_outlives`, `vX_outlives`): the resource is `∅`.
3. `[TR]` 6.131 at `!T`: `[α] 𝒱⟦!T⟧ ⊨ ↺α 𝒱⟦!T⟧` — `reborrow_vDen`'s `!` case, by
   `reborrow_self_of_imm` (`Support/Model/Unr.lean`).
4. Programs (`Examples/`), each with its adequacy instance and an interpreter run:
   - `callBorrowed` — `λx.x : !(1 ⊸ 1)` loaded through an `Imm` borrow and called;
   - `captures` — a closure over an `Imm` borrow, loaded through a second borrow, called twice;
   - `fnMut` — state-passing `!` code run twice on a `Mut` borrow of its environment;
   - `ownedFn` — a closure owning its environment, with code `!(∀'c ⊏ ⊤. (Imm 'c 1 ⊗ 1) ⊸ 1)`,
     loaded through an `Imm` borrow and called twice;
   - `mutClosure` — a whole closure `(env, !code)` borrowed mutably and run twice.

### Closures, in these terms

| Rust | here |
|---|---|
| `fn` item | `!(T₁ ⊸ T₂)` |
| `FnOnce` | `T₁ ⊸ T₂`, or `(env, code)` consumed |
| `FnMut` | `(env, !code)` behind a `Mut` borrow, `code : !(E ⊗ T₁ ⊸ E ⊗ T₂)`, run by `withswap` |
| `Fn` | `(env, !code)` behind an `Imm` borrow, `code : !(∀'c. Imm̲ 'c E ⊗ T₁ ⊸ T₂)` |

### Why `!`, and not a closure former

The typed world chooses each reborrow's image from types (§12.69, §12.71). A closure's image
must be its captured resource, and neither its type nor its value determines that. Packing the
environment existentially does not link the image to the escrow, and neither does naming the
environment's type while its value is free (both refuted in the experiment
`experiments/BorrowedClosures/EnvCheck.lean`). `!T` has image `∅`, which is determined.

### Open

- **Promotion at every value.** Needs `wp` at a value to leave the resource in place; not proved.
- **Conservative extension.** Every baseline derivation is a derivation here and means the
  same thing. `DerivesWf` only gains constructors and `vX` is unchanged at `!`-free types, but no
  theorem states it: stating it needs the baseline and this library in one environment.

---

## 3. Entry 2 — the call-by-push-value core

### Motivation

BoLo is call-by-value: effects, thunks and data share one type language. Splitting value types
from computation types makes the shifts explicit, which is where closures are allocated and
data is materialized, and gives codata (`&`, and the formers of §7) a home.

### Types

    A ::= 1 | A ⊗ A | 0 | A ⊕ A | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk
        | X | μX. A                                                   (value types)
    C ::= F A | A ⊸ C | C & C | ⊤ | ∀'a ⊏ @b. C | νX. C               (computation types)

`X`, `μ` are §6; `ν` (and the delay, stream and iterator types over it) is §7.

### Typing

`CDerives Δ Γ e j`, with `j` either `val A` or `comp C`, over BoLo expressions in A-normal form:
the CBPV formers (`thunk`, `force`, `return`, `to`, `λ`, application, `⟨·,·⟩`, projections),
the lifetime `∀` (elimination at every `C`), the `!` rules of §2, `[]I` at every value type,
`⊑Imm`/`⊑Mut`, one constant per borrow axiom of `[TR]` p. 3 at arbitrary value-type payloads,
and three call-by-value derived forms (`lolliE`, `allEV`, `ofRet`). No new machine rules.

### Semantics

The typed world of §1, re-typed at `VTy`/`CTy`: `vC`, `cC`, `SemV`, `SemC`. `U C` is a leaf of the
record machinery (`Imm̲ (U C) = Unk`).

### Baseline, restated

- **Fundamental Property** — `CDerives Δ Γ e j → SemV`/`SemC` (`fundamentalC`).
- **Adequacy** — a closed computation at `F 1` runs to `()` and leaves memory empty (`adequacyC`).
- **Embedding** — `embed : DerivesWf Δ Γ e T → CDerives Δ (cbvCtx Γ) e (val (cbv T))` for every
  `DerivesWf` rule, so every baseline program is a program here and inherits adequacy
  (`adequacy_of_derivesWf`). "Preserving the baseline" means this embedding; the baseline
  theorem at `SemX` is not restated at `vC`.

---

## 4. Entry 3 — frame lifetimes are non-strict

`FrameLife`'s second conjunct becomes `x ⊑ α` (was `x ⊏ α`), and the reborrow step's premise
`W.InStratum β` becomes `StratumLe W β` (every lifetime of the world is at least `β`). The
typed world then admits views that last exactly as long as their frame. No current rule uses
this; it is kept for later same-lifetime views. From `experiments/Relaxed`.

---

## 5. Entry 4 — blocks, places and records

### Records and variants

A record is a binary tree of `⊗` (no trailing `1`); a variant is a nest of `⊕`. Both are derived
forms: construction, destructuring, projection, injection and case are derived rules, and `Imm̲`
acts fieldwise. Projecting one field of a borrowed record drops the other fields' views, which
must be `Affine`; `Affine` has no `μ` case, so projection past an unboxed `μ`-typed field is not
available (destructuring is).

### Blocks

`Shape ::= leaf A | node Shape Shape`. A block of shape `σ` is `size σ` cells, allocated at once.
Its handle has type `refTy σ`, defined as the family of its leaf references, so
`refTy (node σ₁ σ₂) = refTy σ₁ ⊗ refTy σ₂`: splitting a handle is the identity. An owned pointer to a
struct (`Box<struct>`) is the block form; the one-cell `Ref (A ⊗ B)` remains a separate type.
Blocks are allocated and freed whole (`allocS`, `freeS`).

### Family borrows

Several disjoint places are borrowed at one lifetime by nesting `withbor` and shortening with
`⊑Mut`/`⊑Imm`: `withborF2 : Ref A ⊗ Ref B ⊸ (∀'c. Mut 'c A ⊗ Mut 'c B ⊸ ['c] T) ⊸ …`, its `Imm`
form, and the block form `withborS`. A sub-family is passed on at the same lifetime. All are
derived rules. Restrictions:

- `withborF2`: the second leaf `B` and the result `T` outlive the outer lifetime (`VOutlives`).
- `withborS`: leaves and result are lifetime-free — built from `1`, `0`, `⊗`, `⊕`, `Ref`, `!`,
  `X`, `μ` (not `Imm @e`, `Mut @e`, `[@e]`; not derived, not known to be blocked).

### Open

- **Block provenance.** (The MVP backend keeps a block handle as a tree of separate cells, not one
  word, so this is not yet exercised.) Leaves of two different blocks must not be joined into one handle, and a
  reuse hole (§6) must refill its own node. Neither is enforced by typing; the model is sound
  either way, but lowering a handle to one word needs it. To be settled with the syntax.
- **Variants in place.** A variant's layout depends on its tag; `Ref` does not distribute over
  `⊕`.
- **Same-lifetime views through a pointer** are excluded by the update relation
  (`experiments/FrameEnd`, `imm_view_rejected`, `mut_view_rejected`).

From `experiments/Records`, `Places`, `LeafPlaces`.

---

## 6. Entry 5 — recursive types and folds

### Types

`μX. A`, iso-recursive, with de Bruijn type variables. Positivity (`NoMut`): `X` does not occur
under `Mut`. `U C` is a leaf for type variables.

### Typing

`roll`/`unroll` on the same term (no machine step). `Imm̲` at `μ` substitutes the closed `μ` type
for `X` under `Ref`, `Imm`, `Mut`, `!` and keeps `X` at head positions.

### Folds

For `T` in the class `FShape` (closed leaf, `Ref X`, `X`, `⊗`, `⊕`; not `X` alone):

    foldImm   : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX.T) ⊸ F R)     R outlives every lifetime
    foldOwn   : !U(A′_R ⊸ F R) ⊸ !U(μX.T ⊸ F R)
    foldReuse : !U(A″_R ⊸ F R) ⊸ !U(μX.T ⊸ F R)

`A_R` is the unrolled borrowed view with `R` at recursive positions; `A′_R` the unrolled owned
value; `A″_R` gives `Ref 1 ⊗ R` at each `Ref X` (the emptied cell and the result), so the result can
be built in place. `foldImm` terminates by the size of each view's witness, which is strictly
smaller than its parent's; `foldOwn`/`foldReuse` by the size of the owned resource.

### Semantics

`vC` takes a type-variable environment; `μ` is an impredicative least fixed point.

From `experiments/Recursion`, `CBPVMu`.

---

## 7. Entry 6 — codata: `νX. C`

One computation-type former for codata. Delay, streams and finite iterators are abbreviations
over it; a new codata shape is a new abbreviation, and a library of iterator adapters (`map`,
`take`, …) is ordinary code over `Iter`, never a former or a rule.

### The former

    C ::= … | νX. C          (computation types)

`X` is a computation-type variable bound in `C`; it occurs only as the value type `U X`, "the
rest of the codata". Every observation of a `νX. C` returns, possibly among other values, a
thunk of the rest.

**Positivity** (`CTy.NuOk`). `C` is a `&` of two observation trees, and an observation tree is
an `F A` or a `&` of two observation trees. In each result `A`, `U X` occurs only under `⊗` and
`⊕`: `A` is `U X`, `B ⊗ B'` or `B ⊕ B'` of such types, or a type in which `X` does not occur
(`VTy.Poly`). So `X` is never under a `⊸`, a `Ref`, a borrow, a box, a `!`, a `μ` or another
`U`, and a `νX. C` always has at least two observations.

**Relation.** At a positive `C`, `𝒞⟦νX. C⟧` is the greatest fixed point of one unfolding of the
observation tree, with a candidate `R` for `U X`: `⋃{R | R ⊆ Φ_C(R)}`, written in `Prop` as
`∃ R` (`docs/scope-recursion.md` §3.1). `Φ_C` is monotone because `X` is outside every `Mut`
payload. It needs no approximation of `νX. C` and no step index.

**In and out.** `C[U(νX. C)/X]` is the unrolling:

    Γ ⊢ M : C[U(νX. C)/X]            Γ ⊢ M : νX. C
    ──────────────────────  nuIn     ──────────────────────  nuOut
    Γ ⊢ M : νX. C                    Γ ⊢ M : C[U(νX. C)/X]

on the same term, at a positive `C`. Observing a `νX. C` is `nuOut` followed by the projections
of the unrolling.

**Coiteration.** At every positive `C` and every state type `S`:

    unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)

`C[S/X]` puts the state where `U X` was: the step answers each observation path with the
next state in place of the rest. `unfold step s` answers an observation path by running the same
path of `step s` and replacing each state `s′` in the result by `unfold step s′` (a map along the
`⊗`/`⊕` positions of `X`). The recursion is the rule's: the step returns states, never a
`νX. C`, so it cannot observe the codata it is building. Sound by coinduction with the candidate
`{unfold step s | s ∈ 𝒱⟦S⟧}`.

### Instances

    Loop A B     ≜ νX. F(A ⊕ U X) & F B               (loop)
    D A          ≜ Loop A 1                            (delay)
    Stream A     ≜ νX. F(A ⊗ U X) & F 1               (stream)
    Iter A R R'  ≜ νX. F((A ⊗ U X) ⊕ R) & F R'        (finite iterator)

The first observation is `next`, the second `close`. A delay's `next` returns a result or the
rest; a loop's does the same, and its `close` ends it early with a residual `B` (the delay is the
loop whose residual is `1`); a stream's returns an element and the rest. An iterator's `next` yields an element and the
rest, or finishes with `R`; its `close` ends it early and returns a residual `R'` (for example a
buffer or a cell handed back). `close` is required: no rule forgets a `U C`, so a linear state
is released only by running `close`.

The former rules of the instances are the general ones at their bodies:

    fixD    = unfold at D A      : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)
    unfoldS = unfold at Stream A : !U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)

`delayIn`/`delayOut` and `streamIn`/`streamOut` are `nuIn`/`nuOut` at those bodies. A loop is
`fixD` (or `unfold` at `Loop A B`): the step maps a state to a result or the next state, and never
observes the loop.

**The driver.** `driveE n` observes a loop at most `n` times and closes it if it has not
finished: `d : U(Loop A B) ⊢ driveE n : F(A ⊕ B)`, a `CDerives` derivation at every `n`
(`d_driveL`; at the delay, `d_drive`). So a closed program that returns a loop, followed by
`driveE n`, is a closed program for every `n`, and adequacy covers it.

### Destructor

`U(νX. C & F R)` with `R` closed and in `HasDtor` has a destructor (§12): force, `nuOut`, the
second projection (`close`), then the destructor of the residual `R`. Delay and stream have
`R = 1`; an iterator's residual is dropped by its own destructor.

### Adequacy

For every `n`, observing a `D A` at most `n` times and then closing it is a closed program; it
runs from empty memory and leaves memory empty. Every closed `F 1` program over `νX. C` is covered
by `adequacyC`.

### Baseline

`fundamentalC` covers `nuIn`, `nuOut` and `unfold`; `adequacyC` is unchanged. Nothing in §1–§6
changes. `νX. C` is one `CTy` former and three `CDerives` rules; the fixed formers `D`/`Stream`,
their relations and their six rules are deleted.

### Open

- **Other positions of `X`.** `X` under a `Ref`, a borrow or `!` in an observation result, or in
  the argument of an observation (`A ⊸ …`, a sink), is outside `NuOk`. The relation is monotone
  wherever `X` avoids `Mut` payloads; what is missing is coiteration's map at those positions.
- **Lifetime-indexed iteration.** An iterator over a borrowed list or buffer, whose state is a
  borrow and whose rest keeps it, is not yet written as a program (§9 iteration, `[@d] U(νX. C)`
  per `docs/scope-recursion.md` §3.5).
- **General recursion.** Non-tail recursion needs an explicit stack in the state, or a `bind`
  on `D` (not yet written).
- Whether `D`'s greatest fixed point equals the intersection of its finite approximations is
  reduced to one property of `wpTS` (`WpChainCommutes`), not derived.
- Stream adequacy is stated generically only at `Stream 1` (`take_runs`).

From `experiments/Recursion`, `CBPVMu`; general `ν` per `docs/scope-recursion.md` §3.

---

## 8. Entry 7 — integers

### Types

    A ::= … | I32 | I64                                   (VTy.int w)

`I32`/`I64` hold no resource. They are persistent (§10), `Imm̲ 'b I32 = I32`, and they outlive every
lifetime.

### Terms and machine

Integers are term constants. `Prim` gains `lit c`, with `c` an `i32`/`i64` literal (`UInt32`/`UInt64`),
and `host op`, a host operation. One machine step applies a host operation:
`(μ, host op v) ↦ (μ, r)` when `ℍ.call op v = some r` (`Support/Dynamics/Host.lean`). A host `ℍ` is a
structure of typed Lean functions grouped by operation family (`bin32`, `div32`, `rel32`, …, their
64-bit analogues, and the conversions), so every host is well-sorted by construction. An
ill-shaped argument is stuck. Results are encoded as follows: arithmetic gives a literal; tests give
`inj₂ ()` for true and `inj₁ ()` for false; partial operations give `inj₁ n`, or `inj₂ ()` where
Wasm traps.

### Operations

Wasm's integer instructions (`HostOp`, `Support/Syntax/Integers.lean`), at each width `w`:

| group | operations | type (at `I32`) |
|---|---|---|
| literals | `lit` | `I32` |
| binary | `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `shr_s`, `shr_u`, `rotl`, `rotr` | `I32 ⊗ I32 ⇒ I32` |
| partial | `div_s`, `div_u`, `rem_s`, `rem_u` | `I32 ⊗ I32 ⇒ I32 ⊕ 1` |
| unary | `clz`, `ctz`, `popcnt`, `extend8_s`, `extend16_s` | `I32 ⇒ I32` |
| tests | `eqz`; `eq`, `ne`, `lt_s`, `lt_u`, `le_s`, `le_u`, `gt_s`, `gt_u`, `ge_s`, `ge_u` | `I32 ⇒ 1 ⊕ 1`; `I32 ⊗ I32 ⇒ 1 ⊕ 1` |
| conversion | `wrap`, `extend_s`, `extend_u`, `extend32_s` | between widths |

`A ⇒ B` is the call-by-value function type `U(A ⊸ F B)`. Typing: `CDerives.lit` gives a literal
its width's type, and `CDerives.hostOp op` gives `host op` the type `!(hostArg op ⇒ hostRes op)`.
Partial operations return a sum where Wasm traps, because a trap would abandon linear resources.

### Semantics

The value relation at `int w` holds exactly at a literal of width `w` and the empty resource. Every
theorem holds for every host `ℍ`, so nothing about arithmetic is proved. The concrete host
`wasmHost` (on `BitVec`) is used only by the interpreter and by `decide`-checked evaluations.
Compiler correctness will be stated with the target's own operations as the host. Agreement
between engines is tested on the corpus, not proved.

### Open

- Floats (`F32`, `F64`) by the same scheme; Wasm's NaN bit patterns are nondeterministic.
- `u8` and checked (non-wrapping) arithmetic are derivable from the operations above.
- `plainV` excludes the integer types, so they cannot yet be `withborS` leaves.
- The MVP backend lowers without types, so `I64` values are boxed (a full-width word leaves no
  bit to tell a pointer from an immediate). Type-directed layout would unbox them.

---

## 9. Entry 8 — arrays

### Motivation

The place structure has run-time-sized *values* (`μ`, §6) and statically sized *families of
places* (blocks, §5), but no run-time-sized family of places. An array is that: `n` leaf places at
consecutive locations, `n` known only at run time. It is the type-level counterpart of the
iterated separating conjunction `⊛_{i<n}`. Records are not arrays: a record's labels have no
arithmetic, its length is static, and its fields may differ in type, so it cannot be indexed at
run time.

### Types

    A ::= … | [L]                                  (VTy.fam L)

    Array A       ≜ [Ref A]
    ArrayImm @a A ≜ [Imm @a A]

`[L]` is the run-time family `⊛_{i<n} L` of leaf places. A value of `[L]` is a pair `(ℓ, n)` of a
base location and a length `n : I32`, and its `i`-th leaf is the location `ℓ + i`, a value of `L`.
An owned array is the family of its `n` cells. A borrowed array is the family of its `n` leaf
borrows at one lifetime, as a borrowed block is the family `famTy` of its leaf borrows (§5).

Scoping, well-formedness, lifetime substitution and `TyEq` treat `[L]` as a unary former over `L`.

    Imm̲ 'b [L] ≜ [Imm̲ 'b L]        Δ ⊢ [L] ⊐ @a  if  Δ ⊢ L ⊐ @a

`[L]` is never persistent: it holds cells or borrows of cells.

### Borrowing an array

An array is a value, so it is borrowed as any value is: in a cell. `Imm @a (Array A)` and
`Mut @a (Array A)` are borrows of a cell `Ref (Array A)` that holds the handle (Rust's `&Vec` and
`&mut Vec`), made by `withbor` (§1). No rule is added for them:

- **The family of leaf views** comes from `withload` (`[TR]` p. 3) at `Imm @a (Array A)`: its
  callback receives `Imm̲ 'x (Array A) = ArrayImm 'x A` at a lifetime `'x ⊏ @a`. That is the
  array borrowed as a family, and 6.131 at `[L]` is what makes it sound.
- **Mutation through `Mut @a (Array A)`** is `withswap` (§1): its callback owns the array for a
  moment and uses the owned operations.

**Leaf views are direct places.** `array_get` takes a leaf view out of the family `ArrayImm 'x A`
at the family's own lifetime `'x`. In the family each leaf's `imm` cell is at the top level of the
resource and no cell owns the leaves, so `get` hands out one of them and `↭` is never asked to
accept a cell below a parent (as in `experiments/Places` §2). A leaf view at `@a` taken directly
from `Imm @a (Array A)` would sit below the `imm` cell that holds the handle, whose witness owns
the leaves; the update relation excludes exactly that (§5 Open; `experiments/FrameEnd`,
`imm_view_rejected`), so the view is taken at the shorter `'x` of `withload`.

### Machine

Three primitives, `Prim.tab`, `Prim.idx` and `Prim.drop`, each with one head step. With
`len(c) = c` when `c < 2³¹` and `0` otherwise (a negative length is the empty array):

    (μ, tab (c, f))       ↦ (μ ⊎ {ℓ+i ↦ () | i < n},
                              store (ℓ+0) (f 0); …; store (ℓ+n−1) (f (n−1)); (ℓ, n))
                            where n = len(c) and ℓ, …, ℓ+n−1 are fresh
    (μ, idx ((ℓ, n), i))  ↦ (μ, inj₁ (ℓ + i))   if i < n, unsigned
                          ↦ (μ, inj₂ ())        otherwise
    (μ, drop (f, (ℓ, n))) ↦ (μ, f (free (ℓ+0)); …; f (free (ℓ+n−1)); ())

`tab` places the cells, then runs the ordinary term that fills them; `drop` is a pure step to the
ordinary term that empties and frees them. The machine stays deterministic at each host up to the
choice of fresh locations, as `alloc` is. An index out of range takes the sum's error branch; no
step is stuck on a well-typed argument.

### Relation

    𝒱⟦[L]⟧δ(v) ≜ ∃ℓ c. ⌜v = (ℓ, i32 c)⌝ ⋆ ⊛_{i < c} 𝒱⟦L⟧δ(ℓ + i)

At `Array A` this is `n` owned cells, each holding a value in `𝒱⟦A⟧`; at `ArrayImm @a A`, `n`
`imm` cells at `@a`. Nothing else changes in the typed world: a block allocation is `n` of
`TW.alloc`, a drop `n` of `TW.free`.

### Operations

The constants, at a dead context; `A ⇒ B` is `U(A ⊸ F B)`:

| constant | type |
|---|---|
| `array_new` | `!(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)` — `tab`: the tabulator's result at each index |
| `array_free` | `!(!(A ⇒ 1) ⊗ Array A ⇒ 1)` — `drop`: each element to the consumer, in index order, then the cells freed |
| `array_size` | `!(Array A ⇒ Array A ⊗ I32)` |
| `array_replace` | `!(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))` — the old element, or the new one back if out of range |
| `array_len` | `!(ArrayImm @a A ⇒ I32)` |
| `array_get` | `!(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)` — `idx`: a leaf view at the family's lifetime |
| `array_copy` | `!(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)` |
| `array_forget` | `!(ArrayImm @a A ⇒ 1)` |

`array_replace` on `Mut @a (Array A)` is `withswap` with `array_replace` in its callback.

Implicit destructors (§12): `Array A` has one when `A` does, `array_free` with the destructor of
`A` as the consumer; `ArrayImm @a A` is forgettable, by `array_forget`.

### Lowering

An array is one allocation of `n` slots; slot `i` is at `base + i·s`, with `s` the slot size.
`idx` is an unsigned compare of `i` with `n` and an address computation — a `getelementptr` and
an `icmp ult` in LLVM, `i32.lt_u` and `i32.mul`/`i64.add` in Wasm. `tab` allocates the block and
fills it in a loop; `drop` loops over the slots, moves each value to the consumer, and frees the
block once. The MVP backend's uniform representation keeps a header word in every slot, so its
`s` is 16 bytes and an element's location is an ordinary cell address; a type-directed layout
has `s = sizeof A` and no header.

### Baseline

`fundamentalC` covers the new constants and `adequacyC` is unchanged in statement; the machine
gains three head steps, parametric in the host as before. `[L]` is one `VTy` former, and every
lemma of the typed world proved by induction on types or on positions has its `[L]` case (6.131,
6.60, the images and invariants of reborrowing), which is what makes `withload` sound at arrays.

### Library, not primitive

- **`Vec A`**, a growable array: reallocation is a new array and a move of the leaves, under
  `Mut`. Its capacity slots are `1 ⊕ A` until uninitialised leaves exist.
- **`Str`**: a byte array with the UTF-8 invariant kept by the library's constructors; string
  literals as `Imm ⊤ Str` in the data segment.
- **`u8`**: an integer width stored in bytes.

### Open

- A primitive array borrow `Array A ⊸ (∀'c. [M 'c A] ⊸ ['c] T) ⊸ Array A ⊗ T` with no cell, and
  mutable families `[Mut 'c A]` (a leaf `Mut` view, `iter_mut`). Semantically each leaf would be
  framed by its own 6.64/6.65 frame, nested; not built.
- `split_at` at a run-time index, returning two disjoint sub-families at the borrow's lifetime.
- `iter`/`iter_mut` over the leaf family, as a lifetime-indexed `Iter` (§7).
- `replicate` for persistent `A` without a tabulator; creation from a list.
- Uninitialised leaves (`Uninit`), and sized types (#72).
- Buffers and strings as externs (the previous §9) are withdrawn in favour of the library forms
  above.

## 10. Entry 9 — persistent variables

A value type is **persistent** when its values hold no resource (`VTy.persistent`,
`Core/Persistent.lean`): `1`, `0`, `Unk`, `!A` for any `A`, and `⊗`, `⊕`, `[@a]` and `μ` over
persistent types. `I32` and `I64` (§8) are persistent. `U C` is not, because a thunk holds its
closure's resource; nor are `Ref`, `Imm` and `Mut`.

`Core` extends the paper's context relations with one constructor each: `Ctx.SplitP` may send a
persistent live slot to both sides, `Ctx.DeadP` may drop one, and `Ctx.SoloP` may drop one beside
the variable used. So persistent variables are copied and dropped implicitly, at dead-context rules
and at variable leaves alike, and `copy_bang`/`forget_bang` are needed only to make that explicit.
Soundness (`vCE_empty_of_persistent`): at a persistent type the value relation holds only at `∅`,
and `∅ = ∅ ⋆ ∅`. The paper's `Ctx.Split` is unchanged, and every paper relation converts into its
extension, so the embedding (§3) still applies.

### Open

- The promotion premise `!Γ` (every live slot at `!A`) is not widened to "every live slot
  persistent".

---

## 11. Entry 10 — externs and standard I/O

### Motivation

A program meets the world only at named boundaries. Each boundary is an extern whose contract is
a semantic type (decision 27), and every effect is performed through a capability that the
program was given (decision 30): there is no ambient authority. Standard input, standard output
and standard error are the first capabilities, enough to write command-line tools.

### Externs

    extern name : A

adds a live slot of type `A` to `main`'s initial context, the last declared at index 0
(syntax-core §10). The **contract** of an extern is its semantic type: a value `v` at resource
`ρ` implements `extern name : A` when `vC true A ls δ v ρ`. Externs are named hypotheses, not
rules: no `CDerives` constructor and no machine step is added for them, and an implementation
may be host code, code of our own that the compiler compiles, or a Lean term (a model). The
Fundamental Property quantifies over every closing substitution, so a checked `main` is safe
under every implementation of its externs that meets their contracts.

The allocator is not an extern: it is part of the compiled runtime, trusted against its written
specification (`Backend/README.md`). §8's integer operations are not externs: they are term
constants, and the theorems are parametric in the host instead.

### Opaque host types

    A ::= … | Input | Output                       (VTy.opq k, k ∈ {input, output})

An opaque type is a leaf with no introduction and no elimination rule. A value of one can be
moved, stored in a cell and passed to an extern that takes it; it cannot be inspected, copied or
dropped. Each opaque type `k` has a **model**, a predicate `k.Holds` on values, and

    𝒱⟦k⟧δ(v) ≜ ⌜k.Holds v⌝                                      (in both modes)
    Imm̲ 'b k ≜ Unk          Δ ⊢ k ⊐ @a (at every @a)          not persistent, no destructor

- `Input.Holds v`: `v` is a byte list `Bytes = μX. 1 ⊕ (I32 ⊗ X)`, the input not yet read.
- `Output.Holds v`: `v = (fd, bs)` with `fd : I32` the stream and `bs : Bytes` the bytes written
  to it, most recent first. The stream travels with the content: whichever cell holds it, a
  write goes to `fd`.

**Host handles.** An extern that yields a host resource (a file descriptor, a host-table index)
yields a non-persistent opaque type, never `I32` or `I64`. A persistent handle could be copied
and used after it is closed (l_lang's L-199). `Imm̲` of an opaque type is `Unk`, so a borrow of
a cell holding a handle cannot copy it out either. In compiled code the content of an `Input` or
`Output` cell is the stream's file descriptor.

`VTy.opq` is one `VTy` former, a leaf: every lemma by induction on value types gets a case
that is the `I32` case with `Imm̲ = Unk`, as at `U C`. A new host resource is a new `k` with its
model, not a new former.

### Capabilities

Standard I/O is a bundle of three capabilities, one per effect:

    extern stdin  : ref input
    extern stdout : ref output
    extern stderr : ref output

A capability is a cell whose content is opaque. The operations take a `Mut` borrow of the cell
and hand it back:

| extern | type |
|---|---|
| `read_byte` | `!(all 'a < top. mut 'a input => mut 'a input * (i32 + 1))` — the next byte, or `inr ()` at the end of the input |
| `write_byte` | `!(all 'a < top. mut 'a output * i32 => mut 'a output)` — the low 8 bits of the integer |

So a function's type shows which capabilities it can use: a helper that writes takes
`mut 'a output` (or the cell, `ref output`), one that reads takes `mut 'a input`, and one that
takes neither performs no I/O. A `def` may use the persistent externs declared before it (the
operations, which carry no authority), but never a capability: a capability is not persistent,
so it is visible only in `main`, and a helper that does I/O takes it as an argument. The `def`
is re-checked at each use, where the extern is `main`'s slot, as for any `def`.

`stdout` and `stderr` share the type `Output`: a writer is given an output stream, and which one
is its caller's choice. The bundle is split and lent with the existing machinery (§5): `main`
destructures it, borrows one capability with `withbor2` and passes `mut 'a output` to a helper,
or passes the whole cell.

**Why two operations.** Bytes are the unit of both streams, and end of input is the `inr ()` of
a sum. Everything else a command-line tool needs — reading a line or a chunk into a borrowed
array (§9), writing a string from a borrowed array, parsing and printing numbers, hex — is a
loop over these two, written as library code (`corpus/io-aoc.bc` reads each line into one
borrowed array; `corpus/io-wc.bc` prints decimal). A chunk primitive would change only the cost of a
call, and the runtime may buffer below the interface. A new primitive is added when a loop over
these two cannot express it.

**`main`.** A program with capability externs has `main : F (Caps ⊗ A)`, where `Caps` is its
capability externs in declaration order (one alone, several as a right-nested tuple). The
capabilities have no destructor (§12), so `main` hands them back; the runtime then ends the
streams. `A` is the program's result; `bcc interp` prints it, so it is persistent.

**Loops.** Recursion is structured (decision 24), so a loop over the input is a step function
iterated a bounded number of times (the corpus composes `twice` with itself), and a step after
the end of the input does nothing. The bound is part of the program.

### The model

In the model the capabilities are cells holding the remaining input and the accumulated output,
and the operations are ordinary core terms over the transparent representation
(`Core/Stdio.lean`): `read_byte` is `withswap` popping the head of the byte list, and
`write_byte` is `withswap` consing onto it. Four more externs construct and read capabilities;
they are the model's harness, a handler that serves the streams from memory:

| extern | type | model |
|---|---|---|
| `mk_input` | `!(Bytes => ref input)` | `alloc` |
| `mk_output` | `!(i32 => ref output)` | `alloc (fd, nil)` |
| `take_input` | `!(ref input => Bytes)` | `free` |
| `take_output` | `!(ref output => i32 * Bytes)` | `free` |

**The run.** The checker wraps a `main` with capability externs into a closed-over-externs
program `run_io : Bytes -o F ((i32 * Bytes) * ((i32 * Bytes) * A))`: it makes the declared
capabilities from the input bytes by `mk_input`/`mk_output` (fd 1 for `stdout`, 2 for
`stderr`), runs `main`'s body with them bound to their names, takes the capabilities back and
returns the outputs with `main`'s result. An undeclared stream is made and taken back empty.
`run_io` is checked like any `main`, so it has a `CDerives` derivation at the context of the
operation externs; `bcc interp` runs it with the model implementations.

### Theorems

- **The model meets the contracts** (`Core/Stdio.lean`). Each model implementation is in the
  relation at its extern's type, at `∅`: `readByte_meets`, `writeByte_meets`, `mkInput_meets`,
  `mkOutput_meets`, `takeInput_meets`, `takeOutput_meets`. Each is the Fundamental Property of the
  term at the transparent type, and the transparency of the relation at `Input`/`Output`
  (`vC_bytes`, `vC_outRep`: the relation at the representation is the model).
- **End to end, every implementation** (`externs_every_run`, `externs_safe`). If `run_io`'s
  result `R` is persistent and `γ` implements each of its externs at `∅` (the named hypothesis
  `ExternsMeet`), then for every input byte list, every run of `run_io[γ] inp` from the empty
  memory, under every allocator, can be continued to a value of `R` at the empty memory, and no
  run is stuck. It is `adequacyD`'s form (`theorem32D`).
- **End to end, the model** (`io_every_run`): the same at the model implementations, with the
  outputs byte lists.
- **Every run of `main`** (`externs_main_safe`): at any extern context, from every
  configuration whose resource satisfies the contracts, no run of `main` is stuck. This is
  `fundamentalD` at `main`.
- **The run `bcc interp` performs** (`IORun.every_run`, `Frontend/Check/Externs.lean`): the
  checked `run_io` with the model of each extern, chosen by type, carries the proofs
  `io_every_run` takes, and `bcc interp` runs exactly `run_io[γ] inp`.
- **No capability, no effect** (`wpTSD_frame_own`). A cell owned by the frame of a computation
  holds the same value at the end of every value run of it. A computation's resource is what its
  context and captures hold, so a function given neither the `stdout` cell nor a borrow of it,
  nor an `Output` in a cell it owns, leaves the stream's content as it was: it writes nothing to
  standard output.

**Adequacy's scope.** The empty-memory conclusion is about the model's cells. File descriptors
and other host handles are not memory: adequacy says nothing about them (whether a stream was
flushed or closed). That the compiled lowering behaves as the model is tested, not proved.

### Assurance

Each extern records its assurance level, on the ladder of decision 27: (1) assumed,
(2) interpreter-checked, (3) property-tested, (4) typed low-level (typed unsafe code),
(5) boundary-checked, (6) semi-automatically verified, (7) proved. `bcc trusted <file>` lists
every extern a program declares with its level and its implementation; an unproved boundary is
the program's trusted base.

| extern | model | host implementation |
|---|---|---|
| `stdin`, `stdout`, `stderr` | proved (7): cells with the model content | runtime cells holding the fd; assumed (1), checked against the model on the corpus |
| `read_byte`, `write_byte` | proved (7) | WASI `fd_read`/`fd_write`; interpreter-checked (2): the flat-IR interpreter runs the lowering against scripted streams |
| `mk_input`, `mk_output`, `take_input`, `take_output` | proved (7) | none: the model's harness, not compiled |

An extern the compiler has no implementation for is reported as assumed and not compiled.

### Lowering

The runtime allocates the three cells holding file descriptors 0, 1 and 2, runs `main`, frees
the cells `main` returns and prints the result. `read_byte` is WASI `fd_read` of one byte from
the cell's descriptor (end of input, or an error, is `inr ()`); `write_byte` is `fd_write` of one
byte. Both are unbuffered, so a prompt appears before the next read. The plain LLVM/libc
counterpart is `read(2)`/`write(2)` on the same descriptors (or `getc`/`putc` on a `FILE *`): no
WASI-only feature is part of the semantics (decision 25).

### Programs that run until their input ends

`main` may return a loop over its capabilities:

    main : F (U (Loop (Caps ⊗ A) (Caps ⊗ B)))

The runtime drives it: it observes `next` until the loop finishes with `(caps, a)`, then takes
the capabilities back and prints `a`; it never closes it. Nothing in the kernel changes (no
rule, no relation clause, no machine step); what is new is this obligation of the runtime and
its theorem. A driven program is covered one prefix at a time: for every `n`, `run_io` followed
by `driveE n` is a closed program, and every run of it from the empty memory, under every
allocator, continues to a value at the empty memory (`externs_loop_every_run`,
`io_loop_every_run`, and `IORun.loop_every_run` at the term `bcc interp` runs). A run that
finishes after `k` observations is the run of the `k`-th prefix, which ends at `inl`. A loop
that never finishes runs forever, and every finite prefix of the run is safe. `run_io` is a
loop too: its `next` observes `main`'s loop and, when it finishes, takes the outputs; its
`close` closes `main`'s loop and takes them.

### The I/O library

`lib/io.bc` is ordinary library code over the externs, in scope in a program whose `main`
uses the capabilities ambiently (below):

| name | type | |
|---|---|---|
| `getb` | `ref input => ref input * (i32 + 1)` | one byte, the capability handed back |
| `putb` | `ref output * i32 => ref output * 1` | one byte out |
| `put_dec` | `ref output * i32 => ref output * 1` | a number in decimal |
| `bytes` | `ref input => U (iter i32 (ref input) (ref input))` | the input as a stream of bytes, finishing, or closing early, with the capability |

Each hides the borrow: it lends the capability to one operation and hands it back. A line
reader is not provided: an observation must terminate, so a line of unbounded length is a loop
of its own; programs consume `bytes` and keep the line in their state.

### Sugar

Each form below is elaborated by the frontend into ordinary core, which the unchanged checker
then checks; the theorems apply to the elaborated program with no new case. None exists in the
kernel, the checker's rules or the proofs. `bcc desugar <file>` prints the elaborated program,
and `corpus/sugar/` pairs each sugared program with its hand-written core form, which must
elaborate to the same term.

- **Ambient capabilities in `main`.** A program that declares no externs and whose `main`
  mentions `stdin`, `stdout` or `stderr` gets the I/O library, the operations, and an `extern`
  for each capability it mentions (in the order `stdin`, `stdout`, `stderr`). `main : F A`
  elaborates to `main : F (Caps ⊗ A)`: every terminal `return V` of its body becomes
  `return (caps, V)`, and any other terminal `T` becomes `r <- T; return (caps, r)`, the
  capabilities read by name where the path ends. Nothing else is ambient: a `def` never sees a
  capability.
- **Lending a capability to one call, `&c`.** In `x <- M; N`, one `&c` in `M` elaborates to
  `r <- M[c/&c]; let (c, x) = r; N`: the call takes the capability and hands it back first, as
  `getb`, `putb` and `put_dec` do.
- **`for (x : A) in V with (y : T, …) { M }; N`**, at the end of an ambient `main`, where `V`
  mentions one capability `c` and is an iterator `U (iter A C C)` over it. It elaborates to a
  loop by `unfold`: the state is the iterator, the other capabilities and the listed variables.
  Its `next` observes the iterator: an element `x` runs `M`, which rebinds the state by name, and
  the loop goes on; at the end the capability the iterator hands back is bound to `c`, `N` runs,
  and the loop finishes with the capabilities and `N`'s value. Its `close` closes the iterator.
  `main : F A` then elaborates to `main : F (U (Loop (Caps ⊗ A) (Caps ⊗ 1)))`. This is the
  top-level form of #59's `for`; a `for` inside a function needs a finite consumer and is not
  provided.

### Designed, not built

- **More capabilities, one pattern.** Each is a cell with opaque content, a model and externs
  taking a `Mut` borrow: `Args` (`next_arg`: the next argument into a borrowed array, or the
  end), `Env` (lookup by name into a borrowed array), `Fs` (open yields an `Input`/`Output`, close
  consumes it), `Net`, `Clock`, `Random`.
- **Exit.** The exit status is `main`'s result at `A = I32`; not yet passed to the host.
- **Handlers.** A capability's meaning is its model and its operations are externs, not rules,
  so a capability can be served by any value meeting the extern's type: the host, the model
  (`bcc interp`'s handler), or later a user-defined handler (#18) such as a mock input or a
  recording output. Nothing in the typing depends on the host.

### Baseline

`VTy.opq` is one leaf former; no `CDerives` rule and no machine step is added. `fundamentalC`,
`adequacyC`, `fundamentalD` and `adequacyD` keep their statements and cover the new former.

### Open

- I/O errors are not modeled: a read error is end of input, a write error is ignored.
  Distinguishing them changes both operations' types and the model, which has no errors; left
  for an entry with a failing model.
- `for` has no early exit: a program that stops reading keeps a flag in its state.
- The host implementations agree with the model on the corpus; that is tested, not proved.
- `wpTSD_frame_own` is about the end of a value run, not intermediate states.
- Destructors for host resources, which perform I/O and can fail (§12 Open).
- `main` with borrowed capabilities (lifetime-parametric externs) is not provided.
- `Args`, `Env`, `Exit`, `Fs` and the rest are designed only.
- `|>` pipelines (#59) are not provided.

---

## 12. Entry 11 — implicit destructors

Types stay linear. Where a program lets an owned value go unused, the checker inserts a call
of the value's **destructor**, and that call is the value's one use. The elaborated program is an
ordinary linear core term with an ordinary `CDerives` derivation, so every owned value is still
consumed exactly once, and leak freedom is `adequacyC` on the elaborated term. No typing rule,
judgment index or semantic definition changes. From `experiments/Affine`.

### Destructors

`dtorE T : T ⊸ F 1` is a closed term, defined by one structural recursion on `T`
(`Core/Dtor.lean`). `HasDtor T` is the class of types it is defined at, and `dtor_wf` types it
in `CDerives` at every lifetime context and every dead context, using existing rules only.
There are three classes of value type.

1. **Forgettable types**: the persistent types (§10: `1`, `0`, `I32`, `I64`, `Unk`, `!A`, and
   `⊗`, `⊕`, `[@a]`, `μ` over them), the borrows `Imm @a A`, `Mut @a A`, and `⊗`, `⊕`, `[@a]`
   over these. The destructor is `forget = λx. ()` (at a borrow, the `forgetImm`/`forgetMut`
   constant), componentwise at `⊗`, `⊕`, `[@a]`. Discarding one does
   nothing: it deallocates nothing and runs no code, and ending a loan early is safe. These types
   are genuinely affine. Persistent ones were already dropped by context splitting (§10), with no
   call. Every type of `Core/Records.lean`'s `Affine` is here (`hasDtor_of_affine`).
2. **Owned types with a derived destructor.** The destructor is an action:
   | type | destructor |
   |---|---|
   | `A ⊗ B`, `A ⊕ B`, `[@a] A` | componentwise |
   | `Ref A` | `free`, then the destructor of `A` |
   | `μX. T`, `T` in `FShape` (§6) | `foldOwn`, whose algebra is the destructor of `T[1/X]` |
   | `U(C & F 1)` | `close`: force, then the second projection |
   | `U(νX. C & F R)`, `R` closed with a destructor (`D A`, `Stream A`, `Iter A R₀ R`) | `close` (§7), then the destructor of `R` |
   These are linear. A value of one of these types that goes unused is consumed by its
   destructor, which the checker inserts. Because the destructor deallocates memory and, at codata,
   runs the object's `close` code, where it is inserted can be observed.
3. **Types with no destructor**: `U C` other than the codata above (a thunk of `F A` or of
   `A ⊸ C` can be disposed of only by running it, which has effects and may need an argument), `μ`
   outside `FShape`, a type variable, and anything built from one of these. These are strictly linear.
   A variable of one of these types must be consumed, and an unused one is a type error that
   names the type.

### Insertion policy

A variable is **owed** to the body of its binder (`x <- M; N`, `let (x, y) = V; M`, a `case`
arm, `fun (x : A) -> M`) when its type is in class 1 or 2, it is not persistent, and it is not
declared `linear`. The body must consume an owed variable on every control path; on a path that
does not, the checker consumes it by its destructor:

- **At the end of the path.** The destructor calls go immediately before the path's terminal
  computation: `return V`, `force x`, an application, a projection, an instantiation,
  `nu_out`. They go after every effect of the path and before the result is
  produced. A value never used is therefore dropped at the end of its binder's scope, and a
  `case` arm or a `<M, N>` component that does not consume an owed variable drops it, while one
  that does, does not.
- **In reverse binding order.** Several owed variables are dropped most recently bound first.
- **Tail positions.** The owed set passes to the body of `x <- M; N`, `let () = V; M` and
  `let (x, y) = V; M` (without what `V` or `M` consumed), to both arms of a `case`, both
  components of `<M, N>`, the bodies of `fun` and `Fun`, and through `nu_in` and
  ascriptions. An owed variable that the head `M` of `x <- M; N` mentions is owed to `M`, which
  must then consume it on every path of `M`, dropping it where it does not.
- **Not moved across effects.** A drop is never placed earlier than the path's terminal
  computation. Codata `close` runs code, so moving it would reorder effects.
- `<>` and `absurd V` absorb any context (§11 of `docs/syntax-core.md`), so no drop is inserted
  before them. A value (`thunk M`, `run M`, …) starts its computations with nothing owed: a thunk
  that captures a variable consumes it.

**Opt-out.** `linear x <- M; N` (and `linear x : A <- M; N`) declares `x` owed to nobody:
`N` must consume it on every path, as before this entry. It is for values whose silent
destruction is a bug, such as a transaction that must be committed or aborted.

### Soundness

The elaborated term, with drops inserted, is what the checker returns with its `CDerives`
derivation (`checkProgram_sound`, unchanged). The drop is `unitE` over `lolliE` of the variable and
`dtor_wf` (`drop_derives`). `fundamentalC` and `adequacyC` apply unchanged, so the baseline theorems
(§1) and every theorem of entries 1–10 are preserved; nothing in them is touched. Placement does
not affect soundness: any placement of a destructor call is a `CDerives` derivation. The policy
fixes when the effect of a drop happens.

### Open

- **Destructors with effects that can fail.** A host resource (§11), such as a file handle, may
  need a destructor that performs I/O or can fail. `dtorE` is total and pure apart from
  deallocation and `close`. Whether such a type gets an implicit destructor, and what a failing
  one does, is not decided. Until then these are class 3.
- **Externs** are not owed. `main` must consume every non-persistent extern.
- **`linear` on other binders** (`let`, `case` arms, `fun`) is not provided.
- **Values** do not drop. The value `V` of `let`/`case` and the operands of value forms consume
  what they mention, on every path.
- **Earlier placement** (after the last use rather than at the end of the scope) would free memory
  sooner and is equally sound. It is not done, because it reorders `close` effects.
- **A deep-free primitive** for `μ` would replace the `foldOwn` traversal in the lowering.

---

## 13. Entry 12 — every run is safe

### Motivation

`adequacyC` is angelic: *some* run of a well-typed program is safe and leak-free. `alloc↦` and
`tab↦` may choose any free location, and a compiled program runs under a real allocator, which
reuses freed locations. Adequacy has to hold for every run (issue #75).

### Allocators

An **allocator** `A` (`Alloc`) answers the `k`-th allocation of a run, from memory `μ`, for a
block of `n` cells, with a location `A.pick k μ n`; at every memory of finite domain, the cells
`pick k μ n + i`, `i < n`, are free. The answer may depend on the count `k`, so an allocator can
be any history-dependent policy, least-free reuse included. An **allocator run**
(`ARun A k μ e k' μ' e'`) is a run whose `k`-th allocation step (`alloc v`, or `tab` of `n`
cells) is at `A.pick k μ n`; every other step is a machine step that allocates nothing. The
machine is unchanged.

### Semantics

`wpTS`'s run conjunct becomes: for every allocator `A` and count `k`, the run is an allocator
run of `A` from `k`. Nothing else in `wpTS`, the relation or `CDerives` changes. The rules that
build runs (value, the pure head steps, `alloc`, `free`, `load`, `store`, bind, host steps,
`tab`, `idx`, `drop`) build allocator runs: `alloc` and `tab` are sound at any free location or
free block.

The rule `wpTS_step`/`cC_step` for a step in front takes a step that allocates nothing
(`Step1N`): a `tab` of zero cells changes no memory but still chooses a location.

### Every run

Every non-allocating step is deterministic (`Head` at a fixed host), and every run is an
allocator run of the allocator that replays its choices. So:

- **`wpTSD`**, the demonic `wp`: from every configuration, every run of `e` can be continued to a
  value run that lands in the postcondition. Hence no run reaches a stuck state, and every run
  that reaches a value lands in the postcondition.
- **`wpTS_demonic`**: `wpTS ⊢ wpTSD`, and so the Fundamental Property at `wpTSD`
  (`fundamentalD`).
- **`adequacyD`**: every run of a closed `F 1` program from empty memory can be continued to `()`
  at empty memory; no run is stuck, and a run that reaches a value reaches `()` at empty memory.

Divergence is allowed by `wpTSD`'s form (partial correctness plus safety). Every computation the
relation holds terminates under every allocator: codata (§7) is observed one finite observation at
a time.

### Borrowed closures

A `!` closure behind an `Imm` borrow is callable (`Imm̲ (!A) = !A`), and a caller reaches it at
the program's view. It is in the relation only if every allocator runs it safely, so a closure
that reads a location after freeing it is excluded (#41). `staleL`, which frees `x`, allocates
`y` and loads `x`, is in `wpTSAngelic` (`staleL_angelic`): on the run that reuses `x`'s
location for `y`, the load succeeds. It is in `wpTS` at no postcondition
(`staleL_not_every_alloc`), because `Alloc.atCount` puts `y` elsewhere and the load is stuck.
So `λ_. staleL` is outside the relation at `!U(1 ⊸ F 1)` (`staleClosure_not_vC`), and outside
an `Imm` borrow of it (`staleClosure_not_immPayload`), in `Core/Stale.lean`.

### Baseline

`fundamentalC` and `adequacyC` keep their statements. The previous run conjunct is
`wpTSAngelic`, and `wpTS ⊢ wpTSAngelic` (`wpTS_angelic`, at the least-free allocator).

### Open

- The host is deterministic (§8). A nondeterministic host would be a second oracle, answered
  like the allocator.
- The allocator's answer depends on the count and the memory, not on the program; that covers
  every run of this machine.

---

## Status

Entries 2–6 are implemented in the library directory `Core/`, with one `fundamentalC` and
`adequacyC` covering every rule; §7's `νX. C` is `Core/NuRel.lean` and `Core/Nu.lean`, and the
checker reads `nu X. C`, `iter A R R'`, `nu_in`/`nu_out` and `unfold[C, S]`. Entries 7 and 9 (§8, §10) are implemented; §8 extends `Paper/` and `Support/` with the literal
and host-step forms. Entry 8 (§9, arrays) is implemented: the former and its lemmas in `Core/Types.lean` and the typed
world, the constants in `Core/Arrays.lean` (`Core/ArrayWp.lean` for the steps), the three machine
steps in `Paper/` and `Support/`, the checker (`array`, `array_imm`, syntax-core §8b) and the
backend. Entry 10 (§11) is implemented: the former `VTy.opq` in `Core/Types.lean` and the
typed world, the model and the end-to-end theorems in `Core/Stdio.lean`, the checker (`input`,
`output`, the `run_io` wrapper) and the backend (`Backend/Clos`, `Backend/Flat`, WASI imports). Entry 11 (§12) is implemented in
`Core/Dtor.lean` and the checker (`Frontend/Check/`), with no change to `CDerives`. Entry 12
(§13) is implemented in `Core/Alloc.lean`, `Core/World.lean`, `Core/Demonic.lean` and
`Core/Stale.lean`.

---

## Changelog

- **0.10** (2026-09-27) — Entry 10 (§11): externs and standard I/O. The opaque host types
  `Input`/`Output` (`VTy.opq`), with a model and `Imm̲ = Unk`; the capabilities `stdin`,
  `stdout`, `stderr` as cells, `read_byte`/`write_byte` on `Mut` borrows of them; the model
  harness `mk_input`, `mk_output`, `take_input`, `take_output`; `run_io`; the model meets the
  contracts, `externs_every_run`/`io_every_run` in `adequacyD`'s form, `externs_main_safe`, and
  `wpTSD_frame_own` (no capability, no effect); a `def` may use the persistent externs declared
  before it; assurance levels and `bcc trusted`. `Loop A B` (§7; `D A = Loop A 1`) with the
  driver typed at every loop (`d_driveL`); programs that run until their input ends
  (`externs_loop_every_run`, `io_loop_every_run`); the I/O library; the sugar: ambient
  capabilities in `main`, `&c`, and `for` at the end of `main`, each elaborated before checking.

- **0.9** (2026-09-27) — Entry 12 (§13): every run is safe. `wpTS`'s run is an allocator run at
  every allocator; `wpTSD` (every run continues to a value in the postcondition), `fundamentalD`
  and `adequacyD`. The angelic run is `wpTSAngelic`, a corollary.

- **0.8** (2026-09-27) — Entry 8 revised (§9): arrays. `[L]` (`VTy.fam`) is the run-time family
  `⊛_{i<n} L` of leaf places, with `Array A = [Ref A]` and the borrowed family `[Imm @a A]`; the
  machine steps `tab`, `idx` and `drop`; `array_new`, `array_free`, `array_size`,
  `array_replace`, and on families `array_len`, `array_get` (a leaf view at the family's
  lifetime), `array_copy` and `array_forget`. An array is borrowed in a cell, by `withbor`; the
  family comes from `withload`, mutation through `Mut` from `withswap`. Buffers and strings as
  extern types are withdrawn; `Vec` and `Str` are library code over arrays. §11 and §12 no longer
  mention them.

- **0.7** (2026-09-27) — Entry 6 revised (§7): one codata former `νX. C` with positivity
  (`X` only as `U X`, under `⊗`/`⊕` of observation results), `nuIn`/`nuOut` and coiteration
  `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)`. `D A` and `Stream A` become abbreviations and their
  fixed formers and six rules are deleted (`fixD`, `unfoldS` are `unfold` at their bodies). The
  finite iterator `Iter A R R'` is the first new instance. §12: `U(νX. C & F R)` has a destructor
  that closes and then drops the residual `R`.

- **0.6** (2026-09-27) — Entry 11: implicit destructors (§12). Types stay linear. The checker
  inserts a derived destructor (`dtorE`, `Core/Dtor.lean`) where an owned value goes unused: at the
  end of each path, in reverse binding order. `linear` opts a binder out. No `CDerives` change.

- **0.5** (2026-09-25) — §8 as implemented: integer literals and host operations are term
  constants, one host step in the baseline machine, every theorem parametric in the host; §1 notes
  the host step.

- **0.4** (2026-09-25) — Entries 7–10: integers as opaque types with Wasm's operations and
  signature-parametric theorems (§8), buffers and strings as opaque linear types (§9), persistent
  variables used freely (§10), externs as hypotheses of the theorems and stdio as capabilities
  (§11). The stream former is renamed `Stream`.

- **0.3.1** (2026-09-25) — Status: entries 2–6 are implemented in the library, `Core/`.
- **0.3** (2026-09-25) — Entries 2–6: the call-by-push-value core with the baseline restated
  through the embedding (§3), non-strict frame lifetimes (§4), blocks, family borrows and records
  (§5), recursive types and the three folds (§6), delay and stream codata with `fixD` (§7).
- **0.2** (2026-09-24) — §2 restated as the exponential `!T`, replacing closed code
  `fn T₁ T₂` (which is `!(T₁ ⊸ T₂)`): adds `!I-Λ`, `Δ ⊢ !T ⊐ @a` and promotion over `!Γ`; the
  `ownedFn` and `mutClosure` programs. From the experiment `experiments/Bang`, originally developed in `borrow_lang`.
- **0.1.1** (2026-09-24) — §2: capture and `FnMut` examples; the `Open` list records what
  mutable borrows of closures and owned captures still need.
- **0.1** (2026-09-24) — Baseline (§1). Entry 1, closed code (§2), from the experiments
  `experiments/CBPVSplit`, `ModesLabels`, `Shifts` and `BorrowedClosures`, originally developed
  in `borrow_lang`.
