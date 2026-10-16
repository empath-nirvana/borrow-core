# Borrow core — specification

Version 0.57 · 2026-10-15

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
| `FnMut` | `[@c] U(Aff^c T₁ T₂)`, the affine closure of §22, called through a `Mut` borrow by `withswap` |
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
an `F A`, a `&` of two observation trees, or an observation that takes a closed argument,
`A ⊸ D` with `X` not in `A` and `D` an observation tree (§22). In each result `A`, `U X` occurs
only under `⊗`, `⊕` and `[@a]`: `A` is `U X`, `B ⊗ B'`, `B ⊕ B'` or `[@a] B` of such types, or a
type in which `X` does not occur (`VTy.Poly`). So `X` is never in an argument, under a `Ref`, a
borrow, a `!`, a `μ` or another `U`, and a `νX. C` always has at least two observations.

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
  the argument of an observation (`A ⊸ …` with `X` in `A`, a sink), is outside `NuOk`. The
  relation is monotone wherever `X` avoids `Mut` payloads; what is missing is coiteration's map at
  those positions. An argument without `X`, and `X` under `[@a]`, are §22.
- **Lifetime-indexed iteration.** An iterator over a borrowed list or buffer, whose state is a
  borrow and whose rest keeps it, is not yet written as a program (§9 iteration, `[@d] U(νX. C)`
  per `docs/scope-recursion.md` §3.5).
- **General recursion.** Non-tail recursion needs an explicit stack in the state. Sequencing
  loops is library code over `unfold` (the delay bind, §14), or one `unfold` for a whole body
  (§14, *One state machine per body*).
- Whether `D`'s greatest fixed point equals the intersection of its finite approximations is
  reduced to one property of `wpTS` (`WpChainCommutes`), not derived.
- Stream adequacy is stated generically only at `Stream 1` (`take_runs`).

From `experiments/Recursion`, `CBPVMu`; general `ν` per `docs/scope-recursion.md` §3.

---

## 8. Entry 7 — integers

### Types

    A ::= … | I32 | I64 | U8                              (VTy.int w)

`I32`/`I64`/`U8` hold no resource. They are persistent (§10), `Imm̲ 'b I32 = I32`, and they outlive
every lifetime. `U8` (`Width.w8`) is the byte: its reason is layout (an array of bytes is one byte
per element, `Backend/README.md`), and it has no arithmetic of its own.

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
| byte | `wrap8`, `extend8_u` | `I32 ⇒ U8` (the low 8 bits), `U8 ⇒ I32` |

The grouped operations are Wasm's, at `w32` and `w64`. At `w8` they exist as names and take `0`
(`hostArg`), so none is applicable, and `Host.call` has no argument shape for them: arithmetic
on bytes is done at `I32`, as in Wasm. The surface elaborates an operator at `u8` to the `i32`
operation on `extend8_u` of its operands, narrowing an arithmetic result by `wrap8`, and reads
the byte literal `b'c'` as `u8[n]` (`docs/decisions.md` 43).

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
- Checked (non-wrapping) arithmetic is derivable from the operations above.
- `plainV` excludes the integer types, so they cannot yet be `withborS` leaves.
- The backend's layout is type-directed (`Backend/README.md`, Representation): `I32` and `I64`
  are each one unboxed word.

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

### Slice borrows

An owned array is also lent directly, as a family of leaf borrows at one lifetime, with no cell
(`Core/Slices.lean`, K2 of `docs/strings-slices-design.md`):

    slice_borrow_mut : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B
    slice_borrow_imm : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B

    ArrayMut @a A ≜ [Mut @a A]

Each is a constant at a dead context whose term is `withbor`'s, `λa. λg. (a, g () a)`: the
handle `(ℓ, n)` goes to the callback and comes back, and nothing new runs. Side conditions, at
both modes: `A` and `B` each outlive a lifetime `@b` defined by `Δ` (`withbor2`'s condition on
`A`, and `withborF2`'s on its result), `'x` free in neither; at `Imm`, `A` is scoped in `Δ`.

**Soundness.** The model reads a family of places as the iterated separating conjunction of its
leaves. One Mut Frame (`[TR]` 6.65) per leaf, nested around the one callback, is an induction on
the list of places (`wpTS_M_frameList`, `Core/SliceFrames.lean`); at `Imm`, one Imm Frame
(6.64) per leaf, each adding its record, with the leaves stable along `Ext`
(`wpTS_I_frameList`). Frame `j` takes its own lifetime `α_j`, strictly below the one before;
the callback runs at a lifetime below all of them, where every leaf is a leaf of `[M 'x A]`
because leaf cells are antitone in their lifetime (6.118, 6.114). The callback's result, and at
`Imm` the payloads handed back, are reboxed at each outer frame's lifetime by 6.60
(`vC_outlives`): that is what the side conditions on `A` and `B` pay for. The side conditions
are non-strict (§23): 6.60 at `Δ ⊢ A ⊒ @b` gives every stratum below `@bδ`, and the frames are
taken at `↓@bδ` (`vC_outlivesLe`). The compatibility lemmas are `sliceBorrowM_compatX` and
`sliceBorrowI_compatX`.

**On a `mut` family** (`ArrayMut @a A`), the element operations, with the terms of their `imm`
counterparts:

| constant | type |
|---|---|
| `slice_get_mut` | `!(ArrayMut @a A ⊗ I32 ⇒ Mut @a A ⊕ 1)` — `idx`: the leaf at the index; the rest of the family is forgotten, since a `mut` leaf holds no `own` cell (`noOwn_mut`) |
| `slice_len_mut` | `!(ArrayMut @a A ⇒ ArrayMut @a A ⊗ I32)` — the family handed back beside its length |

A family `[L]` is split at a run-time index, and two adjacent ones joined, at every leaf type
(`vP_fam_split`, `vP_fam_join`); the split is exposed on borrowed families below.

**Surface.** `borrow imm a { 'x, v -> S }` and `borrow mut a { 'x, v -> S }` on an array `a`
elaborate to `slice_borrow_imm['x, top, A, B]` and `slice_borrow_mut['x, top, A, B]`, `v` at
`array_imm 'x A` and `array_mut 'x A`, and rebind `a` from the pair, as the blocks on a cell do.
The lowering is the term's: the handle is passed, and there is no cell (`corpus/slice-imm.bc`,
`corpus/slice-mut.bc`).

### Splits and writes on a borrowed family

A borrowed family is cut at a run-time index into two families at the same lifetime, and a
`mut` family is written at an index while the rest of it is kept (`Core/SliceOps.lean`, K3 and
K5 of `docs/strings-slices-design.md`). With `L` either `Imm @a A` or `Mut @a A`:

| constant | type | term |
|---|---|---|
| `slice_split_imm`, `slice_split_mut` | `!([L] ⊗ I32 ⇒ ([L] ⊗ [L]) ⊕ [L])` | `split` |
| `slice_empty_imm`, `slice_empty_mut` | `[L]` | `(0, 0)` |
| `slice_replace_mut` | `!(ArrayMut @a A ⊗ (I32 ⊗ A) ⇒ ArrayMut @a A ⊗ (A ⊕ A))` | `array_replace`'s |
| `slice_swap_mut` | `!(ArrayMut @a A ⊗ (I32 ⊗ I32) ⇒ ArrayMut @a A)` | `swapV` |

- **`split`** at `i ≤ n` answers `inj₁` of the first `i` leaves and the other `n − i`, both at the
  family's lifetime; past the length it hands the family back. It is a machine step (below), not a
  term over the host's `le_u` and `sub`: such a term would be sound only at hosts whose
  subtraction subtracts, and every theorem holds at every host (as `count`, §16). Its soundness is
  `vP_fam_split` at the step (`famSplit_compatX`, at every leaf; the two constants are its
  instances). Owned families are not split: the model allows it, but a block is freed once
  (design §5.4).
- **The empty family** has no leaves and no resource (`famEmpty_compatX`). It is a value, not a
  `!` value: a constant at a dead context is already used at will.
- **`slice_replace_mut`** opens the leaf at the index by Mut Anti-Frame (`[TR]` 6.66,
  `wpTS_M_antiFrameX`), as `withswap` opens its cell, reads and writes it, and puts it back into
  the family (`sliceReplaceM_compatX`). Past the length it hands the new element back.
- **`slice_swap_mut`** `λp. let (f, (i, j)) = p in case idx (f, i) {inj₁ c. case idx (f, j)
  {inj₁ d. (λx. (λy. store c y; store d x; f) (load d)) (load c) | inj₂ _. f} | inj₂ _. f}`
  exchanges two slots; if either index is past the length nothing changes. At `i ≠ j` the two
  leaves are opened by two nested Anti-Frames (`sepRange_pick2N`); at `i = j` the one leaf is read
  and written twice (`sliceSwapM_compatX`).

A `mut` family has a destructor (§12), so a part a program does not use is dropped.

**Surface and library.** `borrow mut a { 'x, v -> … }` lends `v : array_mut 'x A`; the constants
act on it, and `lib/slice.bc` (`include slice`) is the slice library over them and `count_fold`
(§16): `len`, `get`, `at`, `peek`, `set`, `replace`, `swap_at`, `split_at`, `split_first`,
`split_last` (and their `_mut` forms), `reverse`, `fill`, `copy_from`, `find`, `contains`,
`starts_with`, `ends_with`, `eq`, `cmp`, `sort`, `binary_search`, and the iterators `iter_imm`
and `iter_mut`, codata whose state is the rest of the view. Its functions are generic in the
element type and take the view's lifetime; a comparison is an argument (`eq_u8`, `cmp_i32`, …).

**Lending an array to one call.** `&mut a` (or `&a`) of an owned array `a : array A`, passed at
a parameter `array_mut 'a A` (or `array_imm 'a A`) of a function with the lifetime parameter
`'a`, is `slice_borrow_mut` (or `slice_borrow_imm`) around the call, at a fresh lifetime, and
`a` is rebound from the pair, as the lend of a cell is (typed elaboration §5.1): `reverse(&mut a)`,
`at(&buf, i, d)`. A view the call hands back, as its result or its result's first component, is
dropped inside the lend (its destructor, §12), so `reverse(&mut a)` is `()`; a result that holds
anything else at `'a` is rejected (`corpus/reject/lend-array-result.bc`). `for x in &mut a` lends
the array around the whole loop (§16). Pair: `corpus/sugar/lend-array.bc`.

**Lowering.** `split` is an unsigned compare and pointer and length arithmetic: `(p, i)` and
`(p + i·s, n − i)`, with no allocation. The empty family's base is the null word `0`.

### Machine

Four primitives, `Prim.tab`, `Prim.idx`, `Prim.split` and `Prim.drop`, each with one head step. With
`len(c) = c` when `c < 2³¹` and `0` otherwise (a negative length is the empty array):

    (μ, tab (c, f))       ↦ (μ ⊎ {ℓ+i ↦ () | i < n},
                              store (ℓ+0) (f 0); …; store (ℓ+n−1) (f (n−1)); (ℓ, n))
                            where n = len(c) and ℓ, …, ℓ+n−1 are fresh
    (μ, idx ((ℓ, n), i))  ↦ (μ, inj₁ (ℓ + i))   if i < n, unsigned
                          ↦ (μ, inj₂ ())        otherwise
    (μ, split ((ℓ, n), i)) ↦ (μ, inj₁ ((ℓ, i), (ℓ + i, n − i)))   if i ≤ n, unsigned
                           ↦ (μ, inj₂ (ℓ, n))                     otherwise
    (μ, drop (f, (ℓ, n))) ↦ (μ, f (free (ℓ+0)); …; f (free (ℓ+n−1)); ())

`tab` places the cells, then runs the ordinary term that fills them; `drop` is a pure step to the
ordinary term that empties and frees them. The machine stays deterministic at each host up to the
choice of fresh locations, as `alloc` is. An index out of range takes the sum's error branch; no
step is stuck on a well-typed argument.

### Relation

    𝒱⟦[L]⟧δ(v) ≜ ∃ℓ c. ⌜v = (ℓ, i32 c) ∧ c < 2³¹⌝ ⋆ ⊛_{i < c} 𝒱⟦L⟧δ(ℓ + i)

At `Array A` this is `n` owned cells, each holding a value in `𝒱⟦A⟧`; at `ArrayImm @a A`, `n`
`imm` cells at `@a`. Nothing else changes in the typed world: a block allocation is `n` of
`TW.alloc`, a drop `n` of `TW.free`.

**The length bound.** A family in the relation has `tab`'s length: `len(c) = c`
(`arrLen_of_bound`). `tab` builds only such families (`arrLen_bound`), every operation hands
back the length it was given, and a split (`vP_fam_split`) only shortens one. So a constant
whose result array has its argument's length (a map, a clone) builds exactly that many cells;
without the bound a family with `c ≥ 2³¹` would be in the relation, and `tab (c, …)` would
build the empty array beside it (`experiments/PositiveArrays`, `FamLenBound`).

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
`A` as the consumer; `ArrayImm @a A` is forgettable, by `array_forget`, and `ArrayMut @a A` by
`slice_get_mut` past every length and `forget` of the leaf it would hand out.

### Lowering

An array is one allocation of `n` slots; slot `i` is at `base + i·s`, with `s` the slot size.
`idx` is an unsigned compare of `i` with `n` and an address computation — a `getelementptr` and
an `icmp ult` in LLVM, `i32.lt_u` and `i32.mul`/`i64.add` in Wasm. `tab` allocates the block and
fills it in a loop; `drop` loops over the slots, moves each value to the consumer, and frees the
block once. The backend's type-directed layout has `s = sizeof A` (the widest contents the slot
holds) and no header, so an element's location is a cell address like any other
(`Backend/README.md`, Representation). A slot of `U8` is one byte (`load8_u`/`store8`), and an
empty array allocates nothing.

### Baseline

`fundamentalC` covers the new constants and `adequacyC` is unchanged in statement; the machine
gains four head steps, parametric in the host as before; none of them allocates but `tab`. `[L]` is one `VTy` former, and every
lemma of the typed world proved by induction on types or on positions has its `[L]` case (6.131,
6.60, the images and invariants of reborrowing), which is what makes `withload` sound at arrays.

### Library, not primitive

- **`Vec A`**, a growable array: reallocation is a new array and a move of the leaves, under
  `Mut`. Its capacity slots are `1 ⊕ A` until uninitialised leaves exist.
- **`Str`**: a byte array with the UTF-8 invariant kept by the library's constructors; string
  literals as `Imm ⊤ Str` in the data segment.
- **`u8`**: an integer width stored in bytes.

### Open

- An `imm` reborrow of a `mut` family (K2′). Reading an element through a `mut` view is
  `peek`, a replace-and-restore that needs an element to put in the slot meanwhile.
- A generic function of `lib/slice.bc` is called with its element type written
  (`reverse[u8](v)`), and one with two lifetimes (`copy_from`, `eq`, `cmp`, …) with both
  written (`(unbang eq[u8]) ['x] ['y] (…)`): the surface infers one lifetime from the argument.
- Bounds checks at a dynamic index are not eliminated statically.
- Whether `slice_borrow`'s side conditions on `A` and `B` can be dropped: they are used by the
  proof, and not known to be needed.
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

### Surface: deep copies are written

The core rule is unchanged: a persistent variable may be used any number of times. The compiled
program keeps each object owned by one word, so a variable used by two sequential parts is
copied for the earlier one (`Backend/README.md`, Memory discipline), and at a persistent type
that holds recursive data (a `μ`, also under `⊗`, `⊕`, `[@a]`, `!`) that copy allocates every
node. Such a use is written `clone(x)` at the surface; a checked program that would copy
recursive data at an unwritten use is rejected at that use (`Frontend/Elab/Copies.lean`,
decision 39). `clone(x)` elaborates to `x`. A copy at a type that copies as words (`I32`, `1 + 1`,
their products) stays implicit. The check runs on the elaborated program after the checker, so
it only rejects more programs: `checkProgram_sound` and every theorem are unchanged.

### Open

- The promotion premise `!Γ` (every live slot at `!A`) is not widened to "every live slot
  persistent".
- A persistent closure (`!(A ⇒ B)`) that captures recursive data is copied deep too; its type
  does not say what it captures, so that copy is not checked (`bcc-counts` counts it).

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

- `Input.Holds v`: `v` is a byte list `Bytes = μX. 1 ⊕ (U8 ⊗ X)`, the input not yet read.
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
| `read_byte` | `!(all 'a < top. mut 'a input => mut 'a input * (u8 + 1))` — the next byte, or `inr ()` at the end of the input |
| `write_byte` | `!(all 'a < top. mut 'a output * u8 => mut 'a output)` — one byte |
| `write_all` | `!(all 'a < top. all 'b < top. mut 'a output * array_imm 'b u8 => mut 'a output)` — every byte of the view, in order |
| `read_into` | `!(all 'a < top. all 'b < top. mut 'a input * array_mut 'b u8 => mut 'a input * (array_mut 'b u8 * i32))` — bytes of the input into the view from its start, until it is full or the input ends, and how many; fewer than its length only at the end |

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

**Why these operations.** Bytes are the unit of both streams, and end of input is the `inr ()`
of a sum. Everything else a command-line tool needs — reading a line into a buffer, writing a
string, parsing and printing numbers, hex — is a loop over `read_byte` and `write_byte`, written
as library code. `write_all` and `read_into` are such loops too, and their models are exactly
that (below); they exist for cost, one system call per view where the loop makes one per byte,
which a loop over the byte operations cannot express. A new primitive is added when a loop over
the existing ones cannot express it, or cannot at an acceptable cost.

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
`write_byte` is `withswap` consing onto it. `write_all` is a counted loop (`count_fold`, §16)
over the view's length whose step reads the byte at the index (`array_get`, `withload`) and
writes it by `write_byte`'s term; `read_into` is a counted loop over the view's length whose
step, while every step so far has read a byte, reads one by `read_byte`'s term and puts it in
the slot (`slice_replace_mut`), and counts it. Four more externs construct and read capabilities;
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
  relation at its extern's type, at `∅`: `readByte_meets`, `writeByte_meets`, `writeAll_meets`,
  `readInto_meets`, `mkInput_meets`, `mkOutput_meets`, `takeInput_meets`, `takeOutput_meets`. Each is the Fundamental Property of the
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
| `write_all`, `read_into` | proved (7) | WASI `fd_write` of the view, again after a short write; `fd_read` into the view until it is full or the input ends; interpreter-checked (2) |
| `mk_input`, `mk_output`, `take_input`, `take_output` | proved (7) | none: the model's harness, not compiled |

An extern the compiler has no implementation for is reported as assumed and not compiled.

### Lowering

The runtime allocates the three cells holding file descriptors 0, 1 and 2, runs `main`, frees
the cells `main` returns and prints the result. `read_byte` is WASI `fd_read` of one byte from
the cell's descriptor (end of input, or an error, is `inr ()`); `write_all` is `fd_write` of the
view's bytes, called again after a short write; `read_into` is `fd_read` into the view, called
again until it is full or a read answers nothing; `write_byte` is `fd_write` of one
byte. Both are unbuffered, so a prompt appears before the next read. The plain LLVM/libc
counterpart is `read(2)`/`write(2)` on the same descriptors (or `getc`/`putc` on a `FILE *`): no
WASI-only feature is part of the semantics (decision 25).

### Programs that run until their input ends

`main` may return a loop over its capabilities:

    main : F (U (Loop (Caps ⊗ A) (Caps ⊗ B)))

The runtime drives it: it observes `next` until the loop finishes with `(caps, a)`, then takes
the capabilities back and prints `a`; it never closes it. A `main` with no externs may return a
loop with no capabilities, `main : F (U (Loop A B))`, the instance `Caps = 1` written without
them: the runtime drives it the same way and prints `a` (`corpus/sugar/loop-main.bc`). Nothing in the kernel changes (no
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
| `getb` | `ref input => ref input * (u8 + 1)` | one byte, the capability handed back |
| `putb` | `ref output * u8 => ref output * 1` | one byte out |
| `put_dec` | `ref output * i32 => ref output * 1` | a number in decimal |
| `write_bytes` | `all 'b < top. ref output * array_imm 'b u8 => ref output * 1` | a byte view, in one write (`write_all`) |
| `read_bytes` | `all 'b < top. ref input * array_mut 'b u8 => ref input * (array_mut 'b u8 * i32)` | bytes into a view (`read_into`), and how many |
| `bytes` | `ref input => U (iter u8 (ref input) (ref input))` | the input as a stream of bytes, finishing, or closing early, with the capability |

Each hides the borrow: it lends the capability to one operation and hands it back. A line
reader is not provided: an observation must terminate, so a line of unbounded length is a loop
of its own; programs consume `bytes` and keep the line in their state, or read the whole input
(`read_all`, §17). Text over the streams (`write_str`, `write_string`, `write_lit`,
`read_all`) is `lib/textio.bc` (§17).

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
- **Lending a place to one call, `&mut c` (and `&c` shared).** In `x <- M; N`, one lent place
  in `M` elaborates to `r <- M[c/&mut c]; let (c, x) = r; N`: the call takes the place and hands
  it back first, as `getb`, `putb` and `put_dec` do with a capability. A terminal `return V` of
  an ambient `main` or of a loop body may lend too: it becomes such a binding before the
  capabilities are handed back. When the parameter at the lent place is a borrow `mut 'a A` (or
  `imm 'a A` for `&c`) under the function's lifetime binder, the call is wrapped in the borrow,
  `withbor2` (`withbor1`) of a cell `c : ref A`, or of a cell scoped to the call for a value
  `c : A` (`alloc`, the borrow, `free`); the borrow's result `(c, x)` rebinds `c` the same way
  (`docs/typed-elaboration.md` §5.1). The earlier spelling `&c` for an exclusive lend is
  retired: `&c` is the shared lend.
- **`for x in bytes c { M }; N`**: the form of draft 0 of the surface syntax
  (`docs/surface-cbpv.md`). It loops without bound, so it is a div construct: it may appear in
  any function, which is then div, and in `main` anywhere on its spine (§14, which withdraws the
  earlier restriction to the end of an ambient `main`). It elaborates to a loop by `unfold`
  whose state is the stream `bytes c`, the other capabilities, and the variables that `M`
  reads, each at the type inference gives it (`docs/typed-elaboration.md`).
  The loop's `next` observes the stream: an element `x` runs `M`, which rebinds the state by
  name, and the loop goes on; at the end of the stream the capability it hands back is bound to
  `c`, and the loop finishes with the capabilities and the threaded variables. Its `close`
  closes the stream and hands the capabilities back. The rest of the body, `N`, runs at the
  loop's end, in the body's one state machine (§14, §15). A `for` over data (a count, a view,
  an array) is a counted loop instead, and total (§16, *The `for` loop over data*).

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
- `for` has no early exit: a program that stops reading keeps a flag in its state, or writes its
  loop in core (`corpus/io-sections.bc`'s `line_length`).
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
   | `U(νX. C & F R)`, `R` closed with a destructor (`D A`, `Stream A`, `Iter A R₀ R`, `Aff^c A B`) | `close` (§7), then the destructor of `R` |
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
a time. For a closed program this is the totality theorem of §14: it has no infinite run.

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

## 14. Entry 13 — divergence as an effect

### Motivation

A program may loop without bound: a command-line tool reads until its input ends, a server runs
until it is stopped, and whether some loops finish at all is unknown (the Collatz iteration). §11
let only `main` loop, and only at its end. Divergence is an effect like any other: any function
may diverge if its type says so, a function whose type does not say so terminates, and running a
divergent computation is handling the effect.

### Types

A **div function** is one whose result is a loop (§7):

    A ⇒ div B   ≜   U(A ⊸ F(U(Loop B R)))          D B = Loop B 1

A call runs the function's code up to its first loop and returns the rest of the run as a loop,
which finishes with `B` or, closed early, hands back the **residual** `R`. A **total function**
is one whose result is `F B` with no loop: `U(A ⊸ F B)`. There is no new former, rule or relation
clause: `div` is a reading of `Loop` (§7), which already exists, and the function types are the
existing ones. `!(A ⇒ div B)` is the persistent form.

**The residual.** A loop closed early must release its state. What has a destructor (§12) is
dropped, and what has none, such as a capability (§11), must be handed back. The residual of a
result `B` is `K ⊗ 1`, where `K` is the tuple of the components of `B` (its right-nested `⊗`)
whose type has no destructor, in their order in `B`; it is `1` when there are none, so `div B` is
`D B` for a function that holds no such resource. The residual is read off the type, not
recognized by names. `main`'s loop `Loop (Caps ⊗ A) (Caps ⊗ 1)` (§11) is the instance.

### The delay bind

Sequencing two loops, run the first and then continue with its result, is library code
(`lib/div.bc`), typed by the existing rules:

    div_bind[A, B, R₁, R] : U(Loop A R₁) ⊗ U((A ⊸ F(U(Loop B R))) & (R₁ ⊸ F R)) ⇒ U(Loop B R)

It is `unfold` (§7) at `Loop B R` with the state "in the first loop, with the continuation" or
"in the continuation's loop":

    S = (U(Loop A R₁) ⊗ U((A ⊸ F(U(Loop B R))) & (R₁ ⊸ F R))) ⊕ U(Loop B R)

`next` in the first loop observes it: an unfinished loop is the next state; a finished one with
`a` runs the continuation's first observation on `a`, which runs the code up to the next loop
and returns it, the next state. `next` in the second loop observes it and finishes when it
does. `close` in the first loop closes it and gives its residual to the continuation's second
observation, which turns it into the whole's; `close` in the second loop closes it. The
continuation is one linear thunk with two observations, so the variables it captures are used
by whichever observation runs, and dropped (§12) by the other where they have destructors. If
either loop never finishes, neither does the whole. Nothing in the kernel changes: `div_bind` is
checked like any `def`, and `fundamentalC` and `adequacyC` cover every use. The elaboration of a
div body does not nest delay binds: the whole body is one `unfold` whose states are its loops
and calls (below, *One state machine per body*).

**The fuel handler.** `div_fuel[A, Q] : U(Loop A Q) ⊗ I32 ⇒ A ⊕ Q` observes a loop at most `n`
times and closes it if it has not finished: `driveE n` (§7) with the count a value, counted by
`count_fold` (§16), whose state is the loop or, once it has finished, its result. A count of
`2³¹` or more (a negative `i32`) observes nothing. Div code under it is total: `collatz_within` of
`corpus/io-fuel.bc` is `total`, and a loop cut off hands its capabilities back.

**Deferring a loop.** `div_defer[B, R] : U(F(U(Loop B R)) & F R) ⇒ U(Loop B R)` is the loop
that runs nothing until it is first observed. Its argument has two observations: the first runs
the code up to a loop and returns the loop, the second hands back the residual without running
anything. It is `unfold` at `Loop B R` with the state "not started, with the code" or "started,
with the loop": `next` before the start runs the code and observes its loop, `close` before the
start takes the second observation. The surface block `{ S }` of a body `S` that loops is
`div_defer` of `⟨S', abort⟩`, `S'` the body elaborated as a div body and `abort` handing back
its residual (`corpus/sugar/surface-defer.bc`). Library code over `unfold`, like `div_bind`.

**The outermost handler.** The runtime drives a `main` that returns a loop until it finishes
(§11); it never closes it. Timeouts and cooperative yielding to a scheduler (#52) are further
handlers of the same loops.

### Inference and markers

A function is div when its type says so (`A ⇒ U(Loop B R)`), or when its body **loops**: on its
spine (the tail positions of binds, `let`s, `case` arms and `for`s) it has a `for`, or it runs
a call of a div function in **direct style**: an application whose type is a loop, where the
type expected of it is not that loop, at any depth of a bound or returned value, a `case`
scrutinee or a `let`'s value. A
function written with a plain result `A ⇒ B` whose body loops is elaborated to
`A ⇒ U(Loop B R)`. Definitions are in dependency order (a recursive group is declared at its last
member, §20),
so one pass in declaration order infers this; there is no fixed point.

- `total def f : A = V` asserts that `f` does not loop: inference that finds a loop in its body
  is a compile error naming it (`corpus/reject/total-loops.bc`, `total-calls-div.bc`). This is
  how a library promises termination, and the common annotation.
- `div def f : A = V` asserts that `f` is div. It is never needed, since inference supplies it;
  it is allowed for documentation, and makes a function div that does not loop yet.
- `main` has implicit div: it is elaborated as a loop exactly when its body loops, and its
  written type is `F A` either way. A `main` that loops but uses no capability is given none:
  the runtime drives a loop with no capabilities (§11).

A function whose written type is already a loop is core and is not elaborated; so is a `main`
written at `F(U(Loop …))`. A call checked against its own loop type is the loop as a value, not
a call in direct style: an annotated binding `l : U (loop B R) <- return (f V)`, or an argument
of a parameter of that type, `div_fuel[…] (f V, n)`.

### Elaboration

All of this is elaboration in `Frontend/Sugar.lean`, on types that inference gives
(`Frontend/Elab/`, `docs/typed-elaboration.md`); the checker sees only core. In a div body of
result `B` and residual `R`:

- **Nested calls** are lifted first: a value with a call in direct style below its top has its
  applications bound before it, innermost and leftmost first, the order its evaluation runs them
  in (`corpus/sugar/div-nested.bc`).
- **The body is one state machine** (*One state machine per body*, below): `unfold` at
  `Loop B R` whose state has a summand for each `for` (its iterator, the capabilities it does not
  hold and the variables live there) and for each call of a div function in direct style (the
  callee's loop and what the rest uses). Each observation is one iteration of a loop, or one
  observation of a callee's loop; what follows a loop or a call runs, within the observation
  that ends it, up to the next state, which the observation returns (a skip), or to a terminal,
  which finishes. The call of the function runs its code up to its first state and returns the
  machine there (`corpus/sugar/for-value.core.bc`).
- **A direct-style call** `x <- return (f V); N`, `f : A' ⇒ U(Loop B' R')`, is a state holding
  `f V`'s loop: its observation observes that loop, a skip until it finishes with `a`, then binds
  `x` to `a` (with `&mut c` in `V` (§11), `(c, x)`) and runs `N`. Closed there, the machine closes
  the callee's loop and hands back the body's residual: its residual itself when `R' = R`; else
  the capabilities by name, with `c` rebound from `r = (c, ())`.
- **`for x in V { M }; N`**, `V : U(Iter A R₀ R₀')` made from a capability `c`, is the loop of
  §11 as a state, with residual `R`; the variables it holds have the types inference gives them
  (`corpus/sugar/for-untyped.bc`). At the end of the stream `c` is bound to what the iterator
  hands back and `N` runs; after `break`, the iterator is closed first. A loop in `M` is a state
  of the same machine.
- **A terminal** `T` finishes: `v : B <- T; return (inl v)`. Before the first state, when the
  function is called, it is the loop that finishes with `v` at its first observation,
  `thunkv nu_in ⟨return (inl v), close⟩`; `close` hands back the components of `v` that have no
  destructor.

The variables that hold `K` are named as a terminal `return` names them, or, in an ambient
`main`, `stdin`, `stdout` and `stderr` (`corpus/sugar/residual-alias.bc`: a residual under a
name of the program's own). `bcc desugar` prints the
elaborated program, and `corpus/sugar/div-infer.bc` pairs an unmarked div helper with its core
form written by hand; `div-annotated.bc` is the same program with `div` and `total` markers.

### One state machine per body

Every div body is **one `unfold`** (`Frontend/Sugar.lean`, `mWalk`, `mAssemble`; #109 item 8).
Its state is a sum with one summand per **resumption point**, a place where the body stops
between two observations, holding the variables live there: a loop's head (its source, and what
the loop and what follows it use), and a call of a div function in direct style (the callee's
loop, and what follows uses). Inside a loop, a state also holds the sources of the loops around
it, and what they use. The step is one code with a `case` on the state. The code between points
is the program's own, with its transitions replaced: reaching a head or a call is a **move** to its
point; the end of a loop's body moves back to its head; `break` closes the source and moves to the
code after the loop, its **join**; `return e` closes the sources of the loops it leaves and
finishes; a terminal finishes.

**Moves.** The code of each head and call, and of each join, is a `!` function of its state,
defined before the step. A move to a join calls its function. At the empty row every move to a
summand is a skip: each observation is one iteration, or one observation of a callee, as with the
delay bind, and `div_fuel` counts the same observations; the body runs its code up to its first
state when called and returns the machine there. At a row (a generator, §15) the observations
perform the row's operations; a move forward, from the step's own code or to a later point, is a
call, and a move back to a loop's head a skip, so each observation runs one turn of a loop; the
body runs nothing when called, its first state holding the parameter. A function calls only the
functions of points after it in the body, so none calls itself and every observation ends.

**The residual by name.** Each state's `close` closes what the state holds, innermost first: the
callee's loop (turning its residual into the body's: the lent capability, `()`, the body's own
residual bound by name, or capabilities of the body by their types), then the loops' sources
(binding the capability each hands back); then it returns the residual from the names. Every
other variable of the state is dropped (§12).

Every observation is then a call of known code. A body the machine does not cover (a variable of
a type that is not determined, live at a point; a callee's residual it cannot hand back) is an
error that names it. The core forms of `corpus/sugar/for-value.bc` and the generator pairs are the
elaboration as `bcc desugar` prints it.

### Higher-order functions: specialization at the callback's type

A callback's thunk type carries its effect: `U(A ⊸ F B)` is total and `U(A ⊸ F(U(Loop B R)))`
is div. A higher-order function written once must serve both, or functions are colored. It is
**specialized at the callback's computation type**: at a call `h V` of a function
`h : P ⇒ Q = thunkv fun (p : P) -> M` (or its `!` form) where `P` has a total function type
(`A ⇒ B` or `!(A ⇒ B)`) at a component whose argument's type, as inference gives it, is a div
function's (`A ⇒ U(Loop B R)`), the elaborator makes a copy of `h` with that component of `P` at
the argument's type, infers the copy's divergence (calls through the parameter are now
direct-style div calls, so the copy is div), and calls the copy (`corpus/div-hof.bc`,
`sum3__0`). The callback may be a named function, a local holding one
(`corpus/sugar/hof-local.bc`), a callback an earlier call returned (`hof-returned.bc`), or a
closure (`hof-closure.bc`): a closure `thunkv fun (x : A) -> M` passed at a callback type whose
body loops is first elaborated in place as a div function body. Only parameter types are
instantiated: a callback's effect in a stored or returned type is the one its type says. There is one copy per function and parameter type; a total
callback uses `h` as written, which stays total. The core has no type ranging over computation
types, so this is whole-program monomorphization, with no kernel change.

The mechanism is not specific to divergence: it is specialization of a function at the
computation type of a callback argument, followed by the effect's own inference on the copy.
Another control effect may reuse it by giving (§30 does, for every control effect, keyed by a
block's sites rather than a computation type):

1. its computation type for a callback, as `Loop` is div's (the result shape a call returns);
2. its inference on a body, as `loopsAt` is div's (which constructs make a body effectful);
3. its elaboration of a body and of a direct-style call, as the body's state machine is div's.

The specialization itself — finding the callback's type at a call, copying, caching by
(function, parameter type), renaming the call — is shared. What it does not yet cover is below.

### Generators

A generator is a function that performs an iteration effect (§15). Its loops are a div body's,
at the function's row: `Loop_Σ`, whose observations perform the operation (§19, *Divergence*).
A `while` or a `loop` is a loop of any div body.

### Borrow scopes over loops, per observation

A borrow block's body is the callback of `withbor`, one computation that returns before the block
ends; a loop is codata, observed one step at a time. So no borrow stays open while a loop runs:
`↭` brackets every borrow cell inside one run, and a lend that spans observations needs a model
change that is not verified (`experiments/LoopBorrow`). What works with no new rule is to **lend
again at each observation**: the owner lives in the loop's state, and each step borrows it by an
ordinary `withbor` inside that step, so the state between steps holds the owner, never a borrow.

**The library** (`lib/lend.bc`, `include lend`) has the per-observation lend as code over
`unfold`: `loop_lend_imm` and `loop_lend_mut` (a loop whose steps take `imm 'x A` or `mut 'x A`
with the state), `pull_lend_imm` and `pull_lend_mut` (a stored generator, §15), and `array_each_imm`, the
lending loop in push form: each observation lends one array entry, a view `imm 'z E` borrowed
inside the observation, to a body that runs inside it. Each takes its steps and the first state
`(owner, s)`, and hands the owner back when the codata finishes or is closed.

**The elaboration** (`Frontend/Elab/LoopLend.lean`) puts the surface's borrow scopes into that
form, before the other sugar, with no kernel or checker change:

- **A borrow block whose body loops** (`borrow imm t { 'x, b -> S }`, `borrow mut`, a family),
  where `S` has on its spine a `for` or a call of a div function in direct style, is rewritten in
  the enclosing body: each stretch of `S` that uses the borrow is a borrow block of the same place
  handing on the variables that later code reads; the body of each `for` that uses it is a borrow
  block of its own, per step; stretches that do not use it are left outside any block. The `for`
  is then on the enclosing spine and threads the place, which each step rebinds. This is
  `loop_lend_*` written inline, so each step is known code.
- **`let r = &x; S`** (or `&mut x`) is `borrow imm x { r -> S }` over the rest of the body; `x` is
  not used in `S`. A loop-invariant borrow is thus lent per observation.
- **A div function over a borrow**: a `def f : !(all 'a < b. P => Q)` whose body loops, with one
  component `imm 'a A` (or `mut 'a A`) of `P`, is elaborated to take the owner `ref A` there and
  hand it back first, `!(P' => ref A * Q)`, its body a borrow block of the owner. A call lends
  the place, `f(&t)`, as a capability is lent (§11); inside a borrow block, the block's borrow
  passed to `f` is the place lent instead.
- **A call of a function with lifetime parameters**, `f(W)` with
  `f : !(all 'a < b. all 'b < c. … P => Q)` and no lend in `W`, is `(unbang f) ['l] ['m] … W`
  with each lifetime the one `W`'s type gives its parameter in `P` (§15, *Generic functions*).

It applies when what the loop holds between steps outlives `'x`. Otherwise it reports where it
does not: an iterator that holds the borrow; a stretch before the loop that hands on something
with `'x` in its type; a div call that takes the borrow other than as its own argument; a div
function with more than one borrow at its lifetime; a name the block binds again and that is read
after it (the rewrite puts the block's bindings in the enclosing body).

**Not covered** (each needs the spanning lend, or a construct not built): a pipeline whose source
holds the borrow, `for x in map(filter(iter(xs), p), f)` inside `borrow imm v { xs -> … }`. The
source could be rewritten to hold the owner, but the owner would come back only through the
pipeline's finishing value and residual: each adapter would pass them on, the `for` would bind
the finishing value, and the residual would have to hand back an owner that has a destructor. A
`yield` inside a borrow block is rejected (§15, *Self-reference*). A div
function called with a borrow that is not lent from a place (a view, a field, a second borrow)
holds it across its loop. `|>` is not provided (§11 Open).

Programs: `corpus/axes/borrow-across-loop.bc`, `corpus/lend-mut.bc`, `lend-config.bc`,
`lend-pipeline.bc` (0 allocations, dispatched calls and copies beyond the table's own),
`lend-server.bc`, `lend-div.bc`, and the library's `lend-lib-loop.bc`, `lend-lib-gen.bc`,
`lend-lib-each.bc`; pairs `corpus/sugar/lend-block.bc`, `lend-let.bc`, `lend-div.bc`; rejects
`corpus/reject/lend-*.bc`. Every elaborated program is checked core, so `fundamentalC` and
`adequacyC` cover it.

### The totality theorem

A closed div-free program terminates on every run (`Core/Totality.lean`). For
`CDerives ∅ [] e (F A)`, at every value type `A`:

- `total_every_alloc`: under every allocator, from every allocation count, the run from the
  empty memory reaches a value;
- `total_run_prefix`: every run under an allocator is a prefix of that run;
- `total_every_run`: every run continues to a value;
- `total_no_infinite_run`: there is no infinite run. One allocator is built from the infinite
  run (`Alloc.ofRun`: at count `k`, the location the run chose at its allocation of count `k`),
  under which every prefix of it is an allocator run; `total_every_alloc` and determinism
  (`AStep1.deterministic`) then put a value on it, which cannot step.

"Div-free" is the type: a closed computation of `F A` is total, whatever it calls inside, since
a loop it holds is observed a finite number of times (by `div_fuel`, or not at all). A program
whose `main` loops is covered one prefix at a time instead (§11, `externs_loop_every_run`).

### Baseline

No `CDerives` rule, relation clause, machine step or kernel type is added. `fundamentalC`,
`adequacyC`, `fundamentalD` and `adequacyD` keep their statements, and every theorem of §§1–13 is
preserved. The runtime's obligation for a looping `main` is §11's.

### Open

- **Some loop bodies are total**: the body of a counted loop (§16) and the clause of a `for` over
  a generator (§15) are one step, and have no drain and no div call. The body of any other loop
  may loop: its states nest in the body's machine (`corpus/gen-nested.bc`). A `for` over data is a
  counted loop, total, and nests anywhere, unless its body performs an operation that resumes
  (§16, *Effectful bodies*).
- **A call lends at most one capability** with `&mut c`, and a div call whose residual differs
  from the caller's must hand back, in its residual, the capability it was lent (it is matched
  to the lent `&mut c`), or nothing.
- **Specialization** is at parameter types only; a callback stored in data or a cell keeps the
  effect its type says. A generic function is instantiated at its types first (§15, *Generic
  functions*), and its instance is specialized as any function is, so a div function may be
  generic (a `fn f[A](g: U (pull A 1 1)) -> …` that drains `g`).
- **`div_fuel` is `driveE`** by construction, not by a proved equation.
- The model interpreter (`bcc interp`) copies the remaining input on every read.

---

## 15. Entry 14 — generators

### Motivation

A producer is easiest to write in direct style: a loop that `yield`s each element, with the
consumer deciding how many to take (#18, #107, #109, #188). Here yielding is an effect like any
other (decision 54): `Yield[T]`, a library effect (`lib/yield.bc`) whose one operation,
`ctl yield(x: T)`, is affine. A generator is a function that performs it, `fn range(lo: i32, hi:
i32) -> 1 with Yield[i32]`; a `for` over a call of one handles it (push); and a call stored where
a value is expected is the generator's **stored generator**, codata that a consumer pulls. There
is no generator type former and no iterator trait: everything below is elaboration into §19's
`handle`, `perform` and §7's `ν`, so the kernel, the checker's rules and the proofs are
unchanged.

### The iteration effect

An effect is an **iteration effect** when its one operation is control, resumes, and answers
`()`: its structure, read in `Frontend/Elab/Effects.lean` (`Env.iterEff`), not its name. Nothing
in the elaborator names `Yield`. `include yield` declares

    effect Yield[T] { ctl yield(x: T) }

and a function that performs it writes its row, `with Yield[T]`, which gives `T` (§18: an effect's
type arguments are written when the function performs it directly).

### `for` over a generator: a handler site

`for x in g(e) { M }; N`, where `g`'s row has an iteration effect `E`, is a handler site of `E`
with a static name `n` of its own (§18, §19):

- **The loop's variables travel through the operation.** The variables the body reads or assigns
  (locals and capabilities, as for a `for` over data, §16), `ws`, are threaded: the copy of `g`
  for the site takes their tuple `w` first and hands it back first, a type parameter `W` of the
  copy (instantiated at the call), as an answering handler's capability is threaded (§18); in it,
  `yield(v)` is `w <- perform[n.0] (v, w)`, the operation `A ⊗ W ↠ W`. A generator that calls
  another at the same site passes `w` on to it. So the body, which must be the clause of a `!`
  handler (§19's `[handle]`), receives the variables with the element.
- **The body is the clause.** `yield((x, w), k) = M; (force k).1 ws`: it binds `x` and `ws` from
  the payload, runs `M`, and resumes with the variables at its end and at `continue`. `break e`
  and `return e` cancel the continuation, `(force k).2`, which runs the generator's finalisers
  (its owned values dropped, §19's drop glue), and leave with the variables and the exit. The
  clause runs outside the site: what the body performs goes to the sites around the `for`.
- **The loop's value** is what `g` returns, or `e` after `break e` (`let r = for …`, as §16's);
  a generator that returns `0` gives only `break`'s. A `for` over a generator has no `else`.
- **When `g`'s body does not loop**, the `for` is one handled call: total. When it loops, `g`'s
  call is its loop (below), whose observations perform the operation; the `for` is a call of a
  div function in direct style (§14) of the loop that handles each of `g`'s observations
  (`io_hwf`): its observation is `handle_with[n](hr, hc) ((nu_out l).1)`, and its close closes
  `g`'s loop under a handler of its own.
- **A body that performs a control operation, or may loop** (a `while`, a `loop`, or a `for`
  over anything but a count), is not a clause: the clause would hold the continuation across the
  operation, and an affine continuation has no destructor (its cancel performs at the site's
  row, so it cannot be drop glue), and a clause is total. The `for` then observes `g`'s stored
  generator instead (below), a loop of the enclosing body.

When the body performs nothing else, the clause resumes in tail position, and the operation is a
direct call of the clause (§19, *Lowering*): `corpus/gen-produce.bc`, `gen-fib.bc` and
`gen-pipeline.bc` allocate nothing and dispatch no call.

### A generator's body

A generator's body is a function body at a row (§18's copy for its sites). On its spine:

- **A terminal** returns, with the threaded variables first.
- **A loop** (`while c { M }`, `loop { M }`, a `for` over a stored generator or an iterator)
  makes the body a div body at the row (§14): the function returns `Loop_Σ B R = νX. F_Σ(B ⊕ U X)
  & F_Σ R` (§19, *Divergence*), one state machine whose observations perform the row's
  operations. Such a body **runs nothing when called**: its first state holds the parameter, and
  closed there it closes the stored generators and iterators it was given and hands back its
  residual. A move forward (to the loop's head from before it, or to a later point) runs in the
  same observation, and a move back to a loop's head is a skip, so each observation runs one turn
  of a loop and every observation is total. Its residual is `K`, the components of its result with
  no destructor, as a stored generator's must be (below).
- **`return e`** inside a loop returns from the generator with `e` from any depth of its loops,
  closing each loop's source on the way out; `break` leaves the innermost loop from any position
  of its body (`corpus/gen-return.bc`).
- **A call of a generator** at the same site passes on what it yields and goes on with what it
  returns: delegation is a call (`corpus/gen-from.bc`). A call of a function that loops, a
  generator included, is a call in direct style, a state holding its loop (`corpus/gen-div.bc`).

### Stored generators

A call of a generator where a value of type `U (pull A B R)` is written to be expected (an
argument at a parameter of that type, or a binding with it, `let g : U (pull A B R) = g(e)`) is
its **stored generator**:

    pull A B R ≜ νX. F((A ⊗ U X) ⊕ (B ⊕ U X)) & F R

`next` gives an element with the rest, returns `B`, or skips a turn that yielded nothing; `close`
ends it early and hands back `R`. `pull` is an abbreviation of the frontend over `ν` (§7), read in
a type only (it is not reserved), with no counterpart in `Core/`. The call is a handler site whose
clause does not resume: it answers the element with the continuation as the rest,
`thunkv nu_in ⟨(force k).1 (), (force k).2⟩`, so nothing runs until the first observation, the
next observation resumes the generator where it yielded, and `close` cancels it (`R = 1`). When
the generator's body loops, the stored generator is `unfold` over its loop or such a rest: an
observation handles one turn of the loop; a resumed rest that ends the turn runs the next turn at
once, so that a loop that yields once per turn gives an element at every observation.

A `for` over a stored generator observes it until it returns (§14's drain, div), and the
adapters (`lib/adapters.bc`) are generic generators over stored generators: `map`, `filter`,
`take`, `skip`, `enumerate`, `chain`, `flat_map`, `take_until`, `scan`, `zip`, `chunks`, `lines`,
`batch`. Each runs its source to the end and returns the source's `K`. `take`, `take_until` and
`zip` close their source, so they take one that hands back, closed, what it returns,
`U (pull A K K)`; a failing source returns an error it cannot hand back closed, and is rejected
there (`corpus/reject/take-failing.bc`). A pipeline of adapters whose functions are known
allocates nothing and dispatches no call (`corpus/gen-pipeline-adapters.bc`: 0, 0, 0;
`gen-adapters.bc`, `gen-adapters-fail.bc` at their previous counts).

### Self-reference

A generator may not hold a borrow of its own local across a `yield` (Rust's generators forbid
it, and its `async` needs `Pin` for it). A borrow block's body may perform only abortive
operations (§19: a non-abortive operation crossing a borrow is T1, #172), so a `yield` inside a
borrow block is rejected (`corpus/reject/gen-self-borrow.bc`). A stored generator that holds a
borrow of outside data cannot leave that borrow's scope, by the outlives rule of the boxed result
(`corpus/reject/gen-escape.bc`). What is allowed is to own the cell in the generator's state and
borrow it anew at each step (`corpus/gen-cell.bc`).

### Generic functions

`fn f[A, …]<'a, …>(x₁: A₁, …) -> B = S` is generic in the types `A, …`. It is a template: it is
not elaborated as written, and a call of it is a call of its instance at the types of the call,
the template with the types substituted for its parameters (`Frontend/Elab/Subst.lean`), made
and elaborated on first use and shared by later calls at the same types (whole-program
monomorphization, as Rust's generics; the instance is named `f__gN`). The body is elaborated at
the instance's types, so what it may do with an `A` (copy it with `*g`, compare it with an
operator) is decided there. An instance is ordinary code at its types, checked by the unchanged
checker, so an adapter over a pure source and one over a failing source are two instances of
one definition. A copy of a generator for a `for`'s site is a template in the type of the threaded
variables. A lifetime that a type argument mentions (the data `array_imm 'x i32` of a sized
iterator, §16) is a lifetime parameter of the instance, `all 'io_q0 < top.` outside the
template's own: the instance is shared by every use at the same types up to those lifetimes, and
each use applies it to its own (`corpus/for-adapters.bc`). Templates of one name from two modules
(`map` of `lib/adapters.bc` and of `lib/iters.bc`) are one name chosen by the arguments' types:
the first whose parameters the arguments match.

Each lifetime parameter `'a` (bounded by `top`, or `'a < @`) is an `all 'a < @.` around the
function type and a `Fun 'a < @.` around its body, outermost first (draft 0 §2.5), for a `fn`
with or without type parameters; a function at a row whose body loops keeps them around its loop
(`corpus/gen-borrowed.bc`).

At a call `f(W)`, what the call leaves out is filled (typed elaboration §2.2–§2.3), and nothing
else:

- **Type arguments** are written, `f[T, …](…)`, or read off the arguments' types by first-order
  matching of each parameter's type, with the type parameters as placeholders; what the
  arguments leave open is matched against the type expected of the result. This covers a core
  `def f[A, …]` too, whose call becomes `f[T, …]`. A closure whose parameter's type is left out,
  and an injection, are typed last, from the parameter's type with what the other arguments
  determined.
- **Lifetime arguments** are read off the argument whose type mentions each parameter, one each
  (`eq(a, b, e)` at `['x] ['y]`), or written after the type arguments, `f[T]['x](…)`. When two
  arguments give one parameter different lifetimes, it is their meet, and an argument that is a
  borrow is shortened to it with `:>`; there is no other solving.
- **`unbang`** is inserted, before the lifetimes, as for any persistent function.

A type that is not determined is an error at the call that names it. A lifetime that is not
determined is `dom`, the meet of the lifetimes in scope, or `main`'s own lifetime in `main` (§23);
with no lifetime in scope outside `main`, it is an error at the call.

### Lowering

Nothing is lowered specially: a `for`'s site and a stored generator are §19's handlers, compiled
by `Backend/Clos/Capture.lean`. Three facts of that lowering keep generators at the cost of the
state machines they replace (`corpus/counts.expected`):

- **Suspension per projection.** A call whose argument is a known injection (`(nu_out l).2`, a
  loop's close) may suspend only with the operations of that projection of its callee, through
  codes that pass their argument on (`unfold`'s). A loop's close suspends with none, so a `for`'s
  handler of its generator's close is not one of the operation's handlers, and the clause of its
  observations stays the one closed tail-resumptive clause: a direct call.
- **One code per suspension.** A code with no resumption point of its own that may tail-call
  several codes that suspend (a generator's step, calling its loops' heads) is not a wrapper: its
  calls are resumption points, so a suspended stored generator's continuation is of one code, and
  resuming it does not dispatch.
- **A finaliser frame's clauses are one code.** `ubind (λx. N, λ_. D) M`, the drop glue around an
  operation, is converted with `N` and `D` one `sel` code called on `inj₁ x` to continue and on
  `inj₂ ()` to finalise (`markUbinds`), so what both use, a generator's owned state held across a
  `yield`, is captured once and not copied (`corpus/gen-close.bc`: 4 allocations, no copy).

### Baseline

No `CDerives` rule, relation clause, machine step or kernel type is added. `fundamentalC`,
`adequacyC`, `fundamentalD` and `adequacyD` keep their statements, and every theorem of §§1–14
and §19 is preserved: every construct of this entry is elaborated into core before checking.

### Open

- **A generator that holds a capability across a `yield`.** `yield` is affine, so what is live
  across it must drop (§19's `[let]`); a capability (`ref input`, `ref output`) has no destructor
  and must be handed back, and a cancel answers `()` with no residual. So a generator over the
  input, or one that writes as it yields, is rejected by the checker
  (`corpus/pending/gen-digits.bc`, `gen-lines.bc`, `gen-lazy.bc`, `gen-adapters-io.bc`). It needs
  a cancel that hands back a residual, or a `linear ctl` iteration effect (no `break`).
- **Callbacks that yield** to a `for`'s site: a block is passed and called (§30), but the site
  threads the loop's variables through the operation, which a block would be passed and hand back
  at each call (`corpus/pending/yield-callback.bc`). Adapters as handlers over a computation
  (`|>` at a computation parameter) need functions over computations (#161).
- **A total consumer of a generator that loops.** A `for` over one is div: its turns are
  unbounded. A finite source written as data, or a sized iterator (§16), is total, and so is a
  generator whose body does not loop.
- **Stored generators over a row.** A stored generator's observations are pure: a generator that
  performs another effect besides its iteration effect (a `Fail`) is not stored.
- **The source interpreter** (`bcc interp`, `Support`'s substitution machine) substitutes into
  the whole step at each observation, so its time per observation grows with the size of the
  body's machine.

---

## 16. Entry 15 — counted loops

### Motivation

Every total loop over a count or a view needs a loop whose bound is known when it starts. The
only total loops were folds over data, so a counted loop folded over the unary count
`μX. 1 ⊕ X` (`div_nat`, #95), and a loop of `n` steps allocated `n` objects. A counted loop
is K0 of `docs/strings-slices-design.md`.

### The constant

    count_fold : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S)        (CDerives.countFold S)

`count_fold (f, (n, (i, s)))` runs `f` at `i, i + 1, …, len(n) − 1`, threading the state, and
answers the last state; `s` itself when `i ≥ len(n)`. `len(n)` is `tab`'s (§9): `n` when
`n < 2³¹`, else `0`, so a negative bound is the empty loop. The step is persistent: what it
changes is the state, which may hold anything (an array, a capability).

### Machine

One primitive, `Prim.count`, with one head step that allocates nothing:

    (μ, count (f, (n, (i, s)))) ↦ (μ, count (f, (n, (i + 1, f (i, s)))))   if i < len(n)
                                ↦ (μ, s)                                   otherwise

(`countNext`, `Support/Dynamics/Arrays.lean`). The comparison and the increment are the
machine's, on `UInt32`, not host operations.

**Why a step, and not a Z-combinator loop over the host's `add` and `lt_u`.** Every theorem
holds at every host (§8), and `wpTS` asks that every run reach a value. A loop that counts with
the host's operations terminates only at hosts whose operations count: at the host whose
`add32` answers its first argument and whose `lt_u32` answers true, the loop from `0` steps
back to itself and never ends, so no such term is in the relation at every host. The machine's
own counter is what makes the loop total at every host. This is the one change the design's K0
did not foresee: it adds a machine step, as §9's `tab`, `idx` and `drop` did.

### Semantics

`countLoop_wp` is the induction on `len(n) − i`: one `count` step, then `f (i, s)` by the
step's validity (`bang_app`), then the loop from `i + 1`. `countFold_compatX` is the constant,
at every host (`Core/CountFold.lean`). The step is deterministic and allocates nothing, so
determinism (`head_det`), allocator runs (§13) and the totality theorem (§14) take it with no
new argument.

### Lowering

A generated loop of tail calls per step and state type (`count_loop`, `Backend/Flat/Lower.lean`):
compare, call the step on a copy of the closure, tail-call with `i + 1`. It allocates nothing
(`corpus/count-fold.bc`: allocs 0).

### The loop with an exit (K0′)

    count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)     (CDerives.countTry S E)

`count_try (f, (n, (i, s)))` is `count_fold` whose step may stop the loop: it answers `inl` of
the next state, and the loop goes on, or `inr e`, and the loop answers `inr e` at once. At the
bound it answers `inl` of the last state (`inl s` when `i ≥ len(n)`). It sits beside
`count_fold`, which stays: a loop that never stops early has no exit to test.

One primitive, `Prim.countTry`, with one head step that allocates nothing:

    (μ, count_try (f, (n, (i, s))))
      ↦ (μ, case f (i, s) { inl s′ → count_try (f, (n, (i + 1, s′))) | inr e → inr e })   if i < len(n)
      ↦ (μ, inl s)                                                                      otherwise

(`countTryNext`, `Support/Dynamics/Arrays.lean`; the branches bind the step's answer, so `f` is
shifted past the binder). It is a step for the reason `count` is (*Why a step*, above): the
counter is the machine's, so the loop is total at every host.

**Semantics.** `countTryLoop_wp` is `countLoop_wp`'s induction on `len(n) − i` with one more
case: after `f (i, s)`, an `inl s′` continues by the induction hypothesis at `i + 1`
(`countTry_cont_subst` undoes the shift), and an `inr e` is a value of `𝒱⟦S ⊕ E⟧`.
`countTry_compatX` is the constant, at every host (`Core/CountFold.lean`); its axioms are
`[propext, Classical.choice, Quot.sound]`. The step is deterministic and allocates nothing, so
`head_det`, allocator runs (§13) and the totality theorem (§14) take it with no new argument.

**Checker and lowering.** The checker reads `count_try[S, E]`. The backend lowers it to a
generated loop of tail calls per step and state type (`count_try_loop`): compare, call the step
on a copy of the closure, test the answer's tag, tail-call with `i + 1` on `inl`, return on
`inr`. It allocates nothing (`corpus/count-try.bc`: allocs 0).

### The `for` loop over data

`for x in y { M }` is Rust's desugaring: `y` is turned into an iterator by its **type** (Rust's
`IntoIterator`), and the loop calls its `next` at each step, with `break`, `continue` and
`return`. It is pull. A source whose type holds the data it came from is **sized**: the loop is
`count_try` over the length of that data, computed when the loop starts, calling `next` at each
step, and it is total (`forData`, `Frontend/Sugar.lean`; all of it elaboration into core):

| source, by type | the bound | the element at step `i` |
|---|---|---|
| a count `a..b` (syntax; `i32`s) | `b − a` | `a + i` |
| a view `array_imm @a A` | its length, `array_len` | the leaf `i`, by `idx` (`array_get`) |
| a view `array_mut @a A` | its length, `slice_len_mut` | the first leaf of the rest, by `split` at `1` |
| `&a`, `&mut a` of `a : array A` | as the view `slice_borrow_imm`/`_mut` lends around the loop (§9) | as the view's |
| an owned array `array A`, `A` persistent | as `&a` | the leaf's content, copied; the array is dropped after the loop |
| a sized iterator `sized D S A` (below) | `len(D)` | what its step answers |

No bound is a number the program gives: it is the length of the data the source's type holds, so
nothing truncates a loop. A call of a generator is a handler site (§15), total when the
generator's body does not loop. Any other source (a stored generator, an iterator, the input) is
a **drain**, the loop of §14, and div. `total` rejects a function that drains, or whose `for` is
over a generator that loops (`corpus/reject/for-free-bound.bc`: `take(g, 10)` of a stored
generator `g` is a generator that loops).

**The step and its exits.** The loop's state is the source's cursor and the variables the body
reads or assigns (a capability the body uses included: an effect of the body is the function's,
and the loop hands the capability back). The step answers `inl` of the next state at the end of
the body and at `continue`; `break e` and `return e` answer `inr` of the threaded variables and
the way out. After the loop the threaded variables are rebound and the loop's value is `e`, or
the `else` value when the source ended. `return e` in the body of a loop of a surface `fn` (or
`main ->`) returns from the function from any depth of its loops: each counted loop leaves by its
exit, and the loop around it by its own (`DivSt.exits`); the loop is first moved onto the
function's spine (`normExits`). A core `def`'s `return V` is the core's.

**The loop's value.** Over a source that can end, `for … { … break v … } else { d }` has the value
`v`, or `d` when the source ends (Zig's `else`, provisional); `break v` without `else` is rejected
there. A source that cannot end, a generator that returns `0` (whose body ends in a
`loop { … }`, a `while` that never fails), has no `else`: its loop's value is `break`'s alone, and
with no `break` its type is `0` and nothing after it runs. A `for` with no value is `()`. A drain
keeps its value, what the source finishes with or `break e`, and takes `else` too; a `for` over a
call of a generator keeps what the generator returns, or `break e`, and has no `else`.

**Reports.** `bcc check` reports each loop: `total, bounded by len(…)`, or `div: its source … is
unbounded (a drain)`, and code after a loop that never ends as `unreachable`. There is no syntax
at the loop for either.

**Sized iterators** (`lib/iters.bc`, `include iters`) are the data's iterators as values that
adapters compose:

    sized D S A  ≜  D ⊗ (S ⊗ !(D ⊗ S ⇒ (D ⊗ S) ⊗ (A ⊕ (1 ⊕ 1))))          (VTy.sized, frontend only)

the data `D` it came from (a view, a count `I32 ⊗ I32`, or a pair of data), its own state `S`,
and its step, which answers the next data and state with an element, a skip (`inr (inl ())`) or
the end (`inr (inr ())`). `len(D)` is a view's length, a count's `b − a`, and a pair's sum
(at most `2³¹ − 1`). `elems`, `elems_mut` (the elements of a view), `copied`, `map`, `filter`,
`take`, `enumerate` and `zip`; `a..b` as a value is the count's. Each step takes at most one
element of the data, so `len(D)` steps see every element: `map` and `enumerate` keep the bound,
`filter` answers at most one element per element, `take(k)` ends after `k`, and `zip` pulls one
side, then the other (holding the first's element when the second skips), so its data is the
pair and its bound the sum, and its elements are at most the shorter side's. An adapter that
takes a stored generator is a generator (`lib/adapters.bc`, §15), and adapters of one name are
chosen by the argument's type. The abbreviation is the frontend's, like `pull` (§15): no former,
rule or relation clause.

**Completeness** (`Support/Dynamics/Completeness.lean`, on the step relation). The relation
proves the loop total; that it sees every element is a fact about the steps:

- `countTry_runs`: when the step answers `inl` at each index, `count_try (f, (n, (i, s)))` runs
  it at `i, i + 1, …, len(n) − 1`, in order, once each, and answers `inl` of the last state;
  `countTry_exit`: its first `inr` is the answer;
- `arrLen_eq_of_lt`: a family of the relation has `len(n) = n` (§9's length bound);
- `idxAns_lt`, `idxAns_ge`, `idxAns_count`: `idx` answers the leaf `ℓ + i` exactly at the
  `n` indices `i < n`;
- `splitFirst_lt`, `splitFirst_end`: the rest after `i` steps is `(ℓ + i, n − i)`; its split
  answers the leaf `ℓ + i` while `i < n`, and the end exactly at `n`.

So the bound equals the number of elements: every element is visited and none is dropped. Their
axioms are within `[propext, Classical.choice, Quot.sound]`.

**Borrowing.** A counted loop is one computation, so a borrow block around it keeps its borrow for
the whole loop (§9's lend of `&a`/`&mut a` is such a block); the per-observation lend (§14)
applies to drains only (`LoopLend`, whose test of a loop reads the source's type in the block's
context).

**Effectful bodies.** A counted loop's step is one total computation, so it cannot hold the
continuation of a control operation that resumes. When the body's row has one (`opsC` finds a
`perform` of a non-abortive operation of the row, the rule keyed on the row, no effect named),
the `for` is a **div loop** over the source's cursor instead: a `while`, a loop of the body's
machine (§14, §15), one turn per element (`forDataDiv`, `Frontend/Sugar.lean`). This holds when the
operation is of a site that observes its computation one turn at a time, a `for`'s site or a
stored generator's (§15); at any other site the loop is total at the row, `bounded_fix` over the
count, which a handler wraps (§30, *Counted loops at a resuming row*, proposed):

| source | the loop |
|---|---|
| a count `a..b` | the index from `a`, the element the index |
| a view `array_imm @a A` | the index, the leaf by `array_get` |
| a view `array_mut @a A` | the rest of the view, split at `1` each turn |
| an owned array `array A`, `A` persistent | the index, the element copied out under a borrow of one turn |
| a sized iterator | its data and state, one step each turn |
| `&a`, `&mut a` | rejected: the lend spans the loop, and an operation that resumes cannot cross a borrow (T1, #172) |

The loop has no value there (`break e`, `else`). `corpus/for-data-div.bc` runs each source that
a program can reach; `corpus/reject/for-lend-resumes.bc` is the lend. A `mut` view reaches such a
body only through a borrow block (§9), which a resuming operation cannot cross, so its row is not
exercised.

**Programs.** `corpus/for-finite.bc` (a `total fn` over a count), `iter-mut.bc` (`&mut a`),
`for-data.bc` (an owned array, `&a`, a view; `break`, `break`'s value and `else`, `continue`,
`stdout` in the body), `for-return.bc`, `for-never.bc`, `for-adapters.bc` (a total chain, no
allocation), `io-for-after.bc` (a drain of the input's lines, code after it). Every loop over data
in the corpus allocates nothing (`corpus/counts.expected`).

### Uses

- `div_fuel` (§14) counts its observations with `count_fold`, in place of the unary count:
  `io-fuel` went from 3746 allocations and 174 dispatched calls to 1 and 0.
- A counted loop over an array's indices, each index lent as a `mut` leaf
  (`corpus/iter-mut-count.bc`).
- The `for` loop over data, above.

### Baseline

`fundamentalC`, `adequacyC`, `adequacyD` and the totality theorem keep their statements; the
machine gains two head steps (`count`, `countTry`), parametric in the host as before. Everything
the `for` loop adds is elaboration into core, checked by the checker, which gains the constant
`count_try`. The erasure of `absurd V` is `case V {inj₁ x. x | inj₂ y. y}` (it was
`case V {inj₁ _. () | inj₂ _. ()}`): no arm runs either way (`zeroE_compatC`), and the new arms give
the backend's layout inference no type of their own.

### Open

- `for` over `μ` data (lists): a borrowed list in order is open (§7 Open; #57), and an owned list's
  rest is a cursor but its drain to the end has no count.
- A `for` over data whose body performs a resuming operation (a `yield`) or loops (a drain, a div
  call, or a `for` over a generator that loops) is rejected: the step of `count_try` is total
  (`corpus/reject/for-data-gen-loop.bc`). A generator over a view pulls it with
  `iter_imm`/`iter_mut` (§9), a drain.
- `zip`'s bound is the sum of its sides' lengths, at most `2³¹ − 1`: a zip of views whose lengths
  add up to more would be cut there. Arrays of the backend are far smaller.
- The imm leaf a view lends is not copied implicitly: a body that reads an element twice binds
  it first, `let v = *x`.
- Push stages (`docs/iteration-design.md` §7.2) and the boundary adapters are not provided.

## 17. Entry 16 — buffers, text and literals

### Motivation

Strings stage S5 of `docs/strings-slices-design.md`: a growable buffer, text over byte views, and
literals, as library code over §9's arrays and families, §16's counted loop and §11's externs.
Nothing in the kernel changes: no constant, rule, former or machine step. What is new is
library code, surface forms that elaborate into core terms, and a lowering of literals.

### Buffers (stage A)

    buf A ≜ Array A ⊗ I32                          (surface `buf A`, `array A * i32`)

The array's length is the capacity and the `I32` the length; the slots at or past the length
hold a **filler**, chosen by the element type (`filler[A]`, elaboration): `0` at an integer, the
empty family at a borrowed family (`slice_empty_*`), an empty array at an owned one (which
allocates nothing), `!(λ_. filler)` at a `!` function, and componentwise at `⊗` and `⊕`. A type
with no filler (a cell, a capability) is not buffered. `lib/buf.bc` (`include buf`): `buf_new`,
`push`, `pop`, `take`, `reserve`, `truncate`, `clear`, `len_of`, `cap_of`, `grow`,
`buf_of_array`, `array_tab`. `push` on a full buffer grows it to twice its capacity (at least
8): a new array of fillers (`tab`), each element moved by `array_replace`, and the old array
dropped with the fillers left in it. Every operation is `tab`, `array_replace`, `array_size`,
`count` and `drop`, so buffers are sound under every allocator by §9 and §13 with nothing new.

**No view across growth.** A view of a buffer exists only inside a borrow block (below), whose
callback does not hold the buffer: a function that grows a buffer takes it and hands it back,
and cannot be given it while a view of it is live. This is linearity, with no new check.

### Text

    string ≜ buf U8      text 'a ≜ [Imm 'a U8]      text_mut 'a ≜ [Mut 'a U8]
    lit ≜ I32 ⊗ !(I32 ⇒ U8)

Text is UTF-8. The types are abbreviations of the byte types, so the invariant is kept by the
library, not enforced by typing (stage T2, with opaque types, #63): text is made from bytes only
by validation (`str_from_utf8`, in place `from_utf8`) or by appends that write whole characters
(`push_char`, `push_str`, `push_lit`), and an in-place change keeps it (`make_ascii_uppercase`).
Every function is safe on any bytes: indexing is checked, and a byte that does not start a valid
sequence decodes to U+FFFD. `lib/text.bc` (`include text`, which includes `buf` and `slice`)
has appends, UTF-8 validation and decoding, character iteration (`chars`, codata over the rest
of the view), lines as sub-views (`next_line`, `lines`, `fold_lines`: no allocation per line),
`split_once`, `trim`, `find_str`, `eq_lit`, checked parsing (`parse_i32`, which raises its error,
§18), and buffers of views (`view_at`, `sort_views`). Every loop is a
`count_fold` bounded by a length, so the library is total. `lib/textio.bc` (`include textio`)
writes and reads text over the standard streams: `write_str`, `write_string` and `write_lit` in
one `write_all`, and `read_all`, which reads the input in chunks into the string's spare
capacity (`read_into`) and runs until the input ends (a div function, §14).

### Literals

A string literal `"…"` is the persistent value `(n, t)` of `lit`: `n` its length in bytes and `t`
a `!` function with no captures from an index to its byte (`0` past the end). The elaborator
writes `t` as a compare of the index with the length, then a search on the index down to one
byte (`Frontend.Sugar.litValue`): an ordinary core term, typed by the checker. A literal holds no
resource, so it is copied and dropped freely, and an array or a buffer holds literals with no
lifetime. `'c'` is a character, the `i32` scalar value.

**Literal views.** `borrow imm "…" { v -> S }` (or on a `lit` variable) lends the literal's bytes
as a `text 'x`: the elaboration tabulates them into an array (`tab`), lends it (`slice_borrow_imm`)
to a callback that first copies the family (`array_copy`), and drops the array after. It is a
scoped lend, like any view (design §5.7, Q4); a literal view cannot be stored past its block.

### Surface

Each is elaborated before checking into core terms the unchanged checker checks.

- The type abbreviations above, read by the parser in type positions only.
- `box buf[A](cap)`, `box string(cap)`, `box array(n, f)`: `buf_new[A](cap)`, `string_new(cap)`,
  `array_tab(n, f)`.
- `borrow imm b { v -> S }` and `borrow mut b { v -> S }` on a buffer lend its initialised
  prefix: its array lent as a family (`slice_borrow_*`, §9) and cut at the length
  (`slice_split_*`); the buffer is handed back. The side conditions' bound is `⊓Δ`, so a
  buffer's elements may be views.
- **A borrow block hands back** the enclosing `let mut` variables it assigns, the places it lends
  that it does not bind, and the standard capabilities it uses, beside its result, as `for`
  does (§11): `borrow imm line { v -> write_str(&mut stdout, v) }` leaves `stdout` in scope.
- A template (§15) is instantiated at a type with lifetimes, a buffer of views: the instance
  takes a lifetime parameter of its own for each, outermost, and a call passes the call's.
- A lend `&x` at a generic function's parameter of `x`'s own type moves `x` and rebinds it, with
  any number of lifetime parameters.

### Lowering

- **Literals in read-only data.** A literal's `t` (the shape above) becomes a closure of one
  shared code over the address and length of its bytes (`Backend/Clos/Convert.lean`,
  `litTable?`, `litClosure`), whose body is a load (`litByte`). The bytes are emitted once, as a
  Wasm data segment from `16384`, before the heap. Every literal is one code, so a call of one is
  direct.
- **Literal views point into the data.** The erased shape of a literal view — the array lent by
  `withbor`'s term to a callback that first copies the family, then dropped — is recognised
  (`litView?`), and its `tab` is `litTab`: when the tabulator is the literal code's closure and
  the length at most the literal's, the array is `(address, n)` in the data and nothing is
  allocated; otherwise it is `tab`. Copying the family is typable only at an `imm` family, so no
  write reaches the array; `$free` skips addresses below the heap.
- **Buffers** are `(ptr, cap, len)`: an array's two words and the length. Growth allocates the
  new block, moves the elements one by one and frees the old block.

That the lowering of literals is the model's run up to locations is a lowering claim, tested on
the corpus (design §5.7, §11 Assurance), not proved.

### Programs

The design's P1–P9, P11 and P13 run at every stage (`corpus/fields.bc`, `parse-int.bc`,
`trim-replace.bc`, `format.bc`, `utf8-count.bc`, `key-value.bc`, `sort-lines.bc`,
`json-tokens.bc`, `http-request.bc`, `ascii-upper.bc`, `labels-json.bc`), with their counts in
`corpus/counts.expected`. Each is written with what exists: `count_fold` where the design writes
a total `for` (S4), sums where it writes `data` (S6), borrow blocks where it writes a lend of a
buffer at a view parameter (the design's §4.3 row, S4).

### Baseline

No change to `CDerives`, the relation, the machine or the checker's rules; §11 gains two externs
whose models are proved to meet their contracts. `fundamentalC`, `adequacyC`, `adequacyD` and the
end-to-end I/O theorems keep their statements.

### Open

- **A `mut` view of a buffer of views inside the views' block.** `slice_borrow_mut`'s side
  condition asks the element type to outlive a lifetime of the context; for `buf (text 't)` at
  `'t` there is none strictly below `'t` (an `imm` borrow at `'t` outlives only lifetimes below
  `'t`), so `borrow mut` of such a buffer is rejected (`cannot show that array_imm 't u8 outlives
  …`). `sort_views` works on the owned buffer instead. Whether the side condition is needed is
  §9's open question.
- The sugar's type inference types a call of a function with lifetime parameters whose body
  lends a place (`push_lit(&mut r, …)`) as `1`; `corpus/http-request.bc` writes that function
  with the appends' results bound instead.
- The design's lend row (§4.3: `&s` of a string at a `text` parameter), the total `for` over a
  view's iterator, and `*e` of a copyable view are S4's; `data` values and `data` with lifetime
  parameters are S6's; the typed text types (T2) and zero-cost growth (a `buf` former, F) are
  later stages.
- `write_lossy`, `char_indices`, `split_at_str`, `sub_str`, `push_hex` and `parse_i64` of the
  design's list are not provided.
- P14 (`args`) waits for the `Args` capability (§11, designed, not built).
- The literal lowering's claim is tested, not proved.

---

## 18. Entry 17 — effects and handlers

### Motivation

The surface of effects (#18, #152–#154, #188): declarations, handlers, `with` and rows. Answering
effects are capabilities, by elaboration into core terms the checker already derives (decision
48): a capability is a value lent by `withbor`, an answering operation is a call on it. Control
effects, errors among them, are the kernel's (§19): each `with` of a control handler is a
`handle` with a static name, and an operation is a `perform` or an `abort` at that name. Effect
safety is `fundamentalC` and `adequacyC` on the elaborated program. What the elaboration can still
get wrong is what a handler means, so the answering clauses have laws about the runs of the terms
they emit (*Laws*, below), and the cost of each is measured against the program written by hand
(*Programs*).

### Declarations

    effect E[T, …] { fn op(x₁: A₁, …) -> B; ctl op(…) -> B; linear ctl …; multi ctl …; … }
    handler h(mut s: S): E = { op(x₁, …) = e; … }                                   (answering)
    handler h[T, …](p: A, …): E[A, …], A -> R with E₂[…] = { return(x) = M; op(x, …, k) = N; … }
    with h[A, …](e, …) { M }          with h(&mut c) { M }
    fn f(…) -> T with E₁, E₂[A] = …                                       (a written row)

An **effect** declares its operations, each **answering** (`fn`, Koka's `fun`) or **control**
(`ctl`, with the structural qualifier of §19: affine by default, `linear ctl`, `multi ctl` for
unrestricted). An effect is one kind or the other. A control operation whose answer is `never`
(the type `0`) at a qualifier with weakening is **abortive** (§19). An abortive operation is
affine: `multi ctl op(…) -> never` is rejected, and so is an unrestricted operation answering `0`
in a row of the core text (decision 63's restriction, 2026-10-12; §27 *Typing*). An effect may
take type parameters (a control effect only).

A **handler** is a value implementing an effect. An answering handler has a state, its `mut`
parameter, a `let mut` variable in each clause, which the clause may assign; the clause's value is
the operation's answer. A control handler names the type `A` of the body it handles and its
answer `R`; its return clause receives the body's value, and an operation's clause receives the
operation's arguments and, unless the operation is abortive, its continuation `k`, which `k(v)`
resumes. Its clauses are `!` code (§19's `[handle]`); what they use besides is passed to them
(§21): the clauses of a handler whose operations are all abortive run after it, and a handler
whose operations resume has a state, its parameters that are not `!` and the capabilities its
clauses use. `with E₂[…]` lists what its clauses perform, served around the `with`.

`with h(…) { M }` runs `M` with `h` handling its effect. An operation is called like a function,
`op(v)`: there is no `perform` token (decision 49). An operation's name is its own: no function may
share it. A **written row** after a function's result type is a promise that its inferred row is
within it, checked, and gives the type arguments of an effect the function performs directly.
All spellings are provisional (decisions 51, 55).

**Errors** are the library effect `Fail[E]` (`lib/fail.bc`), `ctl raise(e: E) -> never`, handled
by ordinary handlers: `to_result` (`inl` the value or `inr` the error), `default(d)` (the value,
or `d`, an owned value) and `map_err(f)` (the error `f(e)` raised to the handler around the
`with`). Nothing in the elaborator knows them.

**Iteration** is the library effect `Yield[T]` (`lib/yield.bc`), `ctl yield(x: T)`: a function that
performs it is a generator, a `for` over a call of one handles it, and a call where a stored
generator is expected stores it (§15). The elaborator knows it only as an iteration effect, by its
structure: one control operation that resumes and answers `()`.

### Elaboration

All of it is in `Frontend/Elab/Effects.lean` (resolution, before the rest of the sugar) and
`Frontend/Sugar.lean` (assembly, where types are known); the checker sees only core.

**Answering effects** are capabilities. With the capability `c : Mut 'l S`:

| form | elaborates to |
|---|---|
| a clause `op(x) = M` of `h` | `fn h__op<'l>(c: mut 'l S, x: A) -> mut 'l S * B = let r = modify c { s -> M; (s, r) }; (c, r)`: `!` code run on the lent state by `withswap`, the `FnMut` row of §2 |
| `with h(e) { M }` | `borrow mut (alloc(e)) { 'l, c -> M' }`: a `withbor` of the state's cell whose callback's parameter is the capability; the cell is dropped after |
| `with h(&mut c₀) { M }` | `borrow mut c₀ { 'l, c -> M' }`, and `c₀` is rebound |
| `op(v)` in `M` | `let (c, r) = h__op(c, v)`, `h` the innermost handler of `E` |

The capability is threaded as a `let mut` variable is: bound again after each call, handed out of
each arm of a `match` or `if` that uses it, out of a borrow block, and through a `for`'s body.

**Control effects** are §19's. Each `with` of a control handler is a **handler site** with a
static name `n` of its own, and an operation is resolved lexically to the innermost site of its
effect: `perform[n.i](v)`, or `abort[n.i](v)` for an abortive operation. The site is
`handle_with[n](hr, hc) M`: the return clause and the operation clauses as `!` closures, at the
types `[handle]` gives them, the handler's type parameters matched against the body's type and its
arguments' types. The clauses run outside the site: their operations go to the sites around the
`with`.

**Rows.** A function's **row** is the set of effect instances it performs: those of the operations
it calls and of the functions it calls, less those a `with` inside it handles. It is inferred in
declaration order. A function with a row is elaborated once per assignment of its effects to what
serves them in scope (the handlers of its answering effects, the sites of its control effects), as
a generic function is once per instance (decision 45): the copy `f__…` takes the capabilities
first and hands them back first, and its type has the sites' operations as its row,
`A ⇒ F[n.i …] B`. A call of `f` is a call of that copy, a computation of its own:
`g <- return f; a <- return v; (force g) a`. A function with a row that is never called is not
elaborated. Resolution is lexical: an operation goes to the innermost handler of its effect around
it, or to what the enclosing function's copy was given.

The checker checks a copy, as any `def`, at each of its uses, so a program holding a closed
function at its uses is §24's `[let-poly]` read by substitution: the program's derivation gives the
rule's derivation of the let that binds the function once (`checkProgram_letPoly`, §24
*Theorems*). The copies for two assignments of names are two functions, each performing at its own
names.

**Where an abortive operation may stand.**
- *In a counted loop's body* (`for` over data, §16): `count_try`'s step is pure, so the step
  handles the operations of the names its body performs itself, each leaving the loop by its exit,
  and after the loop the operation is performed again at the same name. A body with a control
  operation that resumes makes the loop a div loop instead (§16, *Effectful bodies*).
- *In a borrow block's body*: the block is the unwinding form of its borrow (§19), at the
  operations its body performs, which must be abortive (a resuming one is T1, #172); its callback
  is ascribed its row. An unwind ends the lend, and the lender's finaliser runs.
- *With answering capabilities in use*: the body of a control `with` is given a reborrow of each
  capability it uses (`withbor3`), so that the capability comes back when the body is abandoned.

**Drop glue** is the checker's (§19): a binding whose head may abort, at a row with weakening,
puts the destructors of the slots the rest uses in a `[then]` finaliser. A value with no
destructor (§12, class 3) live across such a binding is rejected, naming it.

**Not provided**, each rejected with a message that says so: an operation inside a closure or
block that is not run in place, other than a block passed at a parameter of function type (§30),
and a function with a row passed as a value (effectful callbacks, #161; for a fold's algebra that
raises, K4 below); a lend `&mut x` in the arguments of a call that
threads a capability; an operation of an answering effect inside a clause of an answering handler;
a function with a row whose written result is a computation (a loop); a second instance of
an effect in a row; type parameters on an answering effect; an effect with both kinds of operation;
an unrestricted operation that answers `never` (`multi ctl`, above); a `let mut` declared outside
a control `with` and assigned in it, or a place lent in it; abortive operations of two sites in
one counted loop's body; a borrow of a buffer or a literal crossed by an abort.

### Reports

`bcc check` prints, after the declarations' types, what the elaboration did (#126), in four kinds,
each in source order; the library's own are not printed:

| line | says |
|---|---|
| `effect L:C: E: op, …` | an effect and its operations, with their kind and qualifier |
| `row L:C: f: E, Fail[X]` | a function's inferred row, with the instances' type arguments |
| `lowering L:C: …` | each handler: an answering handler is a **call** (`fun`); a control `with` is a handler site with its static name, each operation abortive (a branch per call, `final ctl`), linear, affine or unrestricted; each copy made for a handler or site |
| `call L:C: …` | per call site (decision 49): which clause or copy an operation or an effectful call calls, and each control operation's name and site |

`corpus/reports/*.txt` pin the reports of the effect programs, and the gate compares them
(`scripts/check-corpus.sh`).

### Laws

`Core/Handlers.lean`, on the terms the elaboration emits for answering handlers, at every host:

- **Tail-resumptive** (`op_tail`, `op_answer`). An operation call on the capability `ℓ` is
  `withswap ℓ (λs. g (s, v))`, `g` the clause's code. In any evaluation context `K` (the rest of
  the handled body), at a memory whose cell `ℓ` holds `s`, the call reduces with no change to
  memory to the clause run on `(s, v)`; and when that run answers `(s', r)`, the call reaches
  `K[(ℓ, r)]` with `s'` in the cell.
- **Handling is the fold of the clauses** (`handle_fold`): the handler is the state-passing fold
  of its clauses over the operations performed.

The file's abort laws (`abort_passes`, `return_resumes`, `loop_abort`) are about the sum schema
that errors elaborated to before §19; errors are now §19's abortive operations, whose meaning is
the kernel's (`handle_compatC`, `then_compatC`, adequacy).

### Programs

`corpus/effects-map.bc` declares a `Map` effect with two handlers, an association buffer and an
array indexed by the key, and runs one client, `census`, under each, from one source, and once
with its state lent from a cell. `corpus/effects-map-hand.bc` is the same program written by hand
in capability-passing style; both run to the same value, and their counts are equal (11
allocations, no dispatched call, no copy). `corpus/sugar/effects-counter.bc` pairs a handled
counter with its core form written by hand.

`corpus/effects-fold.bc` is target 2 of #18: a fold over fallible elements, written with `raise`
and `map_err`, no `try_fold` and no sum threaded by hand, run under `to_result` and under
`default` from one source; a buffer built halfway is dropped when the abort unwinds.
`corpus/effects-fold-sum.bc` is the same program with the sums written by hand: the same value, and
the same counts (7 allocations, no dispatched call, no copy). `corpus/effects-map-fail.bc` combines
`Map` and `Fail`: the capability is reborrowed for the body of `to_result`, and the handler's state
is used after the abort. `corpus/effects-log-fail.bc` runs a function that logs and raises with
`Log` outside `Fail` (the logs kept) and inside it (the log's cell freed by the unwind), and
`corpus/effects-borrow-raise.bc` raises inside `borrow mut c { … }` with the handler outside: §19's
acceptance programs 1 and 3 at the surface.

**The library** raises: `add_checked` and `mul_checked` (`Fail[1]`), `parse_i32`
(`Fail[ParseError]`, over a counted `for`, the checked operations' overflow raised as its own by
`map_err`), `str_from_utf8` and `from_utf8` (`Fail[i32]`, the index of the first bad byte;
`from_utf8`'s buffer is dropped on the error, since an error holds nothing owned; provisionally:
the error should hand the buffer back once an abortive payload may be linear, #215).
`corpus/parse-int.bc`, `ascii-upper.bc`, `sort-lines.bc`, `key-value.bc`, `trim-replace.bc` and
`utf8-count.bc` handle them with `to_result`; their counts are unchanged. A search that finds
nothing still answers a sum.

`corpus/effects-generic.bc` runs a generic function with a row: copied for its handler, then
instantiated at each type (decision 45).

Rejects: `corpus/reject/effect-*.bc`.

### Baseline

No change to `CDerives`, the relation, the machine or the checker's rules: control effects are
§19's, checked by the certifying checker's §19 builders. `fundamentalC`, `adequacyC`,
`fundamentalD` and `adequacyD` keep their statements and cover every elaborated program. The
copies are `[let-poly]`'s premise term (§24): the checker does not emit the rule, and a checked
program's derivation gives it (`checkProgram_letPoly`).

### Open

- Named instances and lexical resolution between two instances of an effect (S2, #155); bundles
  (#156).
- Effectful callbacks stored (#161), and with them functions over computations (`retry`, a
  handler that re-runs its body, and `|>` at a computation parameter). Blocks passed and called
  are §30: E1 (a higher-order function under two handlers) and E6 (a wrapper whose handler the
  callback's raise passes) run from source (`corpus/effects-hof-two-rows.bc`,
  `corpus/effects-tunnel.bc`). E2d (a consumer of generators at two rows) passes a named function
  with a row as a value, and waits (§24 *Open*).
- An operation that answers a borrow into the handler's state (#160); `lookup` answers a copy.
- A handler parameter that is not `!` is the handler's state (§21); its native lowering (§19
  *Open*).
- **K4: an early exit from a kernel fold.** A `raise` in the algebra of `fold_own`/`fold_imm` needs
  the fold to stop (`corpus/pending/raise-in-fold.bc`).
- An error that holds an owned value: §19's `[raise]` asks its argument to drop.
- A control `with` that hands back the `let mut` variables its body assigns or the places it
  lends.
- A capability threaded through a `for` over `&a` of an owned array: the lend around the loop
  takes `top` as its bound, so the loop's state cannot hold a borrow (`corpus/effects-map.bc`
  passes a view instead).

---

## 19. Entry 18 — native capture: `handle` and `perform`

### Motivation

§18 defines handlers by elaboration. That covers answering operations (a call on a capability)
and S1b's aborts, but not a handler that captures the rest of the computation (#186). The
spikes #184 and #185 (`experiments/HandlersAsBorrows`, `experiments/HandlersControl`) found
three things:

- **State behind control needs capture.** Without capture it can be written only with explicit
  requests, at a bounded depth (`no_uniform_comp`).
- **The reentry rule is admissible.** It is the linearity of the state token
  (`not_borrowSpansForward`).
- **A continuation's contraction is its capture's persistence.** A continuation may be copied only if
  what it captures is persistent (`lam_bang_persistent`).

This entry adds handlers, control operations, unwinding and one effectful returner type to the
kernel. Several effects run at once, each handled by its own handler, and a handler passes the
rest outward. A handler can unwind any continuation it holds.

**Acceptance.** Six everyday programs, each typed and safe in the kernel (*Programs*):

1. **Two effects at once.** A function that logs and can fail, run under a `Log` handler nested
   with a `Fail` handler, in both nesting orders, with each order's observable result. `Fail` is
   an ordinary effect: `raise` is an abortive operation.
2. **Logging inside a borrow.** `borrow mut buf { … log(x) … }`, with the `Log` handler outside
   the borrow.
3. **Raising inside a borrow.** `borrow mut buf { … raise(e) … }`, with the `Fail` handler
   outside the borrow: the lend ends, the buffer goes back to its owner, and the handler receives
   the error.
4. **An infinite loop that logs.**
5. **Early exit.** `take(n)` stops a producer that holds a resource, and the resource is
   finalised.
6. **Cancelling a suspended computation.** A stored continuation is unwound, and what it holds
   is finalised.

Beyond those: the reconciler chain `timeout |> retry |> log |> kube`, and the #184/#185
examples (shared stateful capability, `memo`, multi-shot, resume-later).

### Kinds of operation, and the structural qualifier of a continuation

An effect declares each operation as **answering** or **control**, as Koka's `fun` and `ctl`
do (decision 48's cost vocabulary). A control operation also declares a **structural qualifier**
on its continuation `κ`. The qualifier comes from the substructural lattice (Tov and Pucella's
λURAL; Tang et al.'s related work; *Affect*'s affine continuations), and answers two independent
questions:

- **weakening:** may `κ` be discarded?
- **contraction:** may `κ` be duplicated?

| qualifier | weakening | contraction | `κ` is | the handler … |
|---|---|---|---|---|
| **linear** | no | no | `U((B ⊸ F_Σ R) & ⊤)` | resumes exactly once: a must-complete computation |
| **affine** | yes | no | `U((B ⊸ F_Σ R) & F_Σ 1)` | resumes at most once, or cancels |
| **relevant** | no | yes | — | *Open* (below) |
| **unrestricted** | yes | yes | `!U((B ⊸ F_Σ R) & F_Σ 1)` | resumes any number of times, or cancels; its captures are persistent (`lam_bang_persistent`) |

**Weakening has computational content: the continuation's destructor.**

- To discard `κ` is to **unwind** it: its frames finalise innermost first, and each lend in it
  ends, as §12 derives a record's destructor from its fields', frame by frame.
- `(B ⊸ F_Σ R) & F_Σ 1` is the textbook encoding of an affine type as `A & 1`. The `1` branch,
  `cancel`, is the destructor. The additive `&` makes the two branches share the one captured
  context.
- A linear `κ` has no `1` branch, so it must be resumed.

**`raise` is an operation whose handler exercises weakening.** There is no separate mode.

- `Fail[E]` is `raise : E ↠ 0` at an affine or unrestricted qualifier; a program's is affine
  (§18).
- Its answer type is `0`, so the resume branch can never be taken, and the handler can only
  cancel.
- An operation with answer type `0` at a qualifier with weakening is **abortive**, and the machine
  exercises the weakening eagerly, in place ([unwind]/[finalise], below). The clause receives only
  the argument, and `κ` is never reified.

  That is what lets an abortive operation cross a borrow's scope: the borrow's callback returns
  by its unwind path and the lend ends, with nothing kept alive across it. It is not T1.

**Which operations cross a borrow's scope:**

| operation | crosses a borrow's scope |
|---|---|
| answering | yes: it is a call |
| abortive (answer type `0`, weakening qualifier) | yes: unwinding ends each lend it passes, LIFO (*Theorems*) |
| any other control operation | no: its `κ` is reified, and a stored `κ` would hold a lend across a suspension (T1, #172) |

**The relevant cell is Open.** A relevant continuation may be copied but must be used.

- Contraction needs persistent captures, as for unrestricted. A persistent `κ` holds `∅`, so
  discarding it is semantically free, and "relevant" is a typing discipline with no semantic
  content.
- It needs a modality with `copy` and no `forget`. The kernel's `!` has both, and there is no
  other.
- So it costs a new value-type former and its rules, for no new program. It stays Open until a
  target needs it.

- **An answering operation** is a call of the handler's clause on the handler's state. The
  handler's **capability** is a value: the clause, as `!` code, beside the state, threaded as a
  `Mut` borrow (§18, #184), shared as an `Imm` view, or absent (a stateless, persistent `!`
  provider). Nothing in this entry assumes that a provider of answering operations is a lexical
  handler with linear state. A call is typed by §3's rules. So
  `borrow mut buf { … log(x) … }` with the handler outside is the callback capturing the outer
  `log` capability, an outer borrow that outlives the callback's lifetime. This is acceptance (2),
  and it needs no new rule and no new proof.
- **An abortive operation** is how an error is raised. `Fail[E]` is an ordinary effect,
  `raise : E ↠ 0` (affine), handled by ordinary handlers: `to_result`, `default`, `retry`,
  `map_err`.
  There is no sum for failure and no special case (#168). Unwinding closes scopes innermost
  first, which is BoLo's nesting order:
  - when an unwind passes a borrow, that borrow's callback returns, by its unwind path;
  - the lend ends, and the lender regains the place;
  - the frame's finaliser (§12's destructors) runs, and the unwind continues outward.

  Nothing is kept alive across a lend: this is not T1, which needs a continuation held while a
  borrow is out. The obligation is stated under *Theorems*.
- **Any other control operation** captures the rest of the computation up to its handler as a
  continuation `κ`, which the clause may resume now, later, or several times. It may
  **not** cross a borrow's scope, since a stored `κ` would hold a lend across a suspension. That
  is T1 (#172), and it stays behind T1.
- **Any affine or unrestricted continuation a handler holds can be unwound instead of resumed.**
  `κ` has two entries, `resume w` and `cancel ()`. Cancelling runs `κ`'s frames' finalisers innermost first, ends every
  lend inside `κ`, and answers `()`, or re-raises at the canceller an error a finaliser raised
  (*Cancels*, below). This covers every cancellation:
  - a timeout cancelling its body;
  - a scheduler cancelling a parked task;
  - `take(n)` closing a producer early;
  - `break` out of a loop, and `return` from inside a fold;
  - `requeue` abandoning a reconcile attempt;
  - shutdown.

  An affine `κ` is consumed by exactly one of its two entries. So "a continuation cannot be
  dropped" (#185, `forget_not_lolli`) is answered by the destructor `cancel`, not by a `forget`:
  in Core, `forget κ` has no derivation at `1` (`not_forget_kappa`, *Laws* item 4).
  A strictly linear `κ` has no `cancel`, for must-complete computations.

### Names: which handler handles an operation

A control operation names its handler: `perform_n v` is handled by the nearest enclosing
`handle_n`. A name `n` is **static**: each `handle` site of the program has its own name, given
by elaboration, and `perform_n` is resolved lexically to the site whose capability is in scope.
Rows `Σ` are finite sets of names, each with its operations' types. So:

- **Distinct instances are distinguished lexically, as in Effekt's System Ξ.** Two `Kube`
  handlers are two sites, two names, and two row entries; an operation reaches the one whose
  name it carries, whatever handlers lie between. A higher-order function that handles its own
  instance of an effect cannot capture its callback's operations (no accidental handling).
  **Named instances fall out.**
- **Re-entry of one site** (`memo` running itself under itself) meets the nearest enclosing
  instance of that name, as Koka's dynamic handlers do. That instance has the same operation
  types, so this is sound. Operation types are closed in lifetimes, so every instance of a site
  has one protocol, and a typed program gives each operation one signature (decision R,
  *Typing*).

**Why not generative names (Ξ's runtime labels).**

- A generative label must never meet a stale copy of itself. The heap is leak-free (§13, every
  run from empty memory to empty memory), so a label cell is freed when its handler ends.
- A continuation that escapes its handler can then be resumed after the label is reused, inside
  a handler that took the reused label. An operation on the old capability would then reach the
  wrong handler, with the wrong types.
- Preventing this needs a continuation confined to its handler's scope: a scope-indexed thunk
  with no elimination to plain `U`. The box `[@c] U C` is not enough, since `[]E` removes it. That
  is a T2 (#173) former the kernel does not have.
- Static names need neither the label nor the confinement.

I have not built this scenario in Lean. It is the reason for the choice, not a claimed
obstruction; generative labels are *Open*, behind T2.

**Why not operation names with dynamic forwarding alone (Koka, Links, Tang et al.).** Resolution
by operation name makes two instances of one effect indistinguishable without a mask or lift,
and it gives accidental handling across a higher-order function. Static per-site names keep
forwarding (an operation passes every handler of another name) and add lexical instance
resolution.

### Terms and machine

Six primitives (`ccatch` and `cfin`, below), and no new `Expr` constructor:

    perform_n V          ≜  perform (n, V)                  (`.app (.prim .perform) …`)   non-abortive
    raise_n V            ≜  raise (n, V)                    (`.app (.prim .raise) …`)     abortive
    handle_n e with H    ≜  hnd (n, (qs, H)) e              (`.app (.app (.prim .hnd) …) e`)
    M then x. N unwind D ≜  ubind (λx. N, λ_. D) M          (`.app (.app (.prim .ubind) …) M`)

`ubind` is `M to x. N` with a finaliser `D`, which runs instead of `N` when `M` unwinds.

`H = (h_ret, h_op)` is a pair of values, `n` a literal, and `qs` the tags of the operations'
qualifiers (§25), which `[handle]` writes. Evaluation is argument-first, so `e` runs under the frame
`hnd (n, (qs, H)) [·]`; below, `hnd (n, H)` abbreviates it. A context `K` is **free of `n`** (`Kont.NoHnd n K`) when
none of its frames is `hnd (n, H′) [·]`. It may hold handlers of other names. A context is
**unwind-clear** (`Kont.NoUbind K`) when none of its frames is `ubind _ [·]`. The head steps
below and the cancel steps (*Cancels*) do not allocate:

    (μ, hnd (n, H) v)                  ↦  (μ, h_ret v)                                     [ret]
    (μ, hnd (n, H) K[perform (n, v)])  ↦  (μ, h_op (v, κ))     K free of n, where          [op]
          κ = λy. hnd (n, H) K[y]                          (at a linear or affine operation, §25)
    (μ, hnd (n, H) K[raise (n, v)])    ↦  (μ, h_op v)          K free of n, unwind-clear   [unwind]
    (μ, ubind (N, D) v)                ↦  (μ, N v)                                         [then]
    (μ, ubind (N, D) K[raise (m, v)])  ↦  (μ, D (); raise (m, v))   K unwind-clear, m ≠ ⊥  [finalise]

- **The continuation.** The `[op]` step's `κ` is the pair of its entries:

      κ = ⟨ λy. hnd (n, H) K[y] ,  λ_. ccatch (K†[raise (⊥, none)]) ⟩

  - `⊥` is a reserved name that no program uses.
  - `K†` is the **cancelled region** `K` with its handler frames and its `ccatch` frames removed
    (`Kont.dead`): the region is dead, and a dead frame catches nothing (*Cancels*). Its other
    frames stay, finaliser frames among them.
  - `ccatch e` is a delimiter that catches only `⊥`.
  - So cancelling runs the region with an unwind. The unwind runs `K`'s finalisers and the
    unwinding forms of the borrows in `K`, and stops at `ccatch` (*Cancels*).
- **Unwinding runs innermost first.** A `raise` goes to the nearest `ubind` (its finaliser runs,
  then it raises again from there) or to its handler, whichever is nearer (`unwind_prefix`,
  *Laws*).
- **Other handlers' frames are transparent to it.** They are dropped, which is sound because
  their clauses are `!`, at `∅`.
- **Capture passes `ubind` frames**, which `κ` keeps.

- **The handler is deep**, and `κ` reinstalls it together with every other handler frame in `K`.
  That is the forwarding: an operation of name `m ≠ n` inside `hnd (n, H)` is not a redex there,
  and it is handled further out with `hnd (n, H)` inside its continuation.
- **`K[perform (n, v)]` is final**, with `K` free of `n`: not a value, and not reducible until an
  enclosing `hnd (n, _)` reduces it.
- **Substitution.** `Kont.shift` makes `κ y` substitute back to `hnd (n, H) K[y]`.
- **Unique decomposition** holds: no redex holds another redex at an evaluation position
  (`head_nested`), and a redex that holds a non-value holds it at a catcher position
  (`head_plug`). The `[op]` redex holds `perform (n, v)`, which is not a redex, under frames free
  of `n`. §13's determinism gains the capture cases (`head_det_eff`); `[cfin-raise]` and
  `[cfin-cancel]` are told apart by the raise's name.

### Cancels

A cancel is not interceptable. The cancelled region `K` is torn down: nothing in it resumes, and
**its handler frames are dead**. Deadness is a property of frames, not names: `κ`'s cancel branch
runs the region with its handler frames and its cancel delimiters removed (`K†`), so a dead frame
catches nothing, neither a raise nor an operation, and a finaliser's effects reach the nearest
*live* instance of their name, outside the region. A cancel is `raise (⊥, err)` with a **cancel
state** `err`, the error kept so far (`none` at the start). No handler is named `⊥`, so no live
handler catches the cancel itself. At a finaliser the cancel runs `D ()` under a sixth primitive,
`cfin err`:

    (μ, ubind (N, D) K[raise (⊥, err)])  ↦  (μ, cfin err (D ()))         K catching nothing of ⊥   [finalise-cancel]
    (μ, cfin err v)                       ↦  (μ, raise (⊥, err))                                     [cfin-ret]
    (μ, cfin err K[raise (m, v)])         ↦  (μ, raise (⊥, err ∨ (m, v)))  m ≠ ⊥, K catching nothing of m   [cfin-raise]
    (μ, cfin err K[raise (⊥, err′)])      ↦  (μ, raise (⊥, err ∨ err′))    K catching nothing of ⊥   [cfin-cancel]
    (μ, ccatch K[raise (⊥, none)])        ↦  (μ, ())                       K catching nothing of ⊥   [cancel]
    (μ, ccatch K[raise (⊥, E)])           ↦  (μ, raise E)                  K catching nothing of ⊥   [cancel-raise]

where `err ∨ e` is `err` when `err ≠ none`, and `e` otherwise: the first error wins.

- **An error raised by a finaliser during a cancel is re-raised at the canceller**, after every
  frame of the region has finalised, and meets the nearest live instance of its name there, as
  any raise does. The canceller's outcome is "cancelled" (`()`), or "cancelled, and cleanup
  failed with `E`" (an ordinary `raise E` at the canceller's point).
- **No error is dropped because of its name.** A name whose site the region re-enters, a dead
  instance inside the region and a live one outside it, reaches the live one (`progRe`,
  `progOut`). A name handled only inside the region has no live handler at the canceller: its
  re-raise is an operation no handler receives, and a typing of finalisers rejects such a
  finaliser (decision D3 of 2026-10-08; `prog`, below).
- **Several failures:** the first is kept and re-raised, a policy; the later ones lose to it. Every
  run of a cancel follows this (`cancel_prefix`, *Laws*).
- **A finaliser's operation** passes the dead region and the cancel's delimiter, and the nearest
  live handler of its name catches it. Its continuation holds the running finaliser's `cfin`, the
  region's remaining frames and the canceller's context. Resumed, the finaliser and then the
  cancel go on (`progFinOp`).
- **A cancel nested in a cancel.** When that handler cancels the finaliser's continuation, the new
  cancel's region holds the running finaliser's `cfin` and the first cancel's `ccatch`. The
  `ccatch` is dead, and the new cancel passes the `cfin` by `[cfin-cancel]`, which keeps the
  earlier error, the first cancel's. The first region's remaining finalisers run under the new
  cancel, which ends at its own `ccatch` (`progNC₁`).
- **An unrestricted continuation dropped.** When the finaliser's continuation is unrestricted and
  its handler discards it, the kept error and the region's remaining finalisers go with it
  (`progDrop`; resumed instead, the error reaches its live handler, `progKeep`). This is the case
  of any discarded unrestricted continuation, which never runs its region's finalisers: `unr` is
  tolerated, never designed for.
- Ordinary unwinding (a `raise` of a name other than `⊥`) is unchanged: a finaliser's raise
  supersedes the pending one and is caught by the live handlers around the finaliser.
- `Core/EffCancel.lean` machine-checks each outcome, as runs (`Steps` of `Head` steps) and by the
  interpreter (`eval`):

  | program | the region and its finalisers | answer |
  |---|---|---|
  | `prog` | a dead `2`; the finaliser raises `2` | `raise (2, (0, ()))`, which no handler catches: no step (`prog_final`) |
  | `prog₃` | a dead `2`; the finaliser raises `3`, handled outside | `inj₂ ()` |
  | `progOut` | `prog` under a live `2` | `inj₂ ()` |
  | `progRe` | `f ()` re-enters the site `3`; the finaliser raises `3`; a live `3` outside | `inj₂ ()` |
  | `progFinOp` | a dead `4`; the finaliser performs `4`; a live `4` outside resumes it | `inj₁ ()` |
  | `progNC₁` | as `progFinOp`, the live `4` cancelling the finaliser's continuation | `()` |
  | `progDrop` | a finaliser raises `2` (kept); a later one performs `4`, whose `unr` clause drops its continuation | `inj₁ ()`; the live `2` never runs |
  | `progKeep` | as `progDrop`, the clause resuming | `inj₂ ()`: the kept `2` reaches the live `2` |

**Why this rule.** Deadness is decided where the region is known: `[op]` builds `κ` from `K`, and
removing the dead frames there makes every cancel rule local. No rule reads a name, and a dead
frame cannot catch because it is not there. A dead frame and no frame cannot be told apart: a dead
frame's body never becomes a value, since the only `⊥` raise inside the region is the region's own
cancel, which nothing in it catches, and `cfin` always yields a `⊥` raise. So the removal needs no
primitive, and `HasHnd` and `Catches` are unchanged. The `ccatch` frames in `K` are delimiters of
cancels in progress (`K` was captured inside a running finaliser): they belong to the dead region,
and removing them lets the outer cancel reach its own `ccatch`, which is what non-interceptability
asks. The `cfin` frames stay: a `cfin` holds a kept error, which `[cfin-cancel]` merges into the
passing cancel's state. The cancel state rides in the `raise`'s payload, so a cancel is an ordinary
abortive unwind for every other frame; `ubind`'s two finalise rules and `cfin`'s two catching rules
split on the payload's name, so unique decomposition and determinism extend case by case.

### Types

    C ::= … | F_Σ A            Σ = {n₁ : E₁, …, n_k : E_k},   E = {op_i : A_i ↠^{q_i} B_i}_i,   q ∈ {lin, aff, unr}

- **`F_Σ A`** (`CTy.eff Σ A`) is a computation of `A` that may perform the control operations of
  the names in `Σ`. `F A = F_∅ A` stays the pure returner, with its own constructor.
- **Row weakening:** `F_Σ A ≤ F_Σ′ A` for `Σ ⊆ Σ′`.
- **Operation types are closed in lifetimes.**
- **The other functions over `CTy`** treat `F_Σ A` like `F A` on its value types.
- **`U(F_Σ A)`** has no outlives rule and is not persistent.
- **`F_Σ A` is an observation-tree leaf** (`cB`, §7), so a `ν` computation may observe to an
  effectful step (*Divergence*, below).

### Typing

Six rules, over `CDerives` with its context premises (§10):

    Δ; Γ ⊢ M : F_Σ A        Σ ⊆ Σ′
    ──────────────────────────── [sub]          (F A = F_∅ A)
    Δ; Γ ⊢ M : F_Σ′ A

    Δ; Γ ⊢ V : A_i        n : E ∈ Σ,   op_i : A_i ↠^{q} B_i ∈ E,   op_i not abortive
    ──────────────────────────────────────────── [perform]
    Δ; Γ ⊢ perform_{n,i} V : F_Σ B_i

    Δ; Γ ⊢ V : A_i        n : E ∈ Σ,   op_i : A_i ↠^{q} 0 ∈ E,   q ∈ {aff, unr}
    ──────────────────────────────────────────── [raise]
    Δ; Γ ⊢ raise_{n,i} V : F_Σ B          (any B: an abortive operation, whose answer 0 is absurd)

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_Σ A    Δ; x : A, Γ₂ ⊢ N : F_Σ B    Δ; Γ₂ ⊢ D : F 1
    ──────────────────────────────────────────────────────────── [then]   (§27: D at its own row)
    Δ; Γ ⊢ M then x. N unwind D : F_Σ B

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_Σ A    Δ; x : A, Γ₂ ⊢ N : F_Σ B
    (Σ has an unrestricted operation ⇒ !Γ₂)
    (Σ has an abortive or affine operation ⇒ Γ₂ drops: NoOwn, or use [then])
    ──────────────────────────────────────────────────────────────────────── [let]
    Δ; Γ ⊢ (λx. N) M : F_Σ B

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ H : !U(A ⊸ F_Σ R) ⊗ ⊗_i !U(A_i ⊗ K_i ⊸ F_Σ R)    Δ; Γ₂ ⊢ e : F_{Σ, n : E} A
    ──────────────────────────────────────────────────────────────────────── [handle]
    Δ; Γ ⊢ hnd (n, H) e : F_Σ R          (n ∉ Σ)

    K_i = U((B_i ⊸ F_Σ R) & ⊤) (lin),   U((B_i ⊸ F_Σ R) & F_Σ 1) (aff),   !U((B_i ⊸ F_Σ R) & F_Σ 1) (unr)
    an abortive operation's clause is !U(A_i ⊸ F_Σ R): the machine has cancelled κ
    (§27: the cancel branch is at F_{F_i ⊕ Σ} 1, F_i the operation's cancel row)

- **As built** (`Core/Fundamental.lean`, `CDerives.eff*`; `Core/EffRules.lean`):
  - a row is a list of operations `(n, i, q, A_i, B_i)`, and `F_Σ R` is `CTy.effOf Σ R`;
  - `[sub]` is `RowLe` (every operation of `Σ` is `Σ′`'s);
  - `[raise]`'s argument type drops (`VTy.Drop`);
  - `[then]` asks `Σ`'s names to be nonzero and its keys unique, and `!Γ₂` at an unrestricted
    row;
  - `[handle]` takes `H` a value form over a part of the context whose live slots are
    persistent, the clause of the `j`-th operation at index `j` (`Row.ofEff`, `clausesTy`), and
    `n ≠ 0` (`CDerives.effHandleV`, §24); `h_ret` and the clauses as two variables is its
    instance (`CDerives.effHandle`).
- **The linear `κ`** is the same `&` pair as the others, its cancel branch at `⊤`, so the clause
  can only resume it. The machine builds `κ` by the operation's qualifier (§25): at `lin` and `aff`
  it owns a cell, and a linear `κ`'s cancel branch has no step.
- **One signature per operation** (decision R). An *effect context* `Ξ` gives each name its
  signature, `(Ξ n)[i] = (q, A_i, B_i)`. A row is tied to `Ξ` when every operation it finds is of a
  nonzero name at `Ξ`'s signature (`RowAt`). `CDerivesAt Ξ` is `CDerives` with `RowAt Ξ` at the
  three rules that read an operation's signature off a row: `[perform]` and `[raise]` (their row)
  and `[handle]` (the handled row `Σ, n : E`). Every other rule is `CDerives`'s, `[sub]`, `[let]`,
  `[then]` and the cancel rows among them (`Core/Tied.lean`).
  - A tied derivation is a `CDerives` derivation (`CDerivesAt.toCDerives`), and a derivation of a
    term with no `perform`, `raise` or `hnd` is tied at every effect context
    (`CDerivesAt.ofEffFree`).
  - At a handler the tie makes `E` a prefix of `Ξ n` (`sig_prefix_of_rowAt`), so the handler
    value's tags are a prefix of `Ξ`'s qualifiers of `n` (`hndTags_of_rowAt`).
  - **The checker** builds every derivation tied (`Frontend/Check/Tied.lean`). `main`'s derivation
    is `CDerivesAt Ξ` at every effect context at which the rows it reads at those three rules are
    (`checkProgram_tied`), and at the program's effect context, the one those rows give
    (`checkProgram_tiedAt`). A program whose rows give one operation two signatures is rejected.
    For an elaborated program those are its effect declarations' signatures at its handler sites:
    the elaborator writes each row and each handler's clauses from the declarations (§18).
  - **Abortive operations are affine** (§18). The kernel's `[raise]` admits an unrestricted
    abortive operation; the checker rejects one, so the effect context of a checked program has
    none (`EffCtx.NoUnrExn`, `checkProgram_tiedAt`). In a row tied to such a context an
    unrestricted operation resumes (`abort_false_of_rowAt`).
  - **The names a run raises** (`Core/RaiseNames.lean`). `[raise]` finds its operation in a row
    tied to `Ξ`, and no rule types a `cfin`, so a tied term is at `Ξ`'s names
    (`raiseOK_of_derivesAt`): each raise in it is of a name `Ξ` declares, or a cancel whose kept
    error is, and each `cfin` holds such a cancel state (`Expr.RaiseOK`, at `EffCtx.Names`). No
    step breaks this, nor stores a value that breaks it (`raiseOK_step1`), so every configuration a
    run reaches from the empty memory is at `Ξ`'s names (`raiseOK_reach`). So the errors cancels
    keep are of names of `Ξ`: at every cancel of `κ` a run reaches, each running finaliser's `cfin`
    frame of the cancelled region keeps none or a raise of a name of `Ξ` (`CancelsNamed`,
    `cancelsNamed_of_derivesAt`).

- **Rows.** `[handle]` removes its name and passes the rest outward. Its clauses and its answer
  are at `Σ`, so a clause may perform the outer handlers' operations. That is how two handlers
  nest.
- **The [let] side condition is Tang et al.'s `T-Seq`, read at the row.** At an unrestricted qualifier, the
  continuation of an operation in `M` holds `N`'s context.
- **The clauses are `!`**, as their `T-Handler` requires of a deep handler.
- **Every other rule is §3's at any computation type**, and holds at `F_Σ A` unchanged:
  - `case`, `let (x, y)`, `;`, `λ` and application (an effectful function is `A ⊸ F_Σ B`);
  - `&`, `∀`, and thunks of λ-values (a block `!U(A ⊸ F_Σ B)`).
- **Unwinding contexts.** `[then]` is `[let]` with a finaliser. `D` runs in the same `Γ₂` as `N`,
  additively, and disposes it (§12's destructors).
- **A finaliser's effects** (§27, decisions D2 and D3 of 2026-10-08): `D` is at its own row
  `Σ_D ≤ Σ`, and each operation of `M` whose continuation may be cancelled records `D`'s effects in
  its cancel row. The machine sends a finaliser's raises and operations to the nearest live handler
  (*Cancels*), and `[sub]` at the cancel's use asks them to have a live instance there. A plain
  `[let]` at a row with an abortive or affine operation needs `Γ₂` to drop with nothing owned
  (borrows, `!`, data), since a cancel or an unwind abandons it.
- **Drop glue** is a surface obligation: the elaborator inserts a `[then]` finaliser for every
  owned local in scope at a possible weakening point, as Rust inserts drop glue. So the side
  condition "the abandoned context drops with nothing owned" is met automatically. The kernel
  checks it; the elaborator establishes it.
- **Borrows.** Each borrow constant (`withbor` 1–3, `withload`, the slice borrows) keeps its
  pure form, and gains an **unwinding form** at a callback `F_Σ(['x] B)` whose row has only
  abortive operations. The unwinding form's term is the pure one's with `ubind`: when the callback
  unwinds, the lend ends, the source goes back to the lender, and the lender's finaliser runs:
  - `forget` for a `Mut`/`Imm` source;
  - the destructor for an owned `Ref A`, at `HasDtor A` (§12).

  Then the unwind continues outward. Non-abortive control operations stay inside a borrow's scope: every
  borrow callback's row is unwind-only.

  **As built** (`Core/EffBorrow.lean`, `CDerives.withbor1U` … `sliceBorrowIU`):
  - the unwinding constant is `U(src ⊸ U(∀'x ⊏ ⊓Δ. L ⊸ F_Σ(['x] B)) ⊸ F_Σ R)`, with the pure
    form's source `src`, lend `L` and result `R`;
  - its term is `withborU d = λr. λf. (f [] r) then b. (r, b) unwind d r`, with a closed finaliser
    `d : src ⊸ F 1` typed by a premise. The elaborator passes the source's destructor `dtorE src`
    (§12), which is `forget` at `Mut`/`Imm`;
  - `withload`'s source is consumed by its load, so nothing goes back to the lender: its unwinding
    form is `withload`'s own term at the effectful type;
  - the callback's row is `Row.Unwind 'x`: every operation abortive and of a nonzero name, and its
    argument type closed data, free of `'x` and outliving every lifetime;
  - `withswap` is not a borrow: its callback takes the payload by value, and an unwind would
    abandon it. It has no unwinding form.

### Semantics

- **Final configurations.** `wpG ls e Q` is `wpTS` with the run ending at a final term `t` (a
  value, or `K[perform (n, v)]` with `K` free of `n`), and the postcondition `Q ls′ t` over it.
  Every other conjunct is `wpTS`'s verbatim, and `wpTS ls e Q = wpG ls e (λ ls′ t. ∃ v, t = v ∧ Q ls′ v)`.
- **Protocols.** A protocol table maps a name and an operation to a protocol,
  `Π : Nm → ℕ → List SRec → Val → (List SRec → Val → WProp) → WProp`. The table of `Σ` at `δ`:

      Π_Σ n i ls v Φ  ≜  𝒱⟦A_i⟧(ls)δ(v) ⋆ (λρ_k. (q_i = unr → ρ_k = ∅) ∧
                            ∀ ls′, Ext ls ls′ ρ_k → ∀ w, (𝒱⟦B_i⟧(ls′)δ(w) ─⋆ Φ ls′ w) ρ_k)

  for `n : E ∈ Σ` at `lin` and `unr`; at `aff` and `unr` the continuation's share also owes the
  cancel run (the `ewpTS` fixed point supplies both). At a stop `K[perform (n, (i, v))]` that run
  is the dead region's, `K†[raise (⊥, none)]`, owed at the empty error table (`cancelOwed`): a
  finaliser lets no raise escape it (§24), so the cancel keeps no error and its `ccatch` answers
  `()`. A handler the stop passes outward is dead in that run, so the run a forwarded stop owes is
  the inner one unchanged. So `κ`'s type stays `U((B_i ⊸ F_Σ R) & F_Σ 1)`. At an abortive
  operation the continuation is abandoned, so it must hold nothing owned:

      Π_Σ n i ls v Φ  ≜  𝒱⟦A_i⟧(ls)δ(v) ⋆ (λρ_k. NoOwn ρ_k)

  Otherwise the table is `False`. Final configurations include `K[raise (n, v)]`, with `K` free
  of `n` and unwind-clear.
  - The resource splits into the argument and the continuation's share, which is `∅` at the
    unrestricted qualifier.
  - The continuation is owed at every `Ext`-extension of the list: this is where protocols meet
    the Kripke order.
  - Each protocol is monotone in `Φ`.
- **The effectful `wp`.** `ewpTS ls e Π Q` is the least `P` closed under

      wpG ls e (λ ls′ t. (t = v ∧ Q ls′ v)
                        ∨ (t = K[perform (n, (i, v))], K free of n, ∧ Π n i ls′ v (λ ls″ w. P ls″ K[w])))

  It is written in `Prop`, as §6's `μ`. A computation performs finitely many operations before
  it answers: total correctness, as `wpTS`.
- **The relation.** `cC (F_Σ A) ls δ e ≜ ewpTS ls e Π_Σ (λ ls″. 𝒱⟦A⟧(ls″)δ)`, and `cC (F A) = wpTS`
  is unchanged.

### Finalisers that perform operations (K3, #162)

A finaliser is a computation `D : F_{Σ_D} 1` (§27), run where its `ubind` stands:

- it may call answering operations (flush a log, close a socket through its capability);
- it may raise and perform operations of live handlers: those outside the `[then]` during an
  ordinary unwind, and those outside every region that can cancel it during a cancel (§27's cancel
  rows).

If a finaliser raises during an ordinary unwind, the new unwind **supersedes** the pending one:
the pending `raise (m, v)` is in the finaliser's continuation and is abandoned. During a cancel,
the first error is kept and re-raised at the canceller, and the later ones lose to it
(*Cancels*). So an operation that raises must have an argument that drops with nothing owned (a
`NoOwn` value: data, borrows, `!`). The protocol's `NoOwn` share covers the abandoned argument. A
finaliser's operation, during a cancel or an ordinary unwind, is caught by the nearest live handler
of its name, and its continuation holds the rest of the finaliser and the frames outside it
(*Cancels*).

Richer policies are K3 (#162), and *Open*:

- richer reporting of finaliser errors that lose to the first (a count, a list, a chain), or a
  finaliser that must not fail (a row with no abortive operation);
- a finaliser that hands a residual to the handler (§14's `close` residual);
- retrying a failed flush.

### Divergence: an infinite loop that performs operations

`ewpTS` is a least fixed point. A computation that performs operations forever is typed as
§14's divergence: `ν` codata whose observation is a finite effectful step,

    Loop_Σ A B ≜ νX. F_Σ(A ⊕ U X) & F_Σ B

- **The observations.** Each observation performs finitely many operations and answers the next
  state or a result.
- **Handling per observation.** A handler is installed per observation, with the handler's
  state carried in the loop's state, as `experiments/LoopBorrow` lends per observation.
- **Answering operations** are calls on a capability the loop's state owns, lent by each
  observation.
- **Adequacy is §13/§14's:**
  - every run of a divergent program, under every allocator, is safe (never stuck);
  - each observation terminates;
  - a run that reaches a value reaches it at empty memory.

  There is no second fixed point: a greatest-fixed-point `ewp` would be a second mechanism for
  what `ν` already is.
- **Acceptance (3)** is a `Loop` whose observation logs by an answering call, with the `Log`
  state in the loop's state.
- **As built** (`Core/Types.lean`, `Core/Relation.lean`, `Core/NuRel.lean`, `Core/Nu.lean`):
  - an observation tree's leaf is `F A` or `F_Σ A` (`CTy.EffLeaf`): a row's layers with closed
    operation types over `F A`, `A` polynomial in `X`;
  - `cB` at `F_Σ A` is `ewpTS` at the row's table, with the answer at the candidate (`effRetE`);
  - `instT` passes through a row's layers, so `unfold` coiterates an effectful step, mapped
    through the `[let]` frame (`node_ok`);
  - `Loop_Σ A B` is `CTy.loopEff`, positive at a row of closed operation types
    (`loopEffBody_nuOk`);
  - the stack semantics (`cB_iff_stacks`, `cC_iff_stacks`) is stated at effect-free types, `ν`
    included.

### Theorems (the obligations of #186)

1. **Compatibility of the new rules.**
   - `sub_compatC`, from `ewpTS` monotone in `Π` (`ewp_mono`), with `ewp_of_wp` at `F A = F_∅ A`.
   - `perform_compatC` and `raise_compatC`, from `ewp_perform`.
   - `let_compatC`, from `ewp_bind`: `ewpTS e Π (λ v. ewpTS K[v] Π Q) ⊢ ewpTS K[e] Π Q` for `K`
     free of every name. The unrestricted case uses `vP_empty_of_persistent` on `Γ₂`.
   - `handle_compatC`, by induction on the least fixed point, in three cases:
     - `[ret]`, then `h_ret`'s relation;
     - `[op]` at its own name, then `h_op`'s relation at `(v, κ)`, where `κ`'s relation is the
       induction hypothesis under the protocol's wand (unrestricted: `κ` is at `∅`, so it is `!`);
     - `[unwind]` at its own name, then `h_op`'s relation at `v`. The abandoned continuation is
       `NoOwn`, and it joins `wpTS`'s leftover.
     - an operation of another name passing outward, where the stop configuration of the whole
       is `(hnd (n, H) K)[perform (m, v)]` or `(hnd (n, H) K)[raise (m, v)]`, and the
       continuation's obligation is the induction hypothesis. This case is the forwarding.
2. **Every existing rule's compatibility at `F_Σ A`**, through `cC_head`, `cC_step` and `cC_bind`
   at `F_Σ` (`ewp_head`, `ewp_step`, `ewp_bind_pure`). Every lemma at `F A` is unchanged, and
   `ewpTS Π_∅ = wpTS` (`ewp_bot`).
3. **Frames.**
   - **Pure callbacks** keep [TR] 6.64–6.66 unchanged: at the empty table `ewpTS = wpTS`
     (`ewp_bot`). Answering operations inside a borrow are calls inside the callback, under the
     same frames.
   - **Unwinding callbacks: the LIFO frame lemmas** `wpTS_I_frameU`, `wpTS_M_frameU` and
     `wpTS_M_antiFrameU`. They are the frames over `ewpTS` at an unwind-only table.
     - At a stop `K[raise (n, v)]` of the callback, the continuation's share is `NoOwn`. It holds
       at most borrows at the frame's lifetime and below, and it is abandoned as `wpTS`'s leftover
       `ρ⁺` is.
     - The frame then ends exactly as at a return: 6.64's `immEnd`, and 6.65/6.66's unfold of the
       `mut` cell, whose value and predicate the world keeps whether or not the borrow was
       forgotten.
     - The argument `v : A_i` outlives the frame, because operation types are closed data.
     - So the unwinding form's `ubind` gets the source back, runs its finaliser, and raises
       again.

     These are the new semantic obligations of unwinding, and they are what "an unwind crosses a
     borrow without T1" means. If one does not hold, the stage stops with a machine-checked
     obstruction, and the unwinding forms are withdrawn.
   - **Cancelling a continuation** is running its dead region from `raise (⊥, none)`
     (`cancelOwed`, `ewp_ccatch`). Its obligations are the frame lemmas above; `ccatch`'s
     compatibility is `[unwind]`'s, and `cfin`'s is `[finalise]`'s, with the finaliser at the pure
     row (`then_cancel`, `cfin_run`). So cancelling a stored continuation needs nothing beyond what
     storing it needed. A continuation stored while it captures borrows is T1 (#172). Once T1 makes that
     storage sound, the lends it holds are ended by the same LIFO frame lemmas that end them at a
     `raise`. Within this entry, non-abortive control operations cannot cross a borrow, so no stored `κ`
     captures a lend, and `cancel` needs only the unwinding forms of the borrows *inside* `κ`.
   - **`ubind`**: `then_compatC`, from `ewp_ubind`. The finaliser's context is framed off while
     `M` runs, and consumed by `D` at an unwind.
4. **Adequacy.**
   - `fundamentalC` and `fundamentalD` cover the extended judgment.
   - `adequacyD` holds for every closed `F 1`, handled programs included.
   - §14's adequacy holds for divergent programs whose observations are effectful.
   - A closed program with an unhandled operation is not typed at `F 1`.

### Laws

The equations and semantic choices the effect system is decided to satisfy, each with the Core
theorem that states it. A law of the machine is stated in every evaluation context
(`Core/EffMachine.lean`), and a step it names is its configuration's only step (`Step1Only`, by
unique decomposition and determinism), except an allocation, which takes any location the memory
does not hold. Safety is stated of the runs of typed programs (`Core/EffSafety.lean`).

1. **Deep handler laws** (Plotkin–Pretnar).
   - *H-ret*: `hnd (n, H) v ↦ h_ret v` (`catch_ret`).
   - *H-op*: `hnd (n, H) K[perform (n, v)] ↦ h_op (v, κ)`, `K` free of `n`, keeping the memory
     (`catch_step`).
     - At an unrestricted operation `κ` is `kappa H K` (`catch_unr`). Resuming it at `w` runs
       `hnd (n, H) K[w]`, the handler reinstalled (`kappa_resume_steps`); cancelling it runs
       `ccatch (K†[raise (⊥, none)])` (`kappa_cancel_steps`).
     - At a linear or affine operation the next two steps allocate `κ`'s cell at a location `ℓ`
       the memory does not hold, any such, and hand the clause `kappaC` at `ℓ`, affine exactly at
       an affine operation (`catch_cell`). Every run from the catch is a prefix of these three
       steps or goes on from them (`catchEv_cell`).
     - Resuming `kappaC` at `ℓ`, at a memory holding `()` at `ℓ`, releases `ℓ` and runs
       `hnd (n, H) K[w]` (`kappaC_resume`): three steps reach the release, and after it `κ`
       resumes as `kappa` does (`kappaC_resume_parts`, `kappa_resume_kResume`). An affine `κ`'s
       cancel releases `ℓ` and runs `κ`'s cancel run (`kappaC_cancel`). A linear `κ`'s cancel
       branch has no step (`kappaC_cancel_lin`).
     - On a run to a value, a use of `κ` at its cell releases the cell three steps later: `κ` is
       applied to `inj₁ ()`, or to `inj₂ ()` at an affine operation, and the memory holds `ℓ`
       (`use_frees_cell`).
   - *H-fwd*: an operation of a name `m ≠ n` is no redex at `hnd (n, H)`. With `K` free of `m`,
     `hnd (n, H) K[perform (m, v)]` takes no step in a context free of `m`; under the nearest
     handler of `m`, that handler catches it, and its `κ` holds `hnd (n, H)` (`catch_fwd`), so
     resuming `κ` reinstalls both (`fwd_resume`). With `K` catching nothing of `m`,
     `hnd (n, H) K[raise (m, v)]` steps, in every context, as `raise (m, v)` does (`fwd_abort`).
   - The abortive catch `hnd (n, H) K[raise (n, v)] ↦ h_op v`, `K` catching nothing of `n`
     (`catch_abort`), and the finaliser frame: `ubind (N, D) v ↦ N v` (`then_ret`), and
     `ubind (N, D) K[raise (m, v)] ↦ D (); raise (m, v)`, `m ≠ ⊥` and `K` catching nothing of `m`,
     the finaliser running under a frame that catches nothing (`then_fin`).
2. **Algebraicity.**
   - *At an abortive operation*: `raise e to x. P = raise e` and `(raise e) w = raise e`. In the
     machine, `raise p` under frames that catch nothing of its name steps, in every context,
     exactly as `raise p` steps there: the frame that catches it drops them (`abort_absorbs`;
     `abort_to`, `abort_app`).
   - *Sequencing*, `op(v) to x. P = op(v; y. (k y to x. P))`, is not yet a Core theorem.
3. **Static per-site names: no accidental handling.** An operation is caught by the nearest live
   handler of its name (*Names*); a handler of another name passes it, in the machine as item 1's
   H-fwd (`fwd_abort`). `tunnel` (E6, `Core/EffTier1Programs.lean`): `fwrap` handles `exnᵢ` around
   a callback that raises `exnₒ`, and the raise passes `fwrap`'s handler to `toResult`'s outside
   (`d_tunnel`, `tunnel_run`; the kernel program `tunnel`).
4. **Continuations are linear or affine; `unr` is tolerated.** A clause's `κ` is at `kTy`
   (*Kinds of operation*): at a linear or affine operation a thunk of an `&`, which is not
   persistent, its cancel branch at `⊤` at a linear one. So a typed clause uses `κ` as its qualifier
   allows, by inversion of `CDerives` (`Core/Inversions.lean`):
   - At every resuming linear or affine operation, every context and every cancel row, a clause
     that drops `κ` (R1), resumes it twice (R2), or cancels and then resumes it (R4) has no
     derivation at its clause type; at every linear one, neither has a clause that cancels it (R3)
     (`refuses_R_clauses`). The refusals are of `κ`'s use, not of the clauses' form: at the clause
     type of a linear `1 ↠ 1` a clause that resumes `κ` once is typed, and a clause that cancels
     `κ` is typed at an affine operation and refused at a linear one (`clauseRefusals_pinned`).
   - `forget κ` has no derivation at `1` (`not_forget_kappa`), and a handler whose clause stores
     `κ` in a cell and reads it out twice has none at all (`not_der_at08`). Moving `κ` through a
     cell and resuming it once is typed (`d_at08Once`).

   An unrestricted `κ` is `!`, and a clause may use it any number of times. That every run of a
   typed program uses each linear or affine `κ` it catches once (S6) is §25 *Open*.
5. **A cancel is not interceptable, and the cancelled region's frames are dead.** `κ`'s cancel
   branch runs the region with its handler frames and cancel delimiters removed (`Kont.dead`), so
   a dead frame catches nothing (`hasHnd_dead`, `catches_dead`, `noCC_dead`). Read prefix-closed
   (`cancel_prefix`, `Core/EffCancelRuns.lean`): take a run of a term a tied derivation types,
   from the empty memory, that cancels `kappa H K`, or `kappaC aff ℓ H K` at its cell, and reaches
   the start of the cancel run (after the cell's release). Every path from there is a prefix of the
   cancel trace of `K†` (`CancelTr`):
   - `K`'s finalisers fire innermost first, each by `[finalise-cancel]` and then `D ()` running
     alone under `cfin`, to `[cfin-ret]` or `[cfin-raise]`;
   - a running finaliser's `cfin` frame is passed by `[cfin-cancel]`, its error first;
   - the first kept error wins, and the canceller gets `()` or the kept error re-raised, an error of
     a name of the effect context (`CancelsNamed`).

   The hypothesis is that each of `K`'s finalisers is a closed computation at a row of abortive
   operations of the context's names (`FinRow`). Typing then gives that it runs alone from every
   memory with finitely many cells (`finAlone_of_finRow`; at the empty row, to `()`,
   `finOK_of_finRow`). A finaliser that performs an operation a handler outside it answers (§27) is
   not covered (§27 *Open*). `progOutT` meets the hypotheses: a tied derivation types it, its run
   cancels `κ`, and its region's finaliser raises `2` (`progOutT_cancel_prefix`). So does
   `progOutTA`, the same program at an affine raise of `2` (`progOutTA_cancel_prefix`), typed by a
   tied derivation at an effect context with no unrestricted abortive operation (`EffCtx.NoUnrExn`,
   §18; `noUnrExn_Ξ₁₂A`): the shape the checker gives every program it accepts
   (`checkProgram_tiedAt`).
6. **The finally law; a finaliser's raise propagates; a raise with no live handler is a type
   error.**
   - *Finally*: `(raise e) then x. N unwind D = D (); raise e`. `[finalise]` steps
     `ubind (N, D) K[raise (m, v)]`, `m ≠ ⊥` and `K` catching nothing of `m`, to
     `D (); raise (m, v)`, its only step (`then_fin`); `then_compatC` is the rule's compatibility.
   - *Unwinding*, read prefix-closed (`unwind_prefix`): from a raise of a name `m ≠ ⊥` pending
     under frames with no running finaliser's `cfin`, every path is a prefix of the unwind trace
     (`UnwindTr`). The finalisers fire innermost first, each running alone. One that returns `()`
     hands the raise on (`[1↦]`); one whose own raise escapes supersedes the pending raise, which
     goes on from there. A handler of the raise's name ends the trace. The hypothesis is item 5's
     (`FinRow`); `(raise 1) then x. x unwind raise 2` meets it (`supersede_prefix`).
   - *Complete runs* (`finaliserOrder_at`): suppose each finaliser a program's runs fire runs alone
     to a value or to an uncaught raise of a name `≠ ⊥` (`FinAloneAt`). Then every complete unwind
     through frames with no handler fires their finalisers innermost first, a finaliser's raise
     superseding the pending one (`UnwindRun`). So does every complete cancel of `kappa H K`, `K`
     holding no `ccatch` or `cfin` frame, keeping the first error (`CancelRun`). The program
     above meets `FinAloneAt` (`finAloneAt_supersedeE`, `supersede_finaliserOrder`).
   - *A raise with no live handler*: a typed closed program's raises are caught (item 9). A
     finaliser whose raise has no live handler at the canceller is rejected by §27's typing, by
     inversion of `CDerives` (`Core/EffCancelTyped.lean`, §27 *Programs*). `progT`, whose
     finaliser raises `2` handled only inside the cancelled region, has no derivation at a row
     without `2` (`not_der_progT`). E7c, a `timeout` whose cancelled region handles its
     finaliser's raise of `exnᵢ`, has none at a row without `exnᵢ` (`not_der_e7c`), and is typed
     at the row of `exnᵢ` (`d_e7c_lift`): the rejection is of the rows with no live instance.
     `progNCrecT`, whose second finaliser performs the operation of the handler that cancels, has
     no derivation at all (`not_der_progNCrecT`).
9. **Safety**: every operation a run performs has a live handler of its name, and every raise a
   live frame that catches it; a stuck state is never a semantics. Stated of a typed closed
   program, a closed computation of `F A` (its row empty, `A` any type), and of its runs from the
   empty memory:
   - Every run continues to a value (`total_every_run`), so none is stuck (`adequacyD_safe` at
     `F 1`).
   - No configuration a run reaches is `K[perform p]` with `K` free of a handler of `p`'s name, or
     `K[raise p]` with `K` catching nothing of it: each is a value or steps (`effSafe_closed`). Its
     raise case (`r = true`) says that an error a typed closed program raises is never left
     uncaught.
   - Each configuration a run reaches has a closed term and closed stored values, and goes on
     (`LiveOK`, `liveOK_closed`). It holds no stuck redex at an evaluation position
     (`LiveOK.not_stuck`), `() ()` among them (`stuckAt_unit_app`): the cancel branch of a linear
     `κ` (`kappaC_cancel_lin`) is never reached.
   - At a persistent `A`, a run that reaches a value reaches it at the empty memory, every cell it
     allocated released, each continuation's cell (§25) among them (`leakFree_closed`,
     `Core/EffPrograms.lean`).

### Baseline

`cC (F A)`, `wpTS`, every existing rule and every existing compatibility lemma keep their
statements. `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD` keep theirs, over the
extended judgment. §18's answering handlers are capabilities, unchanged; its control effects,
`Fail` among them, elaborate to this entry's `handle`, `perform` and `abort` (#188).

### Programs

Primary, each typed, safe and run:

1. **`Log` + `Fail`**, both ordinary effects: `log` answering, `raise` abortive (affine, answer
   `0`).
   - A function that logs and may raise.
   - The `Log` handler inside and outside the `Fail` handler (`to_result`). The logs are kept
     when `Log` is outside. They are lost when `Fail` is outside: the unwind ends `Log`'s
     `with`, whose finaliser drops its state.
   - Once more with `log` a native (affine) control operation, to exercise rows and forwarding.
2. **`borrow mut buf { … log(x) … }`** with the `Log` handler outside.
3. **`borrow mut buf { … raise(e) … }`** with the `Fail` handler outside. Unwinding ends the lend
   (the unwinding `withbor`'s `ubind`), the buffer goes back to its owner (the owner's finaliser,
   or its enclosing borrow, which continues), and the handler receives `e`. Memory ends empty.
4. **`loop { log("tick") }`**, a `Loop` with the `Log` state in its state.
5. **Early exit.** `take(n)` stops a producer that holds a resource (an owned cell). The producer
   yields by an affine control operation; after `n` elements, the consumer's handler cancels the
   stored continuation. The producer's finaliser frees the cell, and memory ends empty.
6. **Cancelling a suspended computation.** A handler stores `κ` and then cancels it instead of
   resuming it. The resource `κ` captured is finalised, and memory ends empty.

Secondary:

- the reconciler chain `timeout |> retry |> log |> kube`;
- two blocks sharing one stateful handler, at any depth;
- `memo` with a re-entrant forward;
- multi-shot `choose`;
- resume-later.

**As built** (`Core/EffPrograms.lean`). Each program is a closed `CDerives` derivation; every run,
under every allocator, is safe and ends at the empty memory (`adequacyD`, and `adequacyD_obs` at a
persistent answer). Where the answer type has one value, every run reaches it. `Support`'s
interpreter has §19's steps, and `eval` gives each program's answer by `decide`.
1. `logOutside` and `failOutside`, with `logRaise`'s answer at `0`:
   - `Log` outside: every run answers `(f, inj₂ ())`, the log state kept beside the error, and
     `eval` gives `(inj₂ (), inj₂ ())`;
   - `Fail` outside: every run answers `inj₂ ()`, the log cell freed by the unwinding `withbor`.

   `nLogOutside` and `nFailOutside` do the same with `log` a native affine operation and
   `with_log` resuming `κ`.
2. `logInBorrow`: `log` is a `withswap` on the outer borrow `l`, captured by `borrow mut b`'s
   callback.
3. `reborrowRaise`: `raise` inside a reborrow (`withbor3U`) inside `borrow mut r` (`withbor2U`).
   Both lends end, `r` is freed, and every run answers `inj₂ ()`.
4. Two versions:
   - `tickAnsProg n`, as stated: `Loop 0 (Ref Flag)` with the log cell as the loop's state;
   - `tickProg n`: `Loop_{Log} 0 1` with a native `log`, `with_log` around each observation,
     for every `n`.
5. `takeProg n`, for every `n`: `take` is a state-passing handler, `U(N ⊸ F(1 ⊕ 1))`.
6. `storeCancel`: `κ` stored in a cell, taken back and cancelled.

**Rejected** (`Core/Rejections.lean`). No derivation types these, at any context and any judgement,
each by inversion of `CDerives` (`Core/Inversions.lean`):
- `at05`: an answering handler whose body uses its `Mut` capability twice, `(m, m)`
  (`not_der_at05`);
- `at06`: a clause that releases a cell the handled body also releases; a clause is at a `!` type,
  so it captures only persistent values (`not_der_at06`);
- `at08`: a clause that stores `κ` in a cell and reads it out twice (`not_der_at08`). `at08Once`,
  the same clause with the copy used once, is typed (`d_at08Once`), and every run of it ends at `()`
  with the memory empty (`at08Once_runs`); it is the kernel program `at08-once`;
- `at13`: a clause that forgets `κ` (`not_der_at13`).

**The effect properties** (`Core/EffTier1Programs.lean`). Each program is a closed term with a
derivation tied to its effect context `ΞE` (`CDerivesAt`, read in `CDerives`), which has no
unrestricted abortive operation (`noUnrExn_ΞE`), and a run computed by `runM` from the empty memory
to its answer at the empty memory (`runM_val`):
- E1, a function at several rows: `hofTwoRows`, `hof = λg. g ()` let-bound once (§24's
  `[let-poly]`) and called with a pure callback, with one that raises `exn` under `toResult`, and
  with one that performs the affine `wait` under a handler that resumes `κ` at its cell. The
  callbacks `λ_. M` are §26's `[λ-dead]`. It answers `(tt, (inr (), tt))` (`d_hofTwoRows`,
  `hofTwoRows_run`).
- E2d: `sumGen`, a consumer of a generator let-bound once and used with generators at `yield ⊙ ∅`
  and at `yield ⊙ exn`; the raise of `exn` passes its reinstalled handler. It answers
  `(tt, inr ())`.
- E4, a deep handler: `deepGen`, whose handler of `yield`, reinstalled at the resume, catches both
  yields, its clause performing the linear `tick` at each; a handler of `tick` counts them. It
  answers `((), 2)`. Under a handler of `tick` that resumes, `deepGenPlain` answers `()`
  (`d_deepGenPlain`, `deepGenPlain_run`).
- E5, nested handlers in both orders: `withLog`, a state-passing handler of the linear `log`, and
  `toResult`. With `withLog` outside, the log is kept beside the error (`nestedLogOutside`,
  `(inr (), tt)`); inside, the raise unwinds `withLog`'s handler and its state
  (`nestedFailOutside`, `inr ()`).
- E6, no accidental handling: `tunnel` (*Laws* item 3).
- E7, abandoning a suspension: `timeout` cancels a body whose region holds finalisers: one that
  returns (`e7a`), one that raises `exnₒ`, handled outside (`e7b`), and two that raise, the first
  error kept and re-raised at the canceller (`e7d`). Each answers `inr ()`. E7c is rejected
  (*Laws* item 6).
- E8b, the finally law: `e8b` unwinds `exn_a` through a finaliser that raises `exn_b`, which
  supersedes it. It answers `inl (inr ())`.
- E9, a stored continuation: a clause answers a closure holding the affine `κ`, called after the
  handler has returned. It resumes `κ` (`storedKResume`, `ff`), cancels it (`storedKCancel`, `tt`),
  or cancels it and its region's finaliser raises `exnₒ`, caught outside (`storedKFin`, `inr ()`).
- E10: `timeoutProg`, `timeout` let-bound once, which cancels a body that waits and passes a body's
  raise. It answers `(ff, inr ())`.

E5's state function and E9's closure hold a `bool` across a `[let]` at a row with `exn`, so they are
typed where `exn` is affine (§27 *Typing*). The kernel programs `hof-two-rows`, `sum-gen`,
`deep-gen`, `deep-gen-plain`, `nested-log-outside`, `nested-fail-outside`, `tunnel`, `e7a`, `e7b`,
`e7d`, `e8b`, `stored-k-resume`, `stored-k-cancel`, `stored-k-fin` and `timeout` are these terms,
compiled at every stage; the lets of `hofTwoRows`, `sumGen` and `timeoutProg` are lowered per use
(§24 *Lowering*).

### Lowering

The backend lowers §19 in two passes over the closure IR (`Backend/Clos/Capture.lean`, then
`Backend/Clos/Unwind.lean`). There is no handler stack and no search, and nothing beyond calls,
branches and the program's own memory is used: no stack switching or other target feature is
part of the semantics.

**Abortive operations** are branch-per-call propagation, the representation of `Result` and `?`.
- **What raises.** A code raises the keys `(n, i)` (static names) its body may raise and no
  frame of it catches, by the closure flow.
- **The convention.** A code that raises answers `inl v` or `inr p`. The codes called at one site
  share a convention.
- **Branches.** A call branches exactly when its callee may raise, and a tail call passes the sum
  on.
- **Handlers and finalisers.** A handler of a name whose operations are all abortive is a `catch`
  of its name, then the answer clause or the caught operation's clause. A finaliser frame
  `M then x. N unwind D` is `fin D M`, then `N`: `fin` runs `D` on `inr p` and raises again.

Answering operations are calls on a capability, compiled as calls (direct when the flow finds one
code).

**Control operations** become state machines, as Rust's `async` does.
- **A handler** of a name with control operations runs its body as a code of its own, and
  *drives* its outcome: a value goes to the answer clause; an operation of the name to its
  clause, with `κ`; any other operation passes outward (forwarding), and when it is resumed the
  driver resumes the body and drives again, which reinstalls the deep handler.
- **A code that may suspend** answers its *outcome*: `inl v`, or `inr (p, k)` when it suspends
  with the payload `p`. The payload is a variant per operation of the program, so operations of
  any argument types share it. `k` is the suspended computation: a closure of the code's resume
  code over its *state*.
- **The state** is an `n`-ary sum with one flat tag word, one variant per resumption point of the
  body: a `perform`, a call of a code that may suspend in non-tail position, a forwarding. It
  holds the variables live there, the finalisers of the `then` frames among them. At a call
  point it holds the callee's `k`: **suspension through calls nests**, a caller's state contains
  its callee's, and `κ` is a value of statically known size.
- **The resume code** takes `inl y` and switches on the state: the point's continuation, its
  frames rebuilt around `y`. A call point resumes its callee's `k` first, and suspends again at
  the same point when the callee does.
- **Which codes suspend** is the least solution of the operations each code's body and callees
  may perform, over the closure flow: the rows' information, recovered after erasure, and
  resolved per code as the codes are monomorphic (a let used at different rows is lowered per
  use, §24 *Lowering*), and per projection: a call whose argument is a
  known injection (a codata observation, `.1` or `.2`) suspends with the operations of that
  projection of its callee, through codes that pass their argument on. Nothing is written by the
  programmer.
- **Tail calls.** The codes called at one site share their convention, and so do a code and a
  code it calls in tail position when the call closes a loop of tail calls, or when the caller has
  no resumption point of its own and may tail-call at most one code that suspends (a wrapper).
  Such a tail call passes its callee's outcome on, so a loop of tail calls through a suspension
  stays a loop, and a clause that resumes in tail position runs the handler in constant stack
  (#123). Any other tail call is a resumption point, so a suspension's continuation is of one
  code.
- **`κ`** is a closure over the handler and the body's `k`: its resume entry is a closure that
  resumes `k` and drives again; its cancel entry cancels `k`.

**A tail-resumptive operation is a direct call.** When every handler of a name whose body may
perform an operation has the same closed clause for it (the specialisation: the handler is known
statically), the clause
resumes `κ` once, in tail position, with an answer computed without `κ`, and it neither suspends nor
raises, a `perform` of the operation calls the clause's code with its resume removed. Nothing
suspends or resumes, and no continuation is materialised. A clause that captures values, or
whose handlers differ, is a state machine like any other: resumed in tail position, it still
runs in constant stack.

**Abortive payloads.** A `raise`'s argument is carried as a variant of the program's abortive
operations when it has more than one (`wrapRaise`), and a handler's clause takes it out of its
variant: a code that raises two operations of different argument types answers one payload type.

**Cancel** is the state's destructor. The resume code takes `inr ()` and switches on the state:
the callee's `k` is cancelled first (innermost), then the point's finalisers run innermost first,
and every other variable is dropped; borrows' unwinding forms are finaliser frames, so their
lends end here. A finaliser's error is caught (`catchAll`), and the first one is kept: the
canceller re-raises it (`reraise`), and the later ones lose to it (*Cancels*). The region's
handlers are dead, as *Cancels* asks: a cancel runs from the canceller's call of `κ`, and the
cancel arms run only the points' `fin` frames, so a finaliser's raise meets the arm's `catchAll`,
never a handler of the region.

**What the representation costs**, as Rust does:
- **Recursion through a resumption point.** A code whose state holds its own `k` has a recursive
  closure type, kept in a heap object (`Backend/README.md`): one allocation per level, as Rust
  needs `Box::pin` for a recursive `async fn`. A resumed level that suspends again is built in its
  own object, updated in place, so the count stays one per level (`recursive-yield`). Recursion
  through several codes costs one object per code of the cycle at each level: a clause that
  resumes in non-tail position inside a handler that forwards recurses through the driver and
  the clause, two per level (`forward`). One per level would box one edge of the cycle of
  closure types only, as a recursive data type's back edge is (#54).
- **A call that may reach several codes that suspend** dispatches, at the call and at each resume
  of its continuation, as `Box<dyn Future>` does; the state is the union of the callees', unboxed,
  so nothing is allocated (`two-callees`).
- **An unrestricted `κ` resumed several times** is copied by the closure IR's ordinary copy: its
  state is duplicated, counted in `copies` when it holds a non-trivial value. The typing makes
  its captures persistent, so the copy duplicates no resource (`multi-shot`).

**A finaliser frame's clauses are one code.** `M then x. N unwind D`, `ubind (λx. N, λ_. D) M`,
is converted with `N` and `D` one code, called on `inj₁ x` to continue and on `inj₂ ()` to
finalise (`markUbinds`, `Backend/Clos/Convert.lean`): exactly one of them runs, so what both use
is captured once, not copied (the drop glue around an operation that holds an owned list or
cell, §15).

**Not lowered**, rejected with a message: a name that has both control and abortive operations.

**As built** (`Backend/Kernel.lean`, `bcc kernel`, `scripts/compile-kernel.sh`). Every
acceptance program, with its native variants, `Core/EffExamples.lean`'s two handled programs,
`Core/EffCancel.lean`'s cancels `prog₃`, `progRe` and `progOut`, and `Core/Rejections.lean`'s
`at08Once` (`κ` moved through a cell, `at08-once`), compiles through every stage
with the same answer and `live 0`, as do terms for the shapes above (100000 operations of a loop
as direct calls, and as suspensions resumed in tail position, both in constant stack; recursion
through a resumption point; two possible callees; forwarding with and without a cancel; a
continuation resumed twice; a let-bound function used at two rows through what it answers).
`prog` is not compiled: its run ends at a raise no handler catches (*Cancels*). The counts
(`corpus/kernel-counts.expected`) and the hand-written equivalents (`corpus/capture-*-hand.bc`):

| program | allocations | dispatched calls | hand-written |
|---|---|---|---|
| `log-outside-native`, `fail-outside-native` | 0 | 0 | 0, 0: the flag passed by hand |
| `tick-native` | 0 | 0 | 0, 0: a loop over the flag |
| `take` | 2 | 2 | 1, 0: a generator (§15) owning the cell |
| `store-cancel` | 2 | 0 | 2, 0 |

`take`'s extra allocation is its count's node (a unary number), and its dispatched calls are its
own: its handler answers one of two closures. The lowering adds neither.

### Open

- Generative handler names (Ξ's runtime labels), behind a continuation confined to its handler's
  scope (T2, #173).
- A tail-resumptive clause that captures values, compiled as a direct call with its captures
  passed to the operation as evidence (*Lowering*); it is a state machine now.
- A non-abortive control operation crossing a borrow's scope (T1, #172). Cancelling
  such a stored continuation then needs nothing more.
- Finaliser policies beyond "a new unwind supersedes" and "a cancel keeps the first error"
  (K3, #162): richer reporting of finaliser errors that lose to the first.
- The typing of finalisers that raise to live handlers and perform operations (decisions D2, D3
  of 2026-10-08), and the lowering of a finaliser that suspends. The machine already gives them
  their meaning (*Cancels*).
- Parameterized handlers are written with a state-passing answer type
  `F R = F(U(S ⊸ F (A ⊗ S)))`, which the elaborator gives a handler with a state (§21); a native
  parameter in the lowering is not provided: each resume applies a closure of the state, a
  dispatched call.
- **Shallow handlers:** covered by `ν` codata (stored generators, §15) for step-wise handling; not
  a separate construct unless a target needs it.
- μ with `X` under `⊸` (T15, #182).
- Type-keyed provision of answering-only signatures (interfaces): reserved; designed after #186's
  core (#169). The signature form above is the interface form. A signature whose operations are
  all answering may later be implemented for a type by a persistent provider, resolved and
  specialised at compile time. Control operations stay lexical.

---

## 20. Entry 19 — recursion as an effect

**Revised by §21.** A recursive group is the bounded fixed point of its generator, called
directly: there is no `rec` operation and no `rec` site, and layers are transformers of the
generator. The kernel's `bounded_fix`, the drivers, `Exhausted`, the budget and the heap driver
below are unchanged; *Recursive groups* and *Lowering* below are as revised there.

### Motivation

Decision 24 (revised): a recursive function is written as ordinary calls of itself. A function
that calls itself, or functions that call one another, is a **recursive group**, and a **driver**
runs it, chosen at the call site. Two drivers are provided:

- **`bounded`**, the default: a native recursion that carries a **budget of depth**, each call
  with one less. Bounded depth and finite branching make the recursion total, so it runs inside
  one computation, as an ordinary native recursion. When the budget is spent the recursion
  performs **`exhausted()`**, an abortive library effect: it unwinds as any error does, running
  the finalisers of what it abandons, and a handler receives it. `Exhausted` stands in a
  recursion's row where `div` stands in a loop's.
- **`deep`**, the heap driver: the pending calls are first-order frames in one growable buffer.
  It is limited only by memory, and it is div.

The budget is a conservative reading of a stack check in each recursive function's entry code:
on WebAssembly, whose stack cannot be inspected, an explicit depth counter (the budget itself,
passed down as a word); with LLVM, a comparison of the stack pointer against a limit, as Go's
prologue does. Design and calibration: `docs/rec-effect/bounded-deep.md`.

### The kernel: `bounded_fix`

    bounded_fix[A, C] : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)

at every computation type `C` (a row `F_Σ B` among them). From `(s, (k, a))` it runs the step `s`
on `(self, a)`, `self` the self-reference:

    (μ, bounded_fix (s, (k, a))) ↦ (μ, s (self_k, a))                          [boundedFix]
    self_0 = inj₁ ()          self_{j+1} = inj₂ (λx. bounded_fix (s, (j, x)))

The budget `k` is read unsigned and counted down by the machine, as `count`'s counter is counted
up (§16), so the step is the same at every host. The step decides what a spent budget does:
`self` is `inj₁ ()`.

- **As built.** The primitive `Prim.boundedFix` and its head step `Head.boundedFix`
  (`Paper/S1_Syntax`, `Paper/S3_Dynamics`; `boundedFixNext`, `fixSelf` in
  `Support/Dynamics/Arrays.lean`), the interpreter's step, the `CDerives` rule `boundedFix`, its
  soundness `boundedFix_compatX` (`Core/BoundedFix.lean`), and the checker's constant
  `bounded_fix[A, C]`.
- **The proof** is the induction on the budget at every `Σ`: the self-reference at `k` is valid
  at `1 ⊕ !U(A ⊸ C)` (`fixSelf_valid`): `inj₁ ()` at `0`, and at `j + 1` a function whose call
  is one `boundedFix` step to the step on the self-reference at `j`. The relation is unchanged:
  `𝒞⟦C⟧` at a row is §19's `ewpTS`, total correctness, read only through its closure under a
  pure step in front (`cC_head`). `fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD` and
  the totality theorems (`total_every_alloc`, …) cover the extended judgment; their axioms are
  within `[propext, Classical.choice, Quot.sound]`.

### Recursive groups

A recursive group is a strongly connected component of the calls among a program's functions
that has a call in it (`Frontend/Elab/Effects.lean`, `recGroupsOf`); it is declared at its last
member (`defineGroup`). Its members take no lifetime parameters and are persistent functions. Its
**row** is the union of its bodies' rows and the exhaustion effect.

The **exhaustion effect** is the first declared effect with no type parameters whose one
operation is abortive and takes no argument: `Exhausted` of `lib/rec.bc` (`include rec`), by its
structure, as the iteration effect is (§15). Nothing in the elaborator names an effect.

A call of a member from outside the group is a call of the group's **copy** for what serves its
row there (§18's copies, `groupCopy`): the bounded fixed point of the group's generator (§21).
The kernel has no recursive type and no recursive handler: the self-reference is a value the
generator is given, and the knot is tied by `bounded_fix`.

**Not provided**, each rejected with a message: a member whose body has a `while` or a `loop`
(§21 *Open*); a generic recursive function; and a call of itself inside a handler of an effect
its recursion performs, which would need a site per level (recursion through a site, decision 57;
generative labels, #173; `corpus/reject/rec-through-site.bc`). A recursion with no handler of
`Exhausted` in scope is rejected as any unhandled operation is (`corpus/reject/rec-unhandled.bc`):
a platform that provides none rejects unbounded recursion statically.

### The heap driver

`with d { M }`, `d` a function of the type of a heap driver,

    !(!(A ⇒ B ⊕ A ⊗ (K ⊕ 1)) ⊗ (!(K ⊗ B ⇒ B ⊕ A ⊗ (K ⊕ 1)) ⊗ A) ⇒ U(Loop B 1))

(`deep` of `lib/rec.bc`, recognized by that type), drives the recursive groups `M` calls by `d`:
`with` removes `Exhausted` from `M`'s row, and a call of a member is a call of its copy for `d`,
`x__d`, which is `d` of the group's **machine** on the tagged argument: a call of a div function
(§14), so the caller is div.

- **The machine** `g__mach = (start, resume)` is made from the group's source, a function of the
  members' self-references, after its sugar is elaborated (`Frontend/Sugar.lean`, `recMachine`,
  `rmWalk`): a call of a self-reference is lifted out of the value it is in, the rest of the body
  is moved into it (into each arm of a `case`), and at `x ← self_j W; N` the code answers the
  request `inr (inj_j W, f)`. The frame `f` is first order: a variant of `K` per call that is not
  in tail position, holding the variables `N` uses, with their types; a call in tail position
  pushes none (`inr ()`). `resume (k, b)` binds the frame's variables and `x = b`, and goes on
  with `N`.
- **`deep`** is library code over `unfold` (§7): its state is a buffer `buf (1 ⊕ K)` (§17) of
  pending frames and the next action; an observation starts a call or resumes the frame on top.
  A slot holds `inl ()` when empty, the filler of `1 ⊕ K` (so a frame may hold an owned `μ` value
  or any value with no filler of its own). The buffer doubles when it is full: a few allocations
  per run, and none per call.

A recursion under `deep` that performs an effect is not provided.

### Lowering

`bounded_fix` is converted to two codes (`Backend/Clos/Convert.lean`, `fixValue`): `fix (s, (k, a))`
calls `s` on `(self, a)`, and `self`'s closure, a stack value of `s`'s words and `k − 1`, calls
`fix` again. A member's call of the group is a direct call of the self-reference (§21), so each
level is a native call of known code, with nothing allocated and nothing dispatched
(`corpus/rec-fib.bc`: 0, 0, 0; `corpus/rec-tree.bc`: the tree's own objects only).

`wasmtime` runs with a 64 MiB stack (`Backend.wasmStackBytes`, `wasmtimeArgs`); the budget is
calibrated against it with room for the finalisers an unwind runs (headroom): measured at about
120 bytes of native stack per level for a linear recursion, 10 000 levels use about 1.2 MiB.

The backend carries the abortive operations' arguments as a variant per operation when a
program has more than one (`wrapRaise`), so that a code raising two of different argument types
(`Fail[i32]` and `Exhausted`) answers one payload type.

### Programs

`corpus/rec-fib.bc`, `rec-tree.bc` (a recursive walk of a `mu` type), `rec-even-odd.bc` (mutual
recursion), `rec-parser.bc` (a recursive-descent parser over five members whose errors leave the
recursion through `Fail`), `rec-overflow.bc` (a recursion far past its budget: `Exhausted`
caught, a cell held at every level freed by the unwind, `live 0`), `rec-deep.bc` (three groups
under `deep` at three times the budget); rejects `corpus/reject/rec-*.bc`; reports
`corpus/reports/rec-*.txt`.

### Baseline

One `CDerives` rule and one machine step are added, with their compatibility lemma; the relation,
every other rule and every existing theorem keep their statements. `fundamentalC`, `adequacyC`,
`fundamentalD`, `adequacyD` and §14's totality theorems cover `bounded_fix`.

### Open

- **`memo`**, a layer (§21), needs a map (#211); deferred.
- **The budget is per driver**: a recursion nested in another's body has a budget of its own, so
  their native depth adds. A global check (the stack pointer, with LLVM) makes it one.
- **Exact frame sizes** for the headroom: the calibration is a measured constant
  (provisional).
- A recursion under `deep` that performs an effect; a generic recursive function; recursion
  through a site (#173). A recursion whose body loops: §21 *Open*.
- Tail recursion modulo context (Leijen and Lorenzen, POPL '23) could make some frames smaller
  before they reach the buffer; `fold_imm`'s native depth could use the same buffer.

---

## 21. Entry 20 — recursion as the fixed point of a generator; closure conversion at the seams

### Motivation

§20 turned a recursive group's calls of itself into an operation, `rec`, at a site of the
group's own, whose clause called the self-reference. The second-class spike
(`docs/second-class-and-system-c.md`, #229) found that this site, and not the kernel, caused most
of the gaps §20 listed:

- **an operation that resumes in a recursion**: `[then]`'s finaliser is at an abortive row, and the
  site's clause cancelled its continuation there, so the recursion's row could hold only abortive
  operations;
- **an answering capability in a recursion**: the group's step is `!` code, a top-level `def`, and
  nothing passed it the capability;
- **members with different result types**: the group was one `bounded_fix[A, C]` with the members'
  arguments a sum and their answers one `C`.

And handler clauses (#216) are `!` code, so a handler could be given only `!` values.

One principle closes these at elaboration, with no kernel change: **effectful code is `!` code,
and its environment is passed to it at each call** (closure conversion at the seams; §2's `FnMut`
row; the environment a copy of a function with a row already takes, §18). It is not captured.
A recursive group is the **fixed point of a generator** (Cook and Palsberg), called directly; a
layer is a **transformer of the generator**; a clause of a handler receives its environment from
the handler's state, or runs after the handler. Decision 59; decision 24 revised.

### Recursive groups

A group with members `fⱼ : Pⱼ → Tⱼ` at the row `Σ`, copied for an environment `E` (the
capabilities its copy takes, §18: the answering effects' capabilities in the order of the row, and
the variable a `for`'s site threads), is the bounded fixed point of its **generator** at the record
of its members (Bekič):

    R = &ⱼ (E ⊗ Pⱼ ⊸ F_Σ (E ⊗ Tⱼ))                  (one member: its function type)
    gen : !U ((1 ⊕ !U(1 ⊸ R)) ⊗ 1 ⊸ R)               (`g__step__…`)

- **The generator** answers the record of the members' bodies, each taking `E` first and handing it
  back first, as a copy does. It is `!` code that holds nothing; when `E` has capabilities it is
  `!(∀'l₁ … 'lₙ. !U(…))` over their lifetimes.
- **A call of member `j` inside it** is a direct call of the self-reference:

      case self { inj₁ _ ⇒ abort[e.0] () | inj₂ g ⇒ (force (unbang g) ()).j (E, W) }

  with `E` bound again after, `e` the site of the exhaustion effect.
- **A member's copy** is `(bounded_fix[1, R] (gen, (budget, ()))).j`, at the budget `recBudget`. It
  has the type a copy of the member has, so a call of it from outside is a call of a copy.

So an answering capability flows through a recursion as part of its argument and answer, an
operation that resumes is performed by the recursion's own frames (nothing is cancelled around a
call of itself), and members answer different types. A recursive generator under a `for` threads
the `for`'s variables as its environment, its copy generic in their type.

**The kernel.** `bounded_fix[1, R]` is §20's constant at `A = 1` and `C = R`; `boundedFix_compatX`
is proved at every computation type, a record among them. The spike's `boundedFixEnv_compatX` and
`boundedFixRec_compatX` (`experiments/SecondClass/SecondClass/Restated.lean`) are instances of it.

### Layers: transformers of the generator

A **layer** is a function whose written type is `!(!(A => B) * A => B)`, `A` and `B` its two type
parameters (recognized by that structure, as a heap driver is by its type, §20):

    fn counted[A, B](call: !(A => B), a: A) -> B = tick(); call(a)

`with L { M }` drives the recursive groups `M` calls (lexically, as `with deep`) by `bounded` over
their generator transformed by `L`, before the fixed point is taken:

    T_L(gen)(self, u) = gen(wrap self, u)
    wrap (inj₁ u) = inj₁ u
    wrap (inj₂ g) = inj₂ (λ_. ⟨ λx. L's body at (Pⱼ, Tⱼ), its call(a) the member's call through g ⟩ⱼ)

- The transformer `L__g__…` is a `def`, applied in each member's copy:
  `bounded_fix[1, R] (T_Lₙ(… T_L₁(gen)), (budget, ()))`. Layers nest; the innermost runs first
  around a call.
- A call made by the recursion of itself runs the layer; the call from outside does not.
- The layer's row joins the row of a call of the group inside `with L`, and its capabilities join
  `E`: `call(a)` passes the environment, as any call of the group does. `call` can only be called.
- A copy's body is outside the layers in scope at its call (lexical, as `deep`).

### Handler clauses

**Abortive operations: the clauses run after the handler.** When every operation of a handler is
abortive, each clause runs at most once and never resumes, so (the derived rule
`d_handleAbortCapture` of the spike, as an elaboration):

    with h(e⃗) { M }  ≜  (p⃗, r) ← handle_n M with (λx. inl x, (λv. inr (inj_i v))ᵢ);
                       case r { inl x ⇒ N_ret | inr e ⇒ case e { … inj_i v ⇒ N_i … } }

- The site binds the arguments to the parameters `p⃗` before the body and answers them beside its
  own answer; the `case` runs in the scope of the `with`, so the clauses use the parameters,
  whatever their types, and the capabilities in scope, as any code there does.
- The `case` is annotated with the handler's answer type, which the typed elaboration knows once
  the handler's type parameters are matched: the site's `HInfo.after`, the type name `fx_res{n}`.
- `default(d)` takes an owned value `d` (`lib/fail.bc`).

**Operations that resume: the handler's state.** `k(v)` in a clause resumes its continuation:
`(force k).1 v`. A handler whose operations resume and that has a parameter not written `!`, or
whose clauses use a capability, has a **state** `S = S' ⊗ P`, the capabilities `S'` its clauses
use and its parameters `P` (`mut` parameters among them):

- the site answers `U(S ⊸ F_Σ (S' ⊗ R))`; the return clause and each clause answer a thunk of the
  state, which binds `S'` and `P`;
- `k(v)` applies the continuation's answer to the current state: the parameters are passed on, and
  the capabilities come back with the answer;
- after the site, its answer is applied to the initial state, the arguments and the capabilities.

**Not provided**, each rejected with a message: a capability used both by a resuming handler's
body and by its clauses (the handler holds it between operations); the continuation of a handler
with a state passed as a value; a clause that uses a `for`'s threaded variables.

### Lowering

- **Recursion.** `fixValue` as in §20; there is no `rec` site, so `Capture`'s rule for a clause
  that resumes under a cancelling finaliser (`unwindClause?`) is removed. `corpus/rec-fib.bc` stays
  at 0, 0, 0; `rec-parser.bc` falls from 22 allocations to 17.
- **Layers** allocate nothing (`corpus/rec-layer.bc`: the two cells only).
- **Abortive clauses after the handler** cost what the clauses did: every corpus program of `Fail`
  keeps its counts.
- **A handler with a state** applies a closure of the state at the start and at each resume: a
  dispatched call each (`corpus/clause-captures.bc`: 3, as the spike's P4(a)). A native handler
  parameter is not built (§19 *Open*).

### Programs

`corpus/rec-log.bc` (an answering capability through a recursion), `rec-yield.bc` (a recursive
generator under a `for`), `rec-emit.bc` (a clause that resumes in the middle of a recursion),
`rec-mixed.bc` (members with different result types), `rec-layer.bc` (two layers composed),
`clause-captures.bc` (an owned argument and a capability in abortive clauses; a handler with a
state); `corpus/reject/rec-loop.bc`; reports `corpus/reports/rec-*.txt`,
`clause-captures.txt`. `rec-overflow.bc` still unwinds a million-deep recursion with `live 0`.

### Baseline

No change to `CDerives`, the relation, the machine or the checker's rules. Every elaborated form
is typed by the existing rules (`bounded_fix`, `[handle]`, `[let]`); `fundamentalC`, `adequacyC`,
`fundamentalD` and `adequacyD` keep their statements and cover every elaborated program.

### Open

- **A recursion whose body loops.** Its members are div (§14), so the fixed point is taken at
  loops, which `bounded_fix` types at every computation type (the spike's P3). But the budget runs
  out inside a loop's observation, where `Exhausted` has no handler: a handler around a div
  computation is not provided for any effect (`with to_result { f(x) }`, `f` looping and raising,
  is rejected the same way). Rejected with that reason (`corpus/reject/rec-loop.bc`).
- A native handler parameter (§19 *Open*).
- **`memo`**, a layer, needs a map (#211) and a layer of its own state: an answering effect with
  type parameters (§18 *Open*).
- A layer over a recursion under `deep`; the heap driver's members with different result types.
- Effects under `deep` and generic recursion (§20 *Open*; separate, per the spike).
- Recursion through a site (decision 57's parser, `corpus/reject/rec-through-site.bc`): a level's
  own handler is a site per level, which static names cannot give (generative names, L2, #173).
  Recursion through values: a member passed as a value is a function with a row (#161).

---

## 22. Entry 21 — the affine closure: observations with arguments and a boxed rest

### Motivation

§2 wrote an affine closure (cf. Rust's `FnMut`) as `(env, !code)` behind a `Mut` borrow, the code
taking the environment `E` and handing it back. That form names `E`, so a function over such
closures is written once per environment type (#233; `docs/effect-polymorphism.md` R2a). The
experiment of #236 (`docs/fnmut.md`) found that two relaxations of §7's positivity make the affine
closure a codata type, its environment hidden by `ν`:

    Aff^c A B  ≜  νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1

No type former, typing rule or `CDerives` index is added. The same relaxation gives codata
observations that take arguments, as `docs/type-declarations-design.md` (#141) asks of `codata`
declarations.

### Positivity

§7's `NuOk` gains two shapes (`Core/Types.lean`):

- **An observation may take a closed argument.** An observation tree may be `A ⊸ D`, with `X` not
  in `A` (`A.Cl 0`) and `D` an observation tree (`CTy.NuLeaf`). `instT` passes through it.
- **The rest may be boxed.** `VTy.Poly` admits `[@a] B` over a polynomial `B`.

**Relation.** One unfolding at `A ⊸ D` is `cC`'s `⊸` clause, the argument read without the
type-variable environment, since `A` is closed (`cB`, `Core/Relation.lean`). It is monotone in
the candidate (`cB_mono`), one unfolding at the relation is the unrolling (`cB_unroll`), and it is
closed under steps and binds and agrees with stacks (`cB_step`, `cB_bind`, `cB_iff_stacks`,
`Core/Computation.lean`). `[@a] B` is the resource condition `@ρ ⊐ a` over `B` (`[TR]` p. 6), so
it is monotone too.

**Coiteration.** The node at `A ⊸ D` is `λx. node_D wr (λ_. c () x)`: the argument is passed on to
the step's computation (`nodeV`, `node_ok`, `Core/Nu.lean`). The map at `[@a] B` is the map at
`B`, because `[]I` and `[]E` are typing rules on the same term (`mapV`, `map_ok`).

Every body positive before is positive after, and `nuIn`, `nuOut` and `unfold` cover the new
shapes through these cases, with no new compatibility lemma.

### The affine closure

`Aff^c A B` above has two observations: `call` takes an `A` and answers a `B` with the rest of the
closure, and `close` ends it (`Core/Aff.lean`). A closure is a value of `U(Aff^c A B)`; one that
outlives `@c` is `[@c] U(Aff^c A B)`, the form in which it is stored, lent `mut` and returned,
and the rest every call hands back is of that form.

- **Positivity** at every closed `A` (`affBody_nuOk`), and at an argument that is itself a
  borrowed closure (`affBody_nuOk_higher`). An effectful closure,
  `νX. (A ⊸ F_Σ(B ⊗ [@c] U X)) & F_Σ 1`, is positive at closed operation types
  (`affEffBody_nuOk`).
- **Relation.** `cC_aff_iff`: a computation is an affine closure when every `call` answers a `B`
  and a rest that is again a closure outliving `@c`, and `close` runs to `()`; coinduction is
  `aff_coind`.
- **Observable view.** Unchanged: the observable view relaxes `U` to `True` (`vC_obs_aff`), and
  `Imm̲` takes the closure to `Unk` (`immReborrow_aff`, `immReborrow_affBox`), the paper's clause
  (4). A closure behind an `Imm` borrow is only forgotten; behind a `Mut` borrow it is held at the
  program's view and called by `withswap`. §12.69's `obs_transfer` takes its `U C` arm
  (`obs_transfer_affBox`).
- **Destructor.** §12's `HasDtor.nu`, class 2: dropping a closure runs its `close`
  (`hasDtor_aff`). It is not `Affine` (`not_affine_aff`) and not persistent (`not_persistent_aff`).

**Derived rules** (`Core/AffRules.lean`), each a `CDerives` derivation, so `fundamentalC` and
`adequacyC` cover them:

| rule | term | from |
|---|---|---|
| introduction | `mkE` over a state `s : S` and `!` code `step : S ⊸ (A ⊸ F(B ⊗ [@c] S)) & F 1` (`d_mk`) | `unfold`, `nuIn`, `&` |
| introduction outliving `@c`, when `S` does | the same (`d_mkBox`) | and `[]I` |
| call | `f π₁ a : F(B ⊗ [@c] U(Aff^c A B))` (`d_callAff`) | `nuOut`, `π₁` |
| close | `f π₂ : F 1` (`d_close`, `d_closeBox`) | `nuOut`, `π₂` |
| call through `Mut @a ([@c] U(Aff^c A B))` | `withswap` with the call as callback (`d_callMut`) | `withswap`, `[]E` |
| persistent ≤ affine | `mkE` at the state `!U(A ⊸ F B)` (`d_ofFn`) | the above |
| affine ≤ linear | `λa. call, then close the rest` (`d_once`) | the above |

A linear function has no destructor (`not_hasDtor_lolli`), so it is not the state of a closure
whose `close` must dispose of it, and there is no uniform linear ≤ affine coercion.

**Three kinds of function**, three types (cf. Rust's `FnOnce`, `FnMut`, `Fn`):

| kind | type | copy | drop | §12 class |
|---|---|---|---|---|
| linear | `U(A ⊸ F B)` | no | only by calling it | 3 |
| affine | `[@c] U(Aff^c A B)` | no | `close` | 2 |
| persistent | `!U(A ⊸ F B)` | yes | `forget` | 1 |

**Bounds.** A closure outlives `@c` when its state does (`d_mkBox`); a closure capturing
`Mut 'x T` is bounded by a lifetime below `'x`, never `'x` (`logState_not_outlives`), and no
closure outlives anything except through its box (`aff_not_outlives`). The box rule of outlives
is non-strict (§23), so a closure bounded by `'x` is lent `mut` inside `'x`'s own scope.

**Programs** (`Core/AffPrograms.lean`), each one closed `CDerives` derivation run by adequacy at
every host and by the interpreter: a counter called twice through `Mut` (`counterProg`, 4),
passed through `n` functions with a reborrow (`d_passF` at every `n`; `passProg 3`, 13), nested
(`nestProg`, 8), returned (`retProg`, 15), a logger capturing a borrow (`logProg`, 12), the two
coercions (`ofFnProg`, 23; `onceProg`, 5), and a drop by the destructor (`dropProg`, 0).

### The checker

`CTy.nuLeafB` admits `A ⊸ D` at a closed `A`, and `VTy.polyB` admits `[@a] B`
(`Frontend/Check/Decide.lean`, sound by `nuLeafB_sound`, `polyB_sound`); `nu_in` finds the `ν`
type through an argument. A `type` declaration may take type and lifetime parameters,
`type N[T, …]<'a, …> = A`, and a use `N[A, …]<'b, …>` elaborates the arguments at the use and the
body in the declaration's scope with the parameters bound to them (`Frontend/Check/Elab.lean`):
substitution, with no kernel change (`docs/type-declarations-design.md` §4.1–4.2, `type` with
parameters). A template's type parameters under a `μ` or `ν` binder are shifted past it, so a
call matches a parameter of type `Aff[A, B]<'c>`.

### The library

`lib/aff.bc` (`include aff`) declares the closure and its operations:

    type Aff[A, B]<'c> = U (nu X. (A -o F (B * box 'c U X)) & F 1)

`aff_new` (a state and its step; the caller boxes it, `boxed['c] aff_new(s, step)`, at the
state's type), `aff_new_boxed` (the same, boxed by the function itself under the bound `S: 'c`,
§23), `aff_call`, `aff_call_mut` (through `mut 'a (box 'c Aff[A, B]<'c>)`),
`aff_close`, `aff_of_fn` (persistent ≤ affine) and `aff_once` (affine ≤ linear). The name `Aff`
is provisional (decision 60).

### Lowering

Nothing new: `unfold` is a closed λ-term, and its node at an argument is one more λ. A closure
built under `boxed` keeps its unfolded code `!`, so its thunk's arms bind the code to a name
first (`g <- return (unbang f); …`); `Backend/Clos/Collapse.lean` builds such a thunk eagerly as
it does the unbound form, so a closure has one code and its calls through `mut` are direct calls
(`corpus/counts.expected`, `aff-counter`, `aff-depth`: no indirect call).

### Programs

| program | what it shows |
|---|---|
| `corpus/aff-counter.bc` | a closure owning a cell, stored in a cell, called twice through `mut`; the state persists |
| `corpus/aff-depth.bc` | the borrowed closure passed through three functions, with a reborrow |
| `corpus/aff-higher.bc` | a closure capturing a closure, and a closure taking a closure |
| `corpus/aff-capture.bc` | a closure capturing `mut 'x i32`, returned from its maker, bounded by `'w ⊏ 'x` |
| `corpus/aff-drop.bc` | closures dropped by their destructors, which close them and free their cells |
| `corpus/aff-coerce.bc` | persistent ≤ affine and affine ≤ linear |
| `corpus/reject/aff-outlives.bc` | refused: a closure bounded by the lifetime of the borrow it captures |
| `corpus/reject/aff-copy.bc` | refused: an affine closure used twice |
| `corpus/reject/aff-linear-state.bc` | refused: a linear function as the state a `close` drops |

### Instances

`Aff^c A B` is the only abbreviation that uses the new shapes. §7's `Loop`, `D`, `Stream` and
`Iter`, and the frontend's `delay`, `stream`, `iter`, `loop` and `pull`, were already instances of
`νX. C` and stay as they are; replacing the frontend's five with library declarations is #141.
§2's closure row is now the type above, and nothing replaced is left to delete: the relaxation
generalises `NuOk` itself, whose earlier trees are its special case, and the `(env, !code)` form
remains the derivation of `d_callMut` (a `withswap` over the closure).

### Baseline

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`, the totality theorems and every result
of entries 1–20 keep their statements and proofs; nothing in `Paper/` or `Support/` changes. The
axioms are `[propext, Classical.choice, Quot.sound]`.

### Open

- **A lifetime-polymorphic argument**, `∀'a. Mut 'a T ⊸ F(B ⊗ [@c] U X)` (cf. Rust's
  `FnMut(&mut T)`): `∀` in observation trees, where `cB` would change `δ` under a candidate fixed
  at one `δ`. An argument's lifetimes are fixed when the closure's type is written.
- **An argument mentioning `X`** (a sink of the codata itself) stays outside `NuOk`.
- **Surface closure sugar**: a closure over a context elaborated to `aff_new` with the captures as
  the state and their destructors as `close`.
- **Strict outlives**: §23 relaxes the box rule and `withbor`'s side condition, gives `main` a
  lifetime of its own, and bounds a template's lifetime by its type parameters.
- **Polyvariant flow.** Closures built at two sites that reach one call are dispatched there
  (`aff-higher`).
- **Linear ≤ affine** is refused by inspection of the derived rules, with `not_hasDtor_lolli` its
  mechanical part; a parametricity statement is not made.
- A generic function's lifetime parameters are unrelated to the lifetimes in its type arguments
  unless a bound relates them (§23, `where S: 'c`); `aff_new` returns the closure unboxed, and
  `aff_new_boxed` is the bounded constructor.

---

## 23. Entry 22 — non-strict outlives: the box rule and `withbor`'s side condition; lifetime bounds and `main`'s lifetime

### Motivation

BoLo prints `⊏` in every outlives premise ([TR] p. 2, rows 2.35–2.37). Two of those premises
cost programs a scope each and protect nothing the model needs (`docs/outlives-strictness.md`,
#241): the box rule of `Δ ⊢ T ⊐ @a`, and the side condition of `withbor` (Ref → Mut). Relaxing
them to `⊑` is an **extension** of the calculus, read against the model the paper defines, as
§4 (Entry 3) is; it is not a correction of the paper, and `Paper/` is unchanged. Two
elaborations, with no judgment change, remove the rest of the cost in the `aff-*` programs: a
lifetime of `main`'s own, and lifetime bounds on the type parameters of a generic function. (#243
calls the four K1, K2, E1 and B1.)

### The outlives judgment

`VOutlivesR Rb Rr` (`Core/Types.lean`) is `[TR]` p. 2's outlives judgment with the box rule's
lifetime premise `Rb @b` and the `Imm`/`Mut` rules' premise `Rr @b`. It has two instances:

- `VOutlives Δ a` (`Δ ⊢ T ⊐ @a`), with `Rb = (Δ ⊨ @a ⊑ ·)` and `Rr = (Δ ⊨ @a ⊏ ·)`;
- `VOutlivesLe Δ a` (`Δ ⊢ T ⊒ @a`), with `⊑` at all three rules.

Every `VOutlives` derivation is a `VOutlivesLe` one (`VOutlives.toLe`). `rename`, `subst` and
`unroll` are proved once, at `VOutlivesR`.

### The box rule

`VOutlives`'s box rule is `[@b] T ⊐ @a` from `Δ ⊨ @a ⊑ @b` (was `Δ ⊨ @a ⊏ @b`). A value of
`[@b] T` has its resource in `Res_β`, and `Res_β ⊆ Res_α` for `α ⊑ β`, so 6.60 (`vC_outlives`,
`Core/RelationFacts.lean`) holds with the box case at `α ⊑ β`; every other consumer of
`VOutlives` reads it through 6.60 or passes it on. `Core/Embedding.lean` maps 2.35's strict
premise to the non-strict one (`entailsLe_of_entailsLt`). The checker's `outlivesB` takes `leB`
at a box (`Frontend/Check/Decide.lean`).

The box modality itself stays strict: `[@x] T` is membership in `Res_x`. So `[@x] T ⊐ 'x` holds,
and a closure bounded by `'x` is lent `mut` inside `'x`'s own scope; `Mut 'x T ⊐ 'x` stays
refused, and a closure capturing `mut 'x T` is still bounded strictly below `'x`
(`corpus/reject/aff-outlives.bc`).

### `withbor`'s side condition

The side condition of the borrows that lend a payload `mut` is `∃ @b. Δ ⊨ @b ∧ Δ ⊢ A ⊒ @b`
(was `Δ ⊢ A ⊐ @b`), at every rule that carries one: `withbor2` and `withbor2U`, and the slice
borrows `sliceBorrowM`, `sliceBorrowI`, `sliceBorrowMU` and `sliceBorrowIU` at both their payload
and their result (`Core/Fundamental.lean`). The family borrows (`Family.borrowsMut`) and the
block borrows (`BlockBorrow.formerMut`) are derived from `withbor2` and take it with it.

The condition reaches each proof through 6.60, as `𝒱⟦A⟧δ ⊧ [@bδ] 𝒱⟦A⟧δ` ([TR] 6.173), and the
frame rule uses it only to put the payload (and, at a slice, the result) in a stratum that its
own fresh lifetime lies below. At `VOutlivesLe`, 6.60 gives every stratum strictly below `@bδ`
(`vC_outlivesLe`), and the frame is taken at `↓@bδ` (`withbor2_compatX`, `Core/Compatibility.lean`;
`sliceBorrowM_compatX`, `sliceBorrowI_compatX`, `Core/Slices.lean`; the unwinding forms,
`Core/EffBorrow.lean`). The checker decides `VOutlivesLe` with `leB` at all three rules
(`outlivesLeB`), and `outlivesWitness` uses it.

### `main`'s lifetime

`main` runs under a lifetime of its own, written `'main`. Its body is elaborated once, with
`'main` in scope, inside a `mut` borrow of a unit cell allocated before it and freed after
(`mainLife`, `Frontend/Sugar.lean`); the standard capabilities the body lends are handed back
beside its result, as a borrow block hands back what it lends. A body whose elaboration names no
`'main` (`Comp.mentionsLife`, `Frontend/Elab/RenameLife.lean`) is left as it is, since the borrow
is then not observable. A body that names it has the
type `F A`.

A lifetime argument that a call of a function does not determine, from its arguments or the type
expected of its result, is `dom`: the meet of the lifetimes in scope, so at least `'main` in
`main`'s body. Outside `main`, a call with no lifetime in scope and a lifetime left undetermined
is an error, as before.

So a library function's lifetime parameter, bounded by `top`, is instantiated at a lifetime the
program has without a scope of its own, and by the box rule a closure bounded by it is stored and
lent `mut` in `main`'s body.

**Cells of no words.** `'main` costs nothing at run time, and the mechanism is general: a cell
whose cell class takes no words (every contents it holds is `1`, or a closure capturing nothing)
is not allocated, its address is `0` and never read or written, and `free` frees nothing
(`zeroCell`, `Backend/Flat/Lower.lean`). This is a change of representation in the backend only;
the source semantics, the interpreter and every golden's output are unchanged.

### Lifetime bounds on type parameters

    fn f[S, …]<'c, …>(…) -> T with … where S: 'c, … = …

A bound `S: 'c` names a type parameter and a lifetime parameter of the function. At an instance
whose type argument for `S` mentions the lifetimes `'q₁ … 'qₙ` (each a lifetime parameter of the
instance, §15 *Generic functions*), the instance's binder of `'c` is
`all 'c < @ /\ 'q₁ /\ … /\ 'qₙ.` (and `Fun 'c < …` around its body), where `@` is the bound
written for `'c` (`'q₁ /\ … /\ 'qₙ` alone when `@` is `top`). With no lifetime in `S` the bound is
unchanged. This is a different bound at the kernel's existing `∀'c ⊏ @b`, so the instance is
checked by the unchanged checker, and `S ⊐ 'c` is checked there, at the instance's types. A
caller instantiates `'q̄` with its own lifetimes and `'c` with one strictly below their meet,
which `allE` asks of it (`corpus/reject/aff-bound.bc`). The bounds are kept with the template
(`Mark.template`) and printed with it, `fn def f[S, …] where S: 'c : A = V`. `where` is a word
in that position, not a keyword.

`lib/aff.bc` declares `aff_new_boxed[S, A, B]<'c>(s: S, step) -> box 'c Aff[A, B]<'c> where
S: 'c`, which boxes the closure and every rest itself, and `aff_of_fn` is built on it.

### Programs

| program | what it shows |
|---|---|
| `corpus/aff-counter.bc`, `aff-depth.bc` | the closure stored and lent `mut` in `main`'s body, under `main`'s lifetime; built with `aff_new_boxed`, with no `boxed` |
| `corpus/aff-drop.bc`, `aff-higher.bc` | a closure over a closure, bounded by the same lifetime as the closure it holds |
| `corpus/aff-coerce.bc` | the coercions at `main`'s lifetime |
| `corpus/aff-capture.bc` | `logger`'s `'w < 'x`, filled with `dom`, gives `aff_new_boxed`'s bound; its scope `'w` stays (the `Mut` rule) |
| `corpus/main-lifetime.bc` | `'main` by name, and cells of `1` that allocate nothing |
| `corpus/borrow-in-scope.bc` | a cell holding `imm 'x i32` lent `mut` inside `'x`'s own scope (the side condition) |
| `corpus/reject/aff-outlives.bc` | still refused: a closure bounded by the lifetime of the borrow it captures |
| `corpus/reject/aff-bound.bc` | refused: a lifetime bound's instance called at a lifetime not below the type argument's |
| `corpus/reject/generic-lifetime-unknown.bc` | refused: a lifetime left undetermined where no lifetime is in scope, outside `main` |

Across the six `aff-*` programs, the scopes opened only to name a lifetime go from 10 to 1, the
cells written for them from 6 to 1 (`aff-capture`'s, a unit cell), and the `boxed[…]` annotations
from 18 to 4. Each program allocates one object fewer than before (`corpus/counts.expected`).

### Baseline

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`, the totality theorems and every result
of entries 1–21 keep their statements; the proofs change at 6.60's box case, at the derivations
that supply a side condition (now `.toLe`), and at the side condition's consumers. Nothing in
`Paper/` or `Support/` changes. The axioms are `[propext, Classical.choice, Quot.sound]`.

### Left as printed

- The `Imm`/`Mut` rules of the outlives judgment where `[]I` reads them: 6.60 fails with them
  non-strict, since a borrow's own cell is in the relation and not in `Res_α`
  (`experiments/Outlives`, `not_vC_outlives_le`).
- The model's strata and the box modality: a stratum whose `mut` cells sit at its own lifetime
  contains its own predicates (`no_nonstrict_stratum`).
- The fresh lifetime `'x ⊏ ⊓Δ` of `withbor` and `withload`: a hypothesis the callback receives.

### Open

- **A non-strict `∀` binder**, `∀'a ⊑ @b`: a second binder kind in `LifeCtx` and `Models`. A
  lifetime bound is strict, so a closure whose state is a closure bounded by `'c` is built with
  `aff_new` and `boxed['c]` (`aff-drop`'s `nest`, `aff-higher`'s `doubler`).
- **A lifetime without a cell.** `main`'s lifetime, and `aff-capture`'s scope below `'x`, are
  borrows of a unit cell, which costs nothing at run time but is written; a rule that opens a
  lifetime without one was not probed.

---

## 24. Entry 23 — the polymorphic let, the general `[handle]`, and `[then]` at option A

### Motivation

Decisions D3 and D5 (2026-10-07). Tier 1's typing needs three things today's rules lack:

- **a let-bound function used at several rows** (effect polymorphism: the targets E1, E2, E6 and
  E10). A context slot has one type, so a variable is read at one row;
- **a handler whose clauses are values**. The run-time handler frame `hnd (n, (h_ret, hs)) □`, with
  its clauses as values, is the form a deep handler takes in every evaluation context, and §19's
  printed `[handle]` types it; as built, `[handle]` took its clauses as variables only;
- **a finaliser that lets no raise escape** (option A): S5's endings are parameterised by the labels
  whose raises a finaliser may let escape, and the target reads the empty set.

### Typing

    ⊢ λy. b : j    (closed)        Δ; x̸, Γ ⊢ N[λy. b / x] : C
    ────────────────────────────────────────────────────── [let-poly]
    Δ; Γ ⊢ let x = λy. b in N : C

- `x̸` is `x`'s slot, dead; `N[λy. b / x]` is `N` with the λ-value for `x` and every other variable
  where it was (`(N.subst 0 V).shift 1 0`).
- Each occurrence of the λ-value in `N` is typed on its own, at its own row (or lifetime, or type).
  Terms carry no rows, so this is let-polymorphism by substitution: one closed function used at as
  many rows as it has occurrences. The value restriction holds: only a closed λ-value is bound.
- The term is the let itself, `(λx. N) (λy. b)`; the rule adds no term former and no type former.
- Core's types have no row variable: a function used at several rows is let-bound and typed at each
  occurrence. Tier 1's typing has a row `∀` in its open types, outside Core, and reads it through
  this rule.

      Γ = Γ₁, Γ₂    Γ₁'s live slots persistent    H a value form over Γ₁
      Δ; Γ₁ ⊢ H : !U(A ⊸ F_Σ R) ⊗ ⊗_i C_i       Δ; Γ₂ ⊢ e : F_{Σ, n : E} A
      ──────────────────────────────────────────────────────────────── [handle]
      Δ; Γ ⊢ hnd (n, H) e : F_Σ R          (n ∉ Σ, n ≠ 0)

- §19's printed rule, as built. A **value form** is a value, a variable of a live slot, or a pair or
  injection of these (`Expr.ValFormIn`): a closing substitution makes it a value, so the frame is a
  handler before `e` runs. The clauses are `!`, so their context is persistent.
- The former rule, `h_ret` and the clauses as two variables, is its instance (`CDerives.effHandle`,
  a theorem with the constructor's former statement): the pair of two variables is a value form, and
  its slots are persistent.

      Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_Σ A    Δ; x : A, Γ₂ ⊢ N : F_Σ B    Δ; Γ₂ ⊢ D : F 1
      ──────────────────────────────────────────────────────────── [then]

- The finaliser is at the pure row: it handles its own raises, and none escapes it. A program
  whose finaliser lets a raise escape is no longer typed; the corpus has none. The machine is
  unchanged (§19's *Cancels* and *Finalisers that perform operations*).
- **Superseded by §27**, whose `[then]` types the finaliser at its own row. This rule stays as a
  derived rule (`CDerives.effThenA`), its unrestricted premise read at some depth.

### Semantics

No change to the machine, the relation, `wpTS`, `wpG` or `ewpTS`.

- `[let-poly]` (`letPoly_compatC`, `Core/PolyLet.lean`): the let takes one β-step, which allocates
  nothing, to `N` with the λ-value for `x` (`cC_head`); closing that term with the λ-value at the
  dead slot is closing `N` at the λ-value (`psub_fill`).
- `[handle]` (`handleV_compatC`, `Core/EffFin.lean`): `H` closes to a value; its relation is read
  off `wpTS` at that value, under the frame the handled run starts in (`wpTS_val_post`: the run from
  a value takes no step); at the persistent types `retTy` and `clausesTy` it holds at `∅`; the
  handler is then `ewp_handle` at clause values (`ewp_handle_vals`), which `handle_compatC` now
  also reads.
- `[then]` (`then_compatC`): the finaliser at the pure row, so a cancel through the frame keeps no
  error. Since §19's dead regions, the rule with the finaliser at `F_{Σ^abort} 1` does not hold:
  at `prog`'s `[then]` its premises hold and the cancel it owes keeps an error the canceller's row
  does not have (`not_thenAbort_compatC`, `Core/EffCancel.lean`).

### Lowering

The backend's codes are monomorphic: what a code may raise and suspend with fixes the convention it
is called by (§19 *Lowering*), and the closure flow gives a code every value any of its uses passes
it. A `[let-poly]` let whose uses are at one row is lowered once, as any let. One whose uses are at
different rows is lowered per use: it is converted as its β-reduct, the closed λ at each use (the
step `letPoly_compatC` reads, which allocates nothing), so each use is a code of its own at its own
row, and a use that applies the λ is a `let` of its argument, with no closure and no call
(`Backend/Clos/Poly.lean`). This is monomorphisation, as Rust instantiates a generic function per
closure type: no use dispatches, allocates, or answers for another use's effects.

- **A use's row** is what the lowering's analysis finds of it when every such let is converted as
  its β-reduct, each use marked: the operations each code the use makes may suspend with and the
  keys it may raise, and the same of every closure that code may be given, answer or capture, at
  any depth, in pairs, sums and cells. The uses of one instance of a let are at one row when these
  agree code by code.
- A program whose lets are each used at one row is converted as it is written; the corpus's
  programs are.
- `hofTwoRows`, `sumGen` and `timeoutProg` (§19 *Programs*) are the kernel programs
  `hof-two-rows`, `sum-gen` and `timeout`, and `poly-id` is `λf. f` let-bound and used at two
  rows that differ only in what it answers. Each runs with no allocation, no dispatched call and
  no deep copy (`corpus/kernel-counts.expected`).

### Theorems

- `fundamentalC`, `adequacyC`, `adequacyD`, `adequacyD_obs` and every compatibility lemma keep
  their statements, over the extended judgment.
- `CDerives` gains `letPoly` and `effHandleV`, loses the constructor `effHandle` (now the theorem
  `CDerives.effHandle`), and `effThen`'s finaliser premise is at `F 1`. No new index.
- S5 holds at every instance of its parameter, a finaliser that lets the raises of some names
  escape, not only at the empty set: `unwind_prefix` and `cancel_prefix` at `FinRow` (§19 *Laws*
  items 5 and 6).
- `[let-poly]` types a closed λ let-bound once and used at several rows: `hofTwoRows` (E1),
  `sumGen` (E2d) and `timeoutProg` (E10), each with a use at the pure row and one under a handler of
  `exn` (§19 *Programs*). The premise's term, the body with the λ at each use, is computed
  (`threeUses_subst`, `sumGenUses_subst`, `timeoutUses_subst`); it is the term the backend compiles
  (*Lowering*).
- **The copy is the premise.** A term holding a closed λ-value at some of its places is
  `[let-poly]`'s premise term for the let that binds the λ-value once. With the bound slot dead in
  front, a derivation of the term is one of the premise: weakening by consumed slots inside a
  context (`CDerives.insert_dead`, `CDerivesAt.insert_dead`, `Core/InsertDead.lean`), so the let
  has a derivation (`CDerives.letPoly_of_fill`). The let's body is the term with the λ-value's
  occurrences replaced by the bound variable (`Expr.unfill`), whose filling is the term
  (`subst_unfill`): `CDerives.letPoly_copy`, and `CDerivesAt.letPoly_copy` for a tied derivation
  (`Core/LetCopy.lean`). The copies of `hofTwoRows`, `sumGen` and `timeoutProg` unfill to their
  lets' bodies (`threeUses_unfill`, `sumGenUses_unfill`, `timeoutUses_unfill`). The checker's
  copies are such terms (§18 *Rows*): a checked program's derivation gives the let's
  (`checkProgram_letPoly`).

### Baseline

`Paper/`, `Support/`, the machine, `cC`/`vC` and the effectful `wp` are unchanged; no borrow rule
and no borrow lemma changes. The checker (`Frontend/Check/`) types a finaliser at `F 1`: the drop
glue (§12's destructors) already was. The checker does not emit `[let-poly]`: it checks a `def` at
each use, which is the rule's premise term, and a checked program's derivation gives the rule's
derivation of the let (`checkProgram_letPoly`). No program from source has a let used at two rows
(*Open*).

### Open

- OQ-7 (finalisers that resume, or clean up asynchronously).
- **One function at two rows, from source.** The effect properties E1, E2d and E6 use a function
  whose row is its callback's: `hof`, `sumGen` and `fwrap` (§19 *Programs*). The surface rejects
  a closure that performs an operation where it performs, and a function with a row passed as a
  value where it is passed (§18 *Not provided*, effectful callbacks, #161); a generator that also
  raises is not stored (§15 *Open*). The core text writes a λ's binder with its type, the row
  included, so a let-bound function has one row there. The kernel programs `hof-two-rows`,
  `sum-gen` and `tunnel` are the three as Core terms; at the surface they are the pending programs
  `corpus/pending/effects-hof-two-rows.bc`, `effects-sum-gen.bc` and `effects-tunnel.bc`.
- **A let-bound function used at different value types.** The lowering specialises per row
  (*Lowering*): a `[let-poly]` let whose uses are at one row but at different value types
  (`λx. x` at `I32` and at `1`) is lowered once, and the layout types (`Backend/Clos/Types.lean`)
  reject it. §18's elaboration instantiates a generic function at each type (decision 45), so no
  checked program has one.
- **A let used at one row with different closures** is lowered once, as decision 57's default has
  it (one body per row, specialising per callback an optimisation): its calls of them dispatch,
  where Rust would instantiate per closure type. `let f = λg. g () in (f (λ_. tt), f (λ_. ff))`
  makes two dispatched calls. Specialising on the closures a use carries as well would also split
  the lets of the corpus's generators, whose uses carry different closures at one row.

## 25. Entry 24 — the capture cell: a linear or affine continuation owns a unit cell

### Motivation

Decision S6 (2026-10-08). Tier 1's soundness property S6 asks
that a continuation caught at a linear or affine operation be used as often as it was caught, and a
linear one never be cancelled. BoLo's linearity is linearity of resources: no `own` cell is leaked.
A `κ` held no resource of its own, so a run that drops it, resumes it twice or cancels a linear one
left the memory as a correct run would, and Core's relation could not tell them apart. This entry gives each such `κ` a resource: a
unit cell, allocated by the ordinary allocator and freed when `κ` is used. It changes no BoLo
definition: the cell is an `own` cell, and BoLo's leak freedom and safety see the three runs above.

### Terms and machine

- **The handler value** is `(n, (qs, (h_ret, hs)))` (`hndVal`). `qs` is a right-nested tuple of
  tags, one per operation at the operation's index: `0` linear, `1` affine, `2` unrestricted
  (`capTag qs i`, `2` where there is none).
- **`[op]`** hands the clause `κ` by the operation's tag `t` (`kappaAt`):
  - at `t = 2`, §19's `κ` (`kappa`);
  - at `t ∈ {0, 1}`,

        κ = (λc. λs. case s { inj₁ u. u; free c; λy. hnd (n, (qs, H)) K[y]
                            | inj₂ u. C }) (alloc ())                       (`kappaCell`)

    with `C = u; free c; ccatch (K†[raise (⊥, none)])` at `t = 1` (`K†` the dead region, §19) and
    `C = () ()`, a term with no step, at `t = 0`.

  The `[op]` step itself keeps the memory. The clause's argument then evaluates `alloc ()`, an
  ordinary allocation (the allocator's location, `ARun`), and `κ` is `kappaC` at the cell `ℓ`.
- **Using `κ` frees its cell** as soon as the branch is chosen: `κ (inj₁ ())` frees `ℓ` and answers
  `λy. hnd (n, (qs, H)) K[y]`; at `t = 1`, `κ (inj₂ ())` frees `ℓ` and cancels.
- So a run that drops `κ` ends with its cell allocated; a run that uses `κ` twice frees `ℓ` twice,
  which has no step unless `ℓ` was allocated again in between (never, under an allocator that does
  not reuse); a run that cancels a linear `κ` reaches `() ()`, which has no step.

### Typing

`[handle]` writes its effect's qualifiers into the term (`hndExpr n (map fst E) H e`, and
`hndTerm` at two variables): `handle_n e with H ≜ hnd (n, (qualsVal (map fst E), H)) e`. No rule
changes otherwise, and `CDerives` has the same indices. The checker emits the same tags
(`Frontend/Check/Rules.lean`, `rEffHandle`).

### Semantics

No change to `wpTS`, `wpG`, `ewpTS`, `opTable`, `contShare`, `KapRel` or the relation.

- `ewp_handle` takes the handler's tags and the hypothesis that each operation's tag is its
  qualifier's; `ewp_handle_vals` discharges it at `[handle]`'s tags (`capTag_ofEff`).
- At a linear or affine operation, the clause runs after the cell's allocation (`ewp_kappaCell`,
  from 6.141 through `ewp_alloc`), and `κ`'s relation `KapRel` holds of `kappaC` at the
  continuation's share and the cell: resuming frees the cell, then runs `hnd H K[w]`
  (`ewp_kappaC_resume`, from 6.142 through `ewp_free`); at an affine operation cancelling frees
  it, then cancels (`ewp_kappaC_cancel`). A linear `κ`'s cancel branch is at `⊤` in `kTy`, so
  `KapRel` asks nothing of it.

### Theorems

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`, `adequacyD_obs` and every compatibility
lemma keep their statements; `handle_compatC` and `handleV_compatC` are at the term with its tags.
The acceptance programs run as before, every cell freed (`Core/EffPrograms.lean`, the interpreter's
runs by `decide`); every kernel program prints the same value and `live 0` at the source and at every
compiled stage (`scripts/compile-kernel.sh`).

The machine's laws at the cell are §19 *Laws* item 1 (`Core/EffMachine.lean`). The catch of a
linear or affine operation allocates `κ`'s cell at a free location and hands `kappaC` there
(`catch_cell`), and every run from the catch that takes two steps has allocated the cell
(`catchEv_cell`): such a catch does not keep the memory. Resuming `κ` and an affine `κ`'s cancel
release the cell (`kappaC_resume`, `kappaC_cancel`); on a run to a value a use of `κ` releases it
three steps later (`use_frees_cell`); a linear `κ`'s cancel branch has no step
(`kappaC_cancel_lin`).

### Lowering

The backend builds `κ` itself (`Backend/Clos/Capture.lean`, `Kap`) and never sees the cell; it
reads past the tags (`Backend/Clos/Convert.lean`). A cell holding `1` takes no words, so it would
allocate nothing if it were lowered (`zeroCell`, §23). The kernel and corpus counts are unchanged.

### Baseline

`Paper/`'s machine changes in §19's rows only: the handler value, `[op]` and its `κ`. No BoLo row,
no `[TR]` lemma and no borrow rule changes; the cell is handled by 6.141, 6.142, `TW.alloc` and
`TW.free`. `Support`'s interpreter follows the machine. The untyped kernel shapes
(`Backend/Kernel.lean`) carry no tags, so their continuations are unrestricted, and
`Core/EffCancel.lean`'s handlers are unrestricted.

### Open

- **S6 at tier 1's typing**, from the cell: reduced to `LiveOK`, leak freedom and two ownership
  properties of the cell, open. `LiveOK` and leak freedom are Core theorems (`liveOK_closed`,
  `leakFree_closed`; §19 *Laws*, *Safety*), and so are the two machine facts the reduction reads: a
  capture event allocates `κ`'s cell (`catchEv_cell`), and a use of `κ` releases it three steps
  later (`use_frees_cell`). The reduction itself is not yet a Core theorem. The typing's side is:
  a clause that drops `κ`, uses it twice, or cancels a linear one has no derivation
  (`refuses_R_clauses`, §19 *Laws* item 4).

## 26. Entry 25 — a λ whose binder is dead, at an effectful returner

### Motivation

Decision E (2026-10-08). Tier 1's expressiveness properties state their schemas over every
callback body: a closed computation `M` at `F_Σ B` is passed
as the callback `λ_. M`, which the higher-order function calls at `()`. As built, Core types
`λx. M` at `1 ⊸ F_Σ B` only by `[λ]`, with `x`'s slot live. `M` does not use `x`, so a leaf of
`M`'s derivation must drop the slot, and the rules with a `!Γ` premise (`!`-promotion of a thunk;
`[let]` and `[then]` at a row with an unrestricted operation) take a context whose live slots are
all `!`: a live slot of `1` is not one. `thunk M : U (F A)` takes `M` under a dead binder, at the
pure returner only.

### Typing

    Δ; x̸, Γ ⊢ M : F_Σ B
    ───────────────────────── [λ-dead]
    Δ; Γ ⊢ λx. M : 1 ⊸ F_Σ B

- `x̸` is the binder's slot, dead: `M` does not use it. The argument is a value of `1`, which holds
  no resource.
- It is `thunk M`'s dead binder at an arrow from `1`, at every row. The term is the λ itself; no
  term former, type former or index is added.

### Semantics

No change to the machine, the relation, `wpTS`, `wpG` or `ewpTS`.

- `[λ-dead]` (`lamDead_compatC`, `Core/Fundamental.lean`): a live slot of `1` holds only the empty
  resource (`gSepC_cons_persistent`), so the context relation at `x : 1, Γ` gives the one at
  `x̸, Γ` (`gDenC_dead_cons`), and `[λ]`'s `lam_compatC` applies.

### Theorems

`fundamentalC`, `adequacyC`, `adequacyD`, `adequacyD_obs` and every compatibility lemma keep their
statements, over the extended judgment. `CDerives` gains `lamDead`. The callbacks of §19
*Programs*' effect properties, `λ_. M` for a closed `M`, are typed by it (`dAt_cb`,
`Core/EffTier1Programs.lean`), and so is every such callback the checker meets (*Baseline*).

### Baseline

`Paper/`, `Support/`, the machine, `cC`/`vC` and the effectful `wp` are unchanged; no borrow rule
and no borrow lemma changes. The checker emits the rule for `fun (x : 1) -> M` at `1 -o F_Σ B`
whose body does not use `x`: the body is checked under the binder's slot as before, and the slot is
closed dead (`lamIt`, `rLamDead`, `TiedDer.lamDead`, `Frontend/Check/`); otherwise `[λ]`. The term
is the λ either way, so every program erases as before. A callback whose answer is a `!` promotion
is accepted where it was rejected: under `[λ]` the binder is live, and the promotion's `!Γ` premise
does not take a live slot of `1` (`corpus/core-callback-dead.bc`, counts `0 0 0`).

### Open

- **Weakening by an unused live slot of a persistent type**, as a derived rule of the kernel: not
  derived. A direct induction meets the `!Γ` premises above.

## 27. Entry 26 — finalisers with effects: cancel rows

### Motivation

Decisions D2 and D3 of 2026-10-08 (D1 is §19's frame deadness). A finaliser may raise and perform
operations of names with a live instance outside every region that can cancel it (D2); a raise or
operation of a name with no live instance there is a type error (D3). Under §24's option A a
finaliser is at `F 1`.

The check cannot live in `[then]`. `e7b 1 2 = toResult 2 (timeoutH 1 (bodyF 1 (raise 2)))` and
`e7c 1 2 = timeoutH 1 (toResult 2 (bodyF 1 (raise 2)))` hold the same `[then]` subterm at rows with
the same entries, and D3 accepts the first and rejects the second (`not_der_e7c`, *Programs*). What
decides is the row of the code that cancels, which is visible where `κ`'s cancel branch is used. So
each operation whose continuation may be cancelled records what that cancel may do, its *cancel
row*; the record is carried outward through function types and `[sub]`, and checked where the
cancel is invoked.

### Typing

- **Cancel rows.** A row entry is `⟨n, i, q, A, B, F⟩` (`OpSig.fin`), and `F_Σ A`'s layers are
  `CTy.eff n i q A B F C`. An entry is *capturable* when it is not abortive and `q ≠ lin`
  (`capB`): its `κ` has a cancel branch, and `F` is read only there. A cancel row is `⊤`
  (`CTy.top`) or a row, its layers `F.rowOf`, whose capturable entries carry cancel rows in turn:
  a finite tree. The default is the empty row (`F 1`), and every existing derivation uses it.
- **Order** (`FinLe`, `OpSig.LeF`, `RowLe`). `F ≤ ⊤`; `R ≤ R′` when each entry `R` finds is the
  one `R′` finds at its key (`n i q A B` equal), with its cancel row `≤` at a capturable entry.
  `[sub]` is this order: an entry's cancel row only grows outward.
- **`F ⋈ E ≤ T`** (`ThenLe`), where `F` is the cancel row of a continuation captured below a
  finaliser whose row is `E`: `T = ⊤`, or `F ≠ ⊤` and
  - each entry `x` of `F` is `T`'s at its key, its cancel row `x.fin ⋈ E ≤ T(x).fin` at a
    capturable `x` (a nested cancel below the finaliser fires it too);
  - each entry `z` of `E` is `T`'s at its key, its cancel row `pend (aborts F) z.fin ≤ T(z).fin`
    at a capturable `z` (`PendLe`: a cancel of the finaliser's own continuation passes the `cfin`
    that keeps an error of `F`'s abortive entries, and those errors are `T(z).fin`'s, at every
    depth).

  Both are relations, defined by recursion on the depth of `F` (`G`).
- **`[then]`**:

      Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_{Σ_M} A    Δ; x : A, Γ₂ ⊢ N : F_Σ B    Δ; x̸, Γ₂ ⊢ D : F_{Σ_D} 1
      Σ_M ≤ Σ    Σ_D ≤ Σ    for every capturable o of Σ_M:  Σ_M(o).fin ⋈ Σ_D ≤ Σ(o).fin
      (Σ has an unrestricted operation at some depth ⇒ !Γ₂)
      (Σ_D has an unrestricted operation at some depth ⇒ Σ_M's pending errors are persistent)
      ──────────────────────────────────────────────────────────────── [then]
      Δ; Γ ⊢ M then x. N unwind D : F_Σ B          (§19: Σ's names nonzero, its keys unique)

  - `Σ_D ≤ Σ`: during an ordinary unwind `D` runs where the `[then]` stands, so its effects, and
    its operations' cancel rows, are the `[then]`'s.
  - `Σ_M(o).fin ⋈ Σ_D ≤ Σ(o).fin`: a cancel of a continuation captured at `o` inside `M` runs `D`
    under its `cfin`, and so does every cancel nested in it.
  - *At some depth* (`Row.UnrD`): at `Σ`'s top, or in the cancel row of a capturable entry at some
    depth. `D`'s frame runs in the cancels below it, where an unrestricted operation may resume its
    continuation twice.
  - *Pending errors* (`Row.PendPers`): the arguments of `Σ_M`'s abortive entries, and of the
    abortive entries of its capturable entries' cancel rows at every depth, are `!`. A running
    finaliser's `cfin` holds such an error while a cancel of its continuation runs.
  - §24's `[then]` is the instance `Σ_M = Σ`, `Σ_D = ∅` (`CDerives.effThenA`), since `F ⋈ ∅ ≤ F`
    (`ThenLe.nil`).
- **`[handle]`** is §24's rule, with the `i`-th operation's cancel row `F_i` (`Row.ofEff n E 0 fs`,
  `clausesTy S R E fs`), and

      K_i = U((B_i ⊸ F_Σ R) & ⊤) (lin),   U((B_i ⊸ F_Σ R) & C_i) (aff),   !U((B_i ⊸ F_Σ R) & C_i) (unr)
      C_i = F_{F_i ⊕ Σ} 1,   ⊤ when F_i = ⊤                                          (`cancelTy`)

  `F_i ⊕ Σ` is `F_i`'s layers ahead of `Σ`'s (`F.rowOf ++ Σ`), rows being read first match. At
  `F_i = []` it is `Σ`, so `κ`'s type is unchanged for every existing derivation. `[handle]` gains
  no premise: D3's check is `[sub]` from `C_i` to the row of the code that invokes the cancel. A
  handler that never cancels is checked for nothing.
- **Every other rule is unchanged**, `[let]`'s side condition included; `[perform]` and `[raise]`
  take entries at any cancel rows.
- **No unrestricted `exn`** (decision 63's restriction, 2026-10-12). An abortive operation is
  affine (§18), so a checked program's effect context has no unrestricted abortive operation
  (`EffCtx.NoUnrExn`), and no name's signature is one unrestricted `exn`
  (`EffCtx.NoUnrExn.ne_exn`). E9's stored closure holds `x : bool` across `cancel k`, a `[let]` at
  a row holding `exnₒ`, and `[let]` asks a persistent context at a row with an unrestricted
  operation, an abortive one included; so E9, as E5, is typed where no `exn` is unrestricted, which
  is every context the restriction leaves: `storedKFin` and `nestedFailOutside` (§19 *Programs*)
  are typed at `ΞE`, whose `exn` is affine (`dAt_storedKFin`, `dAt_nestedFailOutside`,
  `noUnrExn_ΞE`).

### Semantics

No change to the machine, `wpTS`, `wpG`, `ewpTS`'s definition, BoLo's world or a borrow lemma.

- **Entries** (`OpEnt.fin`, `finObl`): a capturable entry's cancel obligation at `δ`, none at `⊤`.
  `cancelObl T ls e ≜ ewpTS ls e (cancelTab T) ⊥`: the cancel run stops at its end
  `K₀[raise (⊥, err)]` (`err` none, or an abortive entry of `T` at its argument relation, with
  nothing owned left) or at a non-abortive operation of `T` under a context free of it, owing its
  continuation as any stop does (`performStop`).
- **The continuation's share** (`contShare`): at a capturable entry, the cancel run of the dead
  region at the entry's obligation (`cancelOK`). At the empty cancel row it is §19's
  `cancelOwed`.
- **The lemmas** (`Core/EffFin.lean`):
  - obligations grow with cancel rows (`finObl_mono`, `cancelOK_le`, `ewp_sub`): `[sub]`
    (`sub_compatC`);
  - a cancel under a plain context (`cancel_frame`, `plain_cancel₀`); a frame beside it holding
    nothing owned is left behind at the run's first stop (`cancel_frame_drop`, from `wpG_garbage`;
    `ent_plain`), so `[let]` reads nothing of the cancel rows (`let_compatC`);
  - `[cfin-cancel]`: `cfin err` around a nested cancel run at `G` is a cancel run at any `G′` with
    `pend {err} G ≤ G′` (`cfin_cancel`); a finaliser at `Σ_D` under a cancel's `cfin` is a cancel run
    (`cfin_run`); the `[then]` frame in a cancel is a cancel run at `F ⋈ Σ_D`, by induction on `F`
    (`then_cancel`); a finaliser that performs during an ordinary unwind (`seq_raise_run`);
    `[then]` (`ewp_frame_then`, `then_compatC`);
  - `κ`'s cancel branch: the cancel run at `F_i`, under its `ccatch`, is in the relation at `C_i`
    (`ewp_ccatch`), and `KapRel`'s cancel part is at `C_i`'s table (`ewp_handle`, `handle_compatC`,
    `handleV_compatC`).

### Theorems

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`, `adequacyD_obs` and every compatibility
lemma keep their statements, over the extended judgment. `CDerives.effThen` takes `Σ_M`, `Σ_D` and
the premises above; `effHandleV` takes the cancel rows; `effSub`'s `RowLe` is the order above.
`CDerives.effThenA` and `CDerives.effHandle` keep their former shapes, `effThenA`'s unrestricted
premise read at some depth. No new index.

### Programs

The runs of §19's cancels are unchanged (`Core/EffCancel.lean`). Their handlers' operations are
unrestricted, so `κ`'s slot is `!U(…)`, and a variable is read at a computation type only from a
`U` slot: a typed clause binds `κ` first, `(λk. k (inj₂ ())) κ` (`cancelCT`, `resumeCT`). The typed
programs (`Core/EffCancelTyped.lean`) are the untyped ones with those clauses, and run as they do,
one β-step longer at each use of `κ`:

- **`progT`** (D3): handler `1` cancels the continuation of `perform 1`, whose region holds a
  handler of `2` and a finaliser that raises `2`. It is typed at a row holding `2`, the cancel row
  of `perform 1`'s continuation `{2}` (`d_progT`), and at no row without `2` (`not_der_progT`, by
  inversion through `[handle]`, `[then]` and the clause); its run ends at a raise of `2` that no
  handler catches (`progT_run`).
- **`progOutT`**: `progT` under a live handler of `2`, typed at `F (1 ⊕ 1)` (`d_progOutT`); its run
  reaches `inj₂ ()` (`progOutT_run`). **`progOutTA`** is the same program at an affine raise of `2`,
  typed by a tied derivation at a context with no unrestricted abortive operation
  (`dAt_progOutTA`, `noUnrExn_Ξ₁₂A`), and run alike (`progOutTA_run`).
- **`cancelKeptT`** and **`progReT`**: the kept raise of `3` caught by a live `3` outside the
  region, the region re-entering the site `3` in `progReT` (`f ()` at `{1}`); cancel row `{3}`.
- **`progFinOpT`** and **`progNC₁T`**: the finaliser performs `4`, whose live instance at the
  cancel is the outer handler, which resumes it, or cancels its continuation (`[cfin-cancel]`);
  cancel row `{4}`.
- **`progDropT`** and **`progKeepT`**: a finaliser raises `2`, kept, and a later finaliser performs
  `4` with `2` pending: cancel row `{2, 4⟨{2}⟩}` (`pend`). `H₄ₒ`'s unrestricted clause drops the
  continuation, and the kept error with it (`inj₁ ()`, *Open*), or resumes it (`inj₂ ()`).
- **`progNCrecT`** (the leftover clause): two finalisers perform `4` under the handler of `4` that
  cancels. The second is a leftover of the first one's cancel, so `⋈` puts `4` in the cancel row of
  the `4` in the cancel row of `1`, which the cancelling handler's clause row, its own outer row,
  cannot hold: no derivation at any context and judgement (`not_der_progNCrecT`). Its run ends at a
  `perform 4` no handler catches (`progNCrecT_run`, `progNCrecT_stuck`).
- **`e7c nw ni qi`** (D3, E7c): `timeout (handle exnᵢ {…} (body (raise exnᵢ ())))`. `timeout`
  handles an affine `wait : 1 ↠ 1` and its clause cancels `κ`; the body's finaliser raises `exnᵢ`,
  handled only inside the cancelled region. `[then]` puts `exnᵢ` in `wait`'s cancel row, and the
  clause reads `κ`'s cancel branch at its own row, so no derivation types the program at a row
  without `exnᵢ` (`not_der_e7c`). At the row of `exnᵢ` it is typed, by a tied derivation at an
  effect context declaring `wait` and `exnᵢ` (`dAt_e7c_lift`, `d_e7c_lift`); at an affine `exnᵢ`
  that context has no unrestricted abortive operation (`noUnrExn_Ξe7c`).

### Lowering

The backend lowers a finaliser that raises (`Backend/Clos/Capture.lean`, `Backend/Clos/Unwind.lean`),
not one that may suspend, performing an operation of a control handler: an unwind and a cancel arm
call a finaliser directly. `Capture` rejects such a finaliser with a message. The four shapes, a
finaliser that performs (`progFinOp`), a cancel nested in a cancel (`progNC₁`), and a kept error
dropped with an unrestricted continuation or resumed (`progDrop`, `progKeep`), are Lean runs
(`Core/EffCancel.lean`, `Core/EffCancelTyped.lean`) and interpreter runs, not kernel programs. The
checker emits no such finaliser: its finalisers are destructors at `F 1`. No kernel program and
no count changes. Finalisers that raise run at every stage in the kernel programs `e7a`, `e7b`,
`e7d`, `e8b` and `stored-k-fin` (§19 *Programs*).

### Baseline

`Paper/`, `Support/`, the machine and the effectful `wp` are unchanged; no borrow rule and no borrow
lemma changes. Every existing derivation types at empty cancel rows. The checker emits empty cancel
rows (`Frontend/Check/Elab.lean`) and reads `[then]`'s premise at some depth (`Row.unrDB`), which at
its rows is the top-level test, so it accepts and rejects what it did.

### Open

- **The lowering of a finaliser that suspends** (planned: its
  cancel arm as a code of its own, each finaliser call a resumption point). Until it lands, a
  feature without its lowering.
- **`[then]`'s two premises on unrestricted operations** restrict `unr` beyond §19's `[then]`
  (decision 63). §19's top-level premise is not enough: the finaliser's frame is live in the
  cancels below it.
- **`⊤` cancel rows.** A continuation whose cancel would need unboundedly many outer instances
  (recursion through a finaliser's capturable operation) gets `⊤` and cannot be cancelled: the
  approximation of a finite type.
- **S5 at a finaliser that performs, algebraicity at every admissible context, and a kept error
  held by a continuation**. S5 is a Core theorem at finalisers that let raises escape
  (`unwind_prefix`, `cancel_prefix`, at `FinRow`; §19 *Laws* items 5 and 6), not at D2's finaliser
  that performs an operation a handler outside it answers, whose run is not a run alone.
  Algebraicity is proved given that every kept error holds no λ, which fails where a
  finaliser raises a thunk; the weaker hypothesis (no captured continuation in a kept error) needs a
  simulation relation that confines the law's frames to continuations. "No error is dropped" is
  proved on the runs whose `[op]` steps capture no kept error. An unrestricted continuation
  discarded with a kept error inside it is the tolerated exception; a linear or affine one holding a
  kept error waits on S6's use exactly once.

## 28. Entry 27 — BOXED-κ: a handler clause that receives its continuation boxed

### Motivation

A scheduler keeps the continuations its handler captures (`docs/async-capabilities.md` §2.3, P4).
The clause of `await` answers the rest of the task, and the scheduler stores it in a queue whose
type outlives a bound: a cell lent `mut` at a fresh lifetime takes a payload whose type outlives
the bound (`withbor2`'s side condition, §23), and so does a block's result (`[]I`). `[handle]`
gives a clause its continuation bare, at `kTy Σ R q B F` (§19, §27), a `U` type, and the outlives
judgment has no case for `U C`. So a continuation is never at a `[@d]` type, and no stored task
outlives anything. Boxing it inside the clause is `[]I` over the clause's context, which holds `κ`
at a `U` type, so it fails the same way.

BOXED-κ is the variant of `[handle]` whose clause receives `κ : [@d] K`. It is ported from
`experiments/BoxedKappa` (branch `nominal-lifetimes`), which proves its compatibility with no new
invariant.

### Typing

    Γ = Γ₁, Γ₂    Γ₁'s live slots persistent    Δ; Γ₁ ⊢ H : retTy Σ A R ⊗ clausesTyB Σ R d E fs
    Δ; Γ₂ ⊢ e : F_{E_n ⊕ Σ} A    n ∉ Σ, n ≠ 0, |E| ≤ 2³²
    Δ ⊨ Γ₂ ⊐ @d    every non-abortive o of E_n ⊕ Σ:  Δ ⊢ o.B ⊐ @d
    ──────────────────────────────────────────────────── [handle-boxed]
    Δ; Γ ⊢ handle_n e with H : F_Σ R

- `clausesTyB Σ R d E fs` (`Core/EffBoxed.lean`) is `clausesTy`'s tuple (§19, §27) with each
  capturing clause at `!U(A ⊗ [@d] K ⊸ F_Σ R)`, `K = kTy Σ R q B (fs i)`; an abortive clause is
  `!U(A ⊸ F_Σ R)`, as in `clausesTy`.
- `Δ ⊨ Γ₂ ⊐ @d` is `[]I`'s premise at the handled computation's context (`CtxOutlives`, which
  holds `Δ ⊨ @d`).
- The answer premise (`Row.AnsOutlives Δ d (E_n ⊕ Σ)`) covers the handled operations and the
  forwarded ones: a forwarded operation's answer comes back into `e`'s continuation, which a later
  handled operation may capture. An abortive operation never resumes and is not constrained.
- No premise excludes a lend open at a stop. A lend's callback is typed at the pure row or at a row
  of abortive operations (§19), and `wpG`'s `↭` from a run's start to its end already excludes a
  borrow cell open at a stop.
- The rule is `CDerives.effHandleVB` (and `CDerivesAt.effHandleVB`, the handled row tied to `Ξ`,
  §19 *Typing*). Its term is `[handle]`'s `hndExpr`: no term former, no type former, no index.

### Semantics

No change to the machine, the relation, `wpTS`, `wpG`, `ewpTS`'s definition, BoLo's world or a
borrow lemma. `Core/EffBoxed.lean`:

- **The stratified table** `opTableS α T`: `opTable T` with one more conjunct at each non-abortive
  stop, the continuation's share in `Res_α` (`box α P ρ = P ρ ∧ ρ.InStratum α`). It is below
  `opTable T` (`opTableS_le`, `ewpS_ewp`).
- **The stop lemma.** A run started in `Res_α` ends in `Res_α`: `wpG` carries `↭` from the start
  to `π = ρ' ● ρp`, `↭` keeps `Res_α` (`ResU.updV_inStratum`, `[TR]` 6.50 at `Res_α`), and the
  end resource is a `●`-factor (`wpG_inStratum`). At a stop the share is a `●`-factor of the
  stop's resource; across a resumption the next run starts at the share and the answer, in `Res_α`
  when the answers are (`OpTab.AnsIn`; `ewp_stratify`, by induction on `ewpTS`'s fixed point). At
  the typing, `stop_sem` takes the context's resource into `Res_{δ(d)}` by `[]I`'s fold of 6.60
  (`gSepC_outlives`) and the answers by `vC_outlives` (`Row.ansIn_of_ansOutlives`); `stop_lemma`
  (`Core/Fundamental.lean`) is it at a `CDerives` derivation.
- **The handler at the stratified table** (`ewp_handleS`): `ewp_handle`'s proof, the clause given
  the share's stratum besides `KapRel`. At a linear or affine operation `κ` also holds its capture
  cell (§25), an `own` cell, in every stratum (`ResU.inStratum_single_own`). From `KapRel`,
  `vC_kTy_of_kapRel` gives `vC K κ`, and the stratum makes it `vC ([@d] K) κ`
  (`ewp_handle_valsB`).
- **Compatibility**: `handleV_compatCB` (the value form, `[handle-boxed]`'s case in
  `fundamentalC`) and `handle_compatCB` (two variables).

### Theorems

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`, `adequacyD_obs` and every compatibility
lemma keep their statements, over the extended judgment; adequacy stays unconditional. New:
`stop_lemma`, `stop_sem`, `ewp_stratify`, `ewp_handleS`, `handle_compatCB`, `handleV_compatCB`.

Each induction over `CDerives` and `CDerivesAt` takes the rule as a case (`Core/Closed.lean`,
`Core/Weaken.lean`, `Core/InsertDead.lean`, `Core/Tied.lean`, `Core/RaiseNames.lean`,
`Core/EffTier1Programs.lean`). The inversions (`Core/Inversions.lean`) read a handler's clause
tuple at `clausesTyO Σ R ob E fs`, `κ` bare (`ob = none`, `clausesTy`) or boxed (`ob = some d`,
`clausesTyB`): `der_hnd`, `der_hndJ`'s `HndBase`, `hnd_clauses`. A boxed `κ`'s views keep the thunk
head (`vview_kBoxO_thunk`, `kviewO`), and `κ`'s cancel branch is read the same way at either
(`kcancel_jr_aff`, `cancelCT_jr`, `timeoutCl_finds`), so the programs no derivation types stay
untyped: `not_der_progT`, `not_der_progNCrecT`, `not_der_e7c` (`Core/EffCancelTyped.lean`),
`not_der_at06`, `not_der_at08`, `not_der_at13` (`Core/Rejections.lean`).

### Checker

`handle_with[n](hr, hc) M` (§19) reads the clauses' type as BOXED-κ's when it can
(`clausesReadBoxed`: the lifetime of the first clause whose argument is `A ⊗ [@d] κ`, `κ` a
continuation's type, then `clausesReadB`; `Frontend/Check/Steps.lean`), and as `[handle]`'s
otherwise. `clausesRead` would read a clause `!U(A ⊗ [@d] κ ⊸ F_Σ R)` as an abortive operation's,
so the boxed reading comes first. At the boxed reading it decides `Δ ⊨ @d` (`Life.wf`), the answer
premise (`ansOutlivesB`, sound by `outlivesB_sound`, `Frontend/Check/Decide.lean`) and the context
premise on the slots `M` uses (`usedSat (outlivesB Δ d)`, as `[]I`), and builds the derivation by
`rEffHandleB` (`Frontend/Check/Rules.lean`, `TiedDer.effHandleB`, `CDerivesAt.effHandleB`). Each
failed premise has its own message, naming the slot or the operation
(`corpus/reject/boxed-kappa-context.bc`, `corpus/reject/boxed-kappa-answer.bc`).

### Programs

P4 with stored continuations (`research/effects/src/boxed-kappa-programs.md`), the spawn handler
in the program and typed by the checker:

- `corpus/sched-a.bc`: two tasks, each borrowing its own local across an `await`, spawned by a
  handler whose clause receives `κ : [@⊤] K` and answers `[@⊤] U Task`,
  `Task = νX. F(i32 ⊕ [@⊤] U X) & F 1`; a queue lent `mut` at a fresh `'q` per observation of a
  run-until-empty loop, driven by a bounded driver. `i32[41130]`: task 2 finishes first, so the
  tasks interleave. Counts `63 18 0`.
- `corpus/sched-a-div.bc`: the same, the loop handed back to the runtime undriven (its type
  mentions no lifetime). `i32[41130]`, counts `31 5 0`.
- `corpus/sched-b.bc`: `spawn` polymorphic in the bound, `!(all 'd < top. box 'd Code => E<'d>)`,
  BOXED-κ at `@d = 'd`; task 2 captures `imm 'r i32`, the queue bounded by `'d ⊏ 'r`, the bounded
  scheduler inside the blocks. `i32[87130]`, counts `64 18 0`.
- Rejected (`corpus/reject/`): `sched-b-div.bc` (the run-until-empty loop out of the blocks, at
  `boxed['d]`), `sched-c-equal.bc` (`@d = 'r`, at `boxed['r]`), `sched-c-outside.bc` (`'r ⊏ 'd`,
  at `boxed['d]`); `boxed-kappa-context.bc` (the handled computation holds `imm 'r` across the
  stop, `κ` boxed at `'r`) and `boxed-kappa-answer.bc` (an operation answering a `U` type). The
  last two check with `κ` bare.

### Lowering

None: the term is `[handle]`'s, and the backend reads no type. Every stage runs the programs above
to their goldens with `live 0`.

### Baseline

`Paper/`, `Support/`, the machine, `cC`/`vC` and the effectful `wp` are unchanged; no borrow rule
and no borrow lemma changes. A clause tuple with no clause whose argument is `A ⊗ [@d] κ` is read
as before, and no existing program has one: every corpus and kernel program checks and runs as
before, with the same counts.

### Open

- **Necessity of the answer premise**: not determined (`experiments/BoxedKappa/README.md` §3, on
  `nominal-lifetimes`). Its only use is `OpTab.AnsIn`, the answers' resources in `Res_{δ(d)}`.
- **One former for the clause tuples.** `clausesTy` and `clausesTyB` are parallel; `clausesTyO`
  (`Core/Inversions.lean`) is the general one, used by the inversions only.
- **The surface.** A surface handler's clause that takes `k` out of a box receives it boxed at
  `top` (§30); `lib/async.bc`'s `spawn` is its first library user. A bound other than `top` needs
  a handler's lifetime parameters (§30 *Open*).

---

## 29. Entry 28 — a borrow held across a suspension: the relaxed lend R1, under `PinLaw`

### Motivation

#52's decision (`docs/async-capabilities.md`): tasks are direct-style code that borrows its own
locals across `await`, with no `Pin` and no annotation, and the one assertion needed for it is a
named hypothesis of the theorems, never an axiom, tested by programs that try to break it. Core
types every borrow callback at a row of abortive operations (`Row.Unwind`, §19): a `mut` borrow
block whose body performs `yield` or `await` is refused (T1, #172). This entry adds the relaxed lend
R1 of `docs/async-capabilities.md` §3.3 as a rule of an extended judgment beside `CDerives`, and
states its soundness as `PinLaw`. `CDerives` and its theorems are unchanged; a program that does not
use R1 keeps them unconditionally.

### Typing

    Δ ⊨ b defined   x fresh   T, B free of 'x   B has no U   Δ ⊢ T ⊒ @b'   Row.ResumeO Σ 'x
    M closed but for m   ·  ⊢ d : Ref T ⊸ 1        Δ, 'x ⊏ b ; m : Mut 'x T ⊢ M : F_Σ ([@x] B)
    ─────────────────────────────────────────────────────────────────────────────── [lend-R]
              r : Ref T ⊢ withborU d r (Λ. λm. M) : F_Σ (Ref T ⊗ B)

    Δ; · ⊢ e : J        Γ consumed
    ───────────────────────────────── [nil-dead]
    Δ; Γ ⊢ e : J

- `Row.ResumeO Σ 'x`: every operation of `Σ` resumes (none abortive), none is unrestricted, its
  cancel row is empty, it answers `1`, its name is not `0`, and its argument is closed data: free
  of `'x`, outliving every lifetime, with no `U` (`NoThunkT`). `await` and `yield` are such
  operations (`resumeO_await_yield`); `raise` is not (`not_resumeO_raise`).
- The term is §19's unwinding `withbor` (`withborUV d`); only the callback's row differs. `d` is the
  owner's finaliser, the source's destructor: it runs when a continuation captured inside the
  callback is cancelled.
- `[lend-R]`'s premise is the callback's derivation in the extended judgment, so a relaxed lend
  may hold another. The rule concludes at the context `r : Ref T` alone. `[nil-dead]` places it
  under a program's other slots, as `(λr. withborU d r (Λ. λm. M)) x`: the λ is typed at the empty
  context and placed at any consumed one. `[nil-dead]` is admissible for `CDerives`
  (`CDerives.append_dead`, §26) and sound by `semC_dead`; it is in the extended judgment because
  `[lend-R]` concludes at one fixed context. It also lets a relaxed lend sit under binders inside
  another's body, so `PinLaw.stop`'s premise ranges over those derivations too.
- R2 (`lendLoopR`, the `imm` lend over a loop whose state holds the borrow,
  `docs/async-capabilities.md` §3.3) is in the judgment as well, with its compatibility lemma
  `PinLaw.loop`; the checker does not emit it (U6).

**The extended judgment.** `CDerivesP` (`Core/PinDerives.lean`) is `CDerives` with every premise
in `CDerivesP`, plus `lendR`, `lendLoopR` and `nilDead`. It is generated from
`Core/Fundamental.lean` by `scripts/gen-pin.py` (templates in `scripts/pin/`), so a rule added to
`CDerives` is in it after a rerun; `python3 scripts/gen-pin.py --check` fails when the generated
files are stale. §28's BOXED-κ (`effHandleVB`) is in it so, its case in `fundamentalC_pin`
`handleV_compatCB`, as in `fundamentalC`.

**`PinLaw`** (`Core/PinLaw.lean`) is a `structure … : Prop` of two fields, the compatibility lemmas
of R1 (`PinStop`) and R2 (`PinLoop`) at the rules' own premises, with every quantifier over code a
quantifier over `CDerivesP` derivations. It is a hypothesis of the theorems that use it.
`PinStop`'s premise is the body's `CDerivesP` derivation, so what it covers is every body that
judgment types: bodies holding a nested relaxed lend (through `nilDead`), and bodies using §28's
BOXED-κ rule (`effHandleVB`), as well as every rule of `CDerives`. What a named assertion of this
kind ranges over is an open question of the design of assertions (kind R of `docs/unsafe.md`, on
the branch `unsafe-spec`).
`docs/async-capabilities.md` §4 gives the evidence for it, what is proved elsewhere, and what
would falsify it.

### The surface

A `borrow mut x { m -> S }` of an owned cell `x : ref A` whose body performs an operation that
resumes is R1, the core form

    withbor2r['x, @b, A, B, [ROW]](p, m) M

with the lend's bound `dom`, the row the operations of the names the body performs, and `M` the
body, its result boxed. Its body sees the view alone: a body that names another variable of the
function is rejected ("… uses `y`, which is outside it …"). A body that performs a resuming
operation and an abortive one, the abortive one's handler outside the block, is rejected (OQ-1 of
`docs/async-capabilities.md`). An `imm` block, or a block over a view, whose body resumes is
rejected as before (§15 *Self-reference*; OQ-2). R1 is chosen only where no ordinary rule
applies: a block whose body performs only abortive operations is §19's unwinding borrow, and a
borrow block over a loop is §14's per-observation lend. Segmenting a block at a suspension when
only the borrow crosses it (L0) is not built (U3).

The checker types `withbor2r` by `[lend-R]` at the slot of `p`: it checks `M` at `Δ, 'x ⊏ @b` and the
context `m : mut 'x A` alone, and decides `Row.ResumeO` (`Row.resumeOB`), `NoThunkT` (`noThunkB`)
and the closedness of `M` (`rLendR`, `Frontend/Check/Pin.lean`).

### Semantics

No change to the machine, the relation, `wpTS`, `wpG` or `ewpTS`. The erasure is the unwinding
`withbor` applied to the callback, under a β-redex.

### The checker's derivation and the assurance report

Every derivation the checker builds is a `CDerivesP` derivation, and it is of `CDerives`, tied
(decision R, §19), exactly when it uses no relaxed rule: `TiedDer p s` (`Frontend/Check/Tied.lean`)
carries the list `p` of the relaxed rules used, with where each is used, and is a tied
`CDerivesAt` derivation when `p` is empty. A checked `main` carries its `pins`.

`bcc check` prints, after the declarations and the reports, one line:

    assurance: unconditional
    assurance: PinLaw (R1 at 22:11, 34:11)

`bcc trusted` lists the same under `typing:`, each site with the field of `PinLaw` it rests on.
The programmer writes nothing.

### Lowering

A cell lent across a suspension must not move while the view is held (§3.5 of
`docs/async-capabilities.md`). The backend already keeps it in place: every `alloc` is a heap
object (Backend/README.md, *Representation*), and a suspended code's state holds the cell's
location, a word, never its contents. Nothing is added; the programs below run at every stage
with the counts of `corpus/counts.expected`.

### Theorems

    fundamentalC_pin (hPin : PinLaw) : CDerivesP Δ Γ e j → SemJ Δ Γ e j
    adequacyC_pin, adequacyD_pin, adequacyD_pin_safe (hPin : PinLaw)
    CDerivesP.ofC : CDerives Δ Γ e j → CDerivesP Δ Γ e j

`fundamentalC_pin` is `fundamentalC`'s induction, case for case, with `hPin.stop` at `lendR`,
`hPin.loop` at `lendLoopR` and `semC_dead` at `nilDead` (`Core/PinFundamental.lean`, generated).
At the checker: `checkProgram_soundP` (every checked `main` has a `CDerivesP` derivation),
`checked_sem_pin` and `checked_runs_pin`; `checkProgram_sound`, `checkProgram_tied`,
`checkProgram_tiedAt`, `checkProgram_letPoly`, `checked_sem`, `checked_runs`,
`IORun.every_run` and `IORun.loop_every_run` take `c.pins = []`, which `bcc check` reports as
`assurance: unconditional`.

### Baseline

`CDerives`, `fundamentalC`, `adequacyC` and `adequacyD` are unchanged and unconditional; no borrow
rule and no borrow lemma changes. A program that performs no resuming operation inside a borrow
block elaborates, checks and erases as before, and `bcc check` reports it `assurance:
unconditional`. Every reject program keeps its message.

### Programs

`corpus/async-r1-local-borrows.bc` (A2: a closure over the view, and a pair holding it, across a
suspension; two tasks interleaved), `async-r1-effects.bc` (A5: a log and an error handled inside
the block), `async-r1-cancel.bc` (A6: a task cancelled while it holds the lend and an owned value),
`async-r1-cancel-finaliser-writes.bc` (§6.2 row 16, in the core text: the borrower's finaliser
writes through the view before the lend ends), `async-r1-nested.bc` (a relaxed lend inside
another), `async-r1-generator.bc` and `async-r1-drain.bc` (§15's self-referential generator with a
`mut` borrow). The tasks are stored generators whose
`yield` is their `await`, and the scheduler is written inline: `lib/async.bc` is U2.
`corpus/reject/async-r1-two-mut.bc`, `async-r1-raise-across.bc`, `async-r1-view-argument.bc`,
`async-r1-unr.bc` and `async-r1-spawn-captures.bc` are §6.2's rows 2, 11, 12, 14 and 10.

### Open

- L0 (U3), R2 at the checker (U6), BOXED-κ (U1) and `lib/async.bc` (U2); `docs/async-capabilities.md`
  OQ-1 to OQ-5.
- A derivation that uses a relaxed rule is not claimed tied (decision R): a tied `CDerivesP` is not
  built.
- Shrinking `PinLaw` (U8).
- What `PinStop` ranges over (above): kind R of `docs/unsafe.md`.

---

## 30. Entry 29 — effectful blocks and async tasks at the surface

### Motivation

The async colourless test (#52, `docs/async-capabilities.md` §1): one function written once is used
by synchronous code and by tasks that suspend to a scheduler, and nothing in its type says which.
Three pieces of the surface were missing (unit U2 of `docs/async-capabilities.md` §7):

1. **Effectful blocks** (#161). A closure that performs an operation was rejected where it was
   passed as a value (§18 *Not provided*), so a higher-order function could not be given an
   awaiting callback.
2. **A counted loop at a resuming row.** A `for` over data whose body performs an operation that
   resumes was always a div loop (§16 *Effectful bodies*), and no handler wraps a div computation
   (§21 *Open*), so a task with a counted loop that awaits could not be spawned.
3. **BOXED-κ from a surface handler.** Only core-text `handle_with` emitted §28's rule, so a
   library scheduler could not store a task's continuation in a queue.

Everything here is elaboration into core terms the checker already derives: no `CDerives` rule,
type former, relation clause or machine step is added.

### Effectful blocks

A **block** is a closure written as an argument at a parameter of function type, `!(A => B)` or
`A => B`, of a function declared before the call (`docs/async-capabilities.md` §2.1, §2.2):

- **Its type names no effect.** The parameter's written type is the callee's, unchanged: `map(xs:
  List[i32], f: !(i32 => i32)) -> List[i32]` takes a pure block and an awaiting one alike.
- **Its effects are those of where it is written.** Its control operations resolve lexically, as
  any operation does, to the innermost sites of their effects around the block (§19 *Names*): a
  block that awaits inside a function served by a spawn site performs that site's `await`. The
  callee handles none of them by accident: its own `with`s are sites with names of their own
  (`corpus/effects-tunnel.bc`, E6).
- **A use is a use of a copy at the block's row.** The call `g(…, blk, …)` of a function `g`
  (with or without a row of its own) is a call of `g`'s copy for its block parameters' rows,
  `g__…_b{j}n{k}…` (`j` the parameter, `k` the sites of its block), made once per (function, sites,
  block rows) and shared: §14's specialization at a callback's type and §18's copy per assignment
  of names, keyed by the block's sites. In the copy, parameter `j` has the type `!U(A -o F[r] B)`
  (or `U(A -o F[r] B)`), `r` the entries of the block's sites, and the copy's row is its own
  sites' and the blocks'. A recursive function given a block is the copy of its group (§20).
- **In the copy, a call of the parameter** is a call of a value whose type has a row, a
  computation of its own bound before the value it is in, as a call of a copy is (§18 *Rows*);
  passing the parameter on to a block parameter of a call (a recursive call included) makes that
  callee's copy at the same rows. **Any other use is rejected** (`corpus/reject/block-stored.bc`):
  a block is called, never stored or returned. A stored callback carries its row boxed at a bound
  (`docs/async-capabilities.md` §2.3), which is *Open* below.
- **The block is checked at its row.** The call's argument is bound at the copy's parameter type
  (`a : P <- return W`), so the block, a `thunkv`/`!thunkv` closure, is checked against
  `!U(A -o F[r] B)` and its operations are typed at `r`.
- Where they coincide, the copies are `[let-poly]`'s premise (§24 *Theorems*,
  `checkProgram_letPoly`): the kernel has no row variable, and Core checks each copy at closed rows.

The pure use of a function is the function as written: no copy, the block a plain closure
(`corpus/async-map.bc`: `map__n3` at `Exhausted`'s row only, for its recursion; `map__n2_b1n1`
for the awaiting block). `bcc check` reports each copy with its blocks, `copy `f__…`: `f` for …,
its block `x` at the site k of `E``, and each call of a block parameter, `x → the block,
performing at the site k of `E``.

**Not provided**, each rejected with a message saying so: a block that uses an answering capability
(it would be passed with the block at each call; `corpus/reject/block-capability.bc`); a block that
performs an operation of a `for`'s site, which threads the loop's variables
(`corpus/pending/yield-callback.bc`); a named function with a row passed as a value (§18); a block
given to a member of a recursive group of several functions, or under a heap driver (§20); a
block given to a generic function (`fn f[A](…)`), whose instance is matched against the block's
type before the block's row is known.

### Counted loops at a resuming row

**PROPOSED, pending the user's decision** (`docs/surface-callbacks.md` OQ-S1, branch
`effects-async-a1`): built as below, so that A1 runs, but the choice among OQ-S1's options is not
settled. §16's *Effectful bodies* rule is kept where it is needed and narrowed where it is not. A counted
loop (a `for` over a sized source) whose body performs an operation that resumes is:

- **a div loop, one turn per observation**, when the operation is of a site that observes its
  computation one turn at a time: a `for`'s site of an iteration effect, or a stored generator's
  (§15). These are the sites the elaboration of effects records (`St.perTurn`); every such loop
  of an existing program is one of these, and is elaborated as before;
- **a loop at the row** otherwise (a site of a `with`): `bounded_fix` (§20) whose budget is the
  count, `max(0, len)`, so that the self-reference is `inl ()` exactly when the body has run at
  every index. Its step runs the body at the row, `I32 ⊗ S ⊸ F_Σ (S ⊕ E)`, and goes on with the
  self-reference at the next index, or leaves by an exit (`break`, `return`, as §16's count_try
  step does). It is a total computation, which a handler wraps; an abortive operation in the body
  is performed where it stands. The kernel's `forN` of the async colourless test is this term
  (`dAt_forN`, branch `effects-async-a1`). A `&a`, `&mut a` or owned-array source lends around
  the whole loop, and is rejected, as at a div loop (T1, #172).

`bcc check` reports such a loop as `total, bounded by len(…): its body performs an operation that
resumes, so it is a loop at the row (bounded_fix over the count)`. It is OQ-S1's option (c),
restricted, as a proposal: counted sources at a `with`'s site take (a); generators keep today's
(b)-shaped div loop.

### BOXED-κ from a surface handler

A clause of a control handler that takes its continuation out of a box, `unbox k`, receives it
boxed at `top`: the site's clause tuple is `clausesTyB Σ R ⊤ E` (§28), whose capturing clauses take
`A ⊗ [@⊤] K`, and the checker types the site by `effHandleVB`. A clause that only resumes or
cancels `k` receives it bare, as before; no existing handler takes `k` out of a box. The bound is
`top` because a handler declaration has no lifetime parameters; a task that holds a borrow from
outside is refused by §28's premises (the handled computation's context must outlive `top`). A
handler with a state (§21) whose clause boxes `k` is not provided. The report of the site adds
`the clauses receive the continuation boxed at `top` (BOXED-κ)`.

### `lib/async.bc`

`include async` declares

    effect Async { ctl await() }
    type Task[A]  = box top U (nu X. F (A + box top U X) & F 1)
    type List[A]  = mu X. 1 + (A * X)
    type Queue[A] = i32 * (mu X. 1 + ((A + Task[A]) * X))
    handler spawn[A]: Async, A -> Task[A]

- `with spawn { M }` runs `M` to its first `await` and answers the task: `inl v` at its next
  observation when it finished, else the rest. The `await` clause receives `κ` boxed at `top`
  (above) and answers `boxed[top] (thunkv nu_in < resume κ, cancel κ >)`: the task's next
  observation resumes `κ`, which runs it under the reinstalled handler (handlers are deep) to its
  next `await` or its end, and its close cancels it.
- `resume(t) : A + Task[A]` observes a task once; `cancel(t)` closes it, running its finalisers.
- `queue[A]()`, `push(q, t)`; `run_until_empty(q) : List[A]` resumes the queued tasks round robin
  until none is pending and answers their values in the order they were queued. Its rounds are
  unbounded, so it is div (§14): a program that runs it is a loop the runtime drives. A round, the
  reversals and the final values are counted loops over the queue's length.

The spellings are provisional: `docs/async-capabilities.md`'s `async::run { s -> s.spawn { … } }`
needs the spawned block's `await` to reach a handler inside `spawn`, a provided effect (decision
57's ports), which is not built; `with spawn { … }` puts the site around the block lexically.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/async-scheduler.bc` | A1: two tasks spawned by `with spawn`, each a `ticker` whose counted loop awaits (a loop at the row), run round robin until empty | `[1111, 22]` | `24 6 0` |
| `corpus/async-map.bc` | A4: `map` written once, given a pure block in `main` and an awaiting block in a task | `([2, 3, 4], [[10, 20, 30]])` | `29 4 0` |
| `corpus/effects-hof-two-rows.bc` | E1 from source: `hof` at three rows | `(inr (), (inr (), inr ()))` | `0 0 0`, as the kernel's `hof-two-rows` |
| `corpus/effects-tunnel.bc` | E6 from source: a block's raise passes the callee's own handler | `inr ()` | `0 0 0`, as the kernel's `tunnel` |

Rejected: `corpus/reject/block-stored.bc`, `corpus/reject/block-capability.bc`. Every program runs
at the source stage, the closure and flat IRs and WebAssembly with `live 0`, and passes
`scripts/falsify.sh`'s four modes.

### Lowering

Nothing is lowered specially: a copy is a `def`, a block a closure, the loop at the row a
`bounded_fix`, and the spawn site §19's handler with a clause that keeps `κ`
(`Backend/Clos/Capture.lean`). One fix in the lowering of abortive operations
(`Backend/Clos/Unwind.lean`): a call of a `sel` code (a resume code's `inl y` / `inr ()` arms) at a
known injection raises only that arm's keys, as the flow and `Capture` already read such calls.
Before, a task's cancel arm was credited with what its resume arm raises, and a task that both
suspends to an outer handler and raises to an inner one (`with spawn { with on_exhausted(…) {
recursion } }`, A4) failed to compile. New programs pin it: `corpus/capture-await-raise.bc`,
`corpus/capture-store-raise.bc`, `corpus/rec-await-exhausted.bc` (`0 0 0`, `0 2 0`, `3 0 0`);
every other program's counts are unchanged.

### Baseline

No change to `CDerives`, the relation, the machine or a kernel program. Every elaborated program is
checked by the unchanged checker, so `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD`
cover it with no hypothesis: A1 and A4 hold no borrow across an `await`, and use no relaxed rule of
`docs/async-capabilities.md` §3.3. Every existing corpus and kernel program elaborates, checks and
runs as before, with the same output and counts; the reports change only where a message changed
(`corpus/reject/include-unknown.bc` lists the module `async`; `corpus/pending/yield-callback.bc`
fails at its block).

### Open

- **Stored callbacks with their row** (`docs/async-capabilities.md` §2.3): a callback stored in
  data, boxed at a bound, whose row is inferred and never written.
- **`s.spawn { … }`**: spawning by a scheduler handle, which needs a provided effect (a port,
  decision 57) or an operation whose argument is a computation (the draft spec's OQ-61).
- **A handler's lifetime parameters**, so that a clause boxes `κ` at a bound other than `top`
  (a queue inside a lend, `corpus/sched-b.bc`'s `'d`).
- **Blocks with answering capabilities** and **blocks at a `for`'s site** (threaded variables):
  the capabilities passed with the block at each call (`docs/surface-callbacks.md` E6, branch
  `effects-async-a1`).
- **Rank 2**: a block parameter has one row per copy; a function that calls one parameter at two
  rows that cannot share one is not expressible.
- **One copy per closure** (`docs/surface-callbacks.md` OQ-S6): two blocks of one row given to
  one copy are one code each, called through the closure's dispatcher where the flow cannot tell
  them apart.
- **Tasks that hold a borrow across `await`** under `lib/async.bc`'s scheduler: R1 is §29, whose
  programs schedule stored generators inline; a task of `spawn` holding a relaxed lend, `cancel` of
  one (A6), a scheduler that logs (A5), and L0 (U3) are not built on this library.

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
`Core/Stale.lean`. Entry 13 (§14) is implemented in `lib/div.bc`, `lib/lend.bc`, `Frontend/Sugar.lean`,
`Frontend/Elab/LoopLend.lean` and `Core/Totality.lean`, with no change to `CDerives`; each div
body is one state machine. Entry 14 (§15) is implemented in `lib/yield.bc`, `lib/adapters.bc`,
`Frontend/Elab/Effects.lean` (the sites), `Frontend/Sugar.lean` (`forYield`, `pullView`, the
machine at a row) and `Frontend/Elab/Subst.lean`, with no change to `CDerives`, and lowered by
`Backend/Clos/Capture.lean` and `Backend/Clos/Convert.lean`. Entry 15 (§16) is implemented in
`Paper/` and `Support/` (the step), `Core/CountFold.lean`, the checker (`count_fold`) and the
backend (`count_loop`). §9's slice borrows are `Core/SliceFrames.lean` and `Core/Slices.lean`,
the checker (`slice_borrow_*`, `slice_*_mut`, `array_mut`) and the borrow blocks of
`Frontend/Sugar.lean`; §8's byte is `Width.w8` throughout. §9's splits and writes are
`Core/SliceOps.lean`, the step `split` in `Paper/` and `Support/`, the checker
(`slice_split_*`, `slice_empty_*`, `slice_replace_mut`, `slice_swap_mut`), the backend, and the
library `lib/slice.bc`. Entry 16 (§17) is implemented in `lib/buf.bc`, `lib/text.bc`,
`lib/textio.bc`, `Frontend/Lexer.lean`, `Frontend/Parser.lean` and `Frontend/Sugar.lean`, and the
literal lowering in `Backend/Clos/Convert.lean`, `Backend/Flat/Lower.lean` and the Wasm
runtime, with no change to `CDerives`; §11's `write_all` and `read_into` are `Core/Stdio.lean`. §16's K0′ is the step `countTry` in `Paper/` and `Support/`,
`Core/CountFold.lean` (`countTry_compatX`), the checker (`count_try`) and the backend
(`count_try_loop`); its `for` loop over data is `forData` in `Frontend/Sugar.lean`, the parser's
`a..b`, `continue`, `else`, `loop` and `sized`, and `lib/iters.bc`; its completeness lemma is
`Support/Dynamics/Completeness.lean`. Entry 17 (§18) is implemented in `Frontend/Parser.lean`
and `Frontend/Elab/Effects.lean`, its laws in `Core/Handlers.lean`, with no change to `CDerives`.
Entry 19 (§20) is implemented: the step `boundedFix` in `Paper/` and `Support/`,
`Core/BoundedFix.lean` (`boundedFix_compatX`), the `CDerives` rule and the checker's
`bounded_fix`; the groups, the steps and the heap driver's sources in `Frontend/Elab/Effects.lean`;
the machine in `Frontend/Sugar.lean` (`recMachine`); `lib/rec.bc`; and the lowering in
`Backend/Clos/Convert.lean` (`fixValue`) and `Backend/Clos/Capture.lean` (`unwindClause?`,
`wrapRaise`).

Entry 20 (§21) is implemented in `Frontend/Elab/Effects.lean` (`groupCopy`, `selfCall`, `layerCopy`,
`withCtl`, `resumeCall`) and `Frontend/Sugar.lean` (`hndCtlC`, `HInfo.after`), with no change to
`CDerives`; `Backend/Clos/Capture.lean` loses `unwindClause?`.

Entry 22 (§23) is implemented: the outlives judgment and its 6.60 in `Core/Types.lean` and
`Core/RelationFacts.lean`; the side condition at the borrow rules in `Core/Fundamental.lean`,
`Core/Compatibility.lean`, `Core/Slices.lean` and `Core/EffBorrow.lean`; the checker's decisions
in `Frontend/Check/Decide.lean` and `Frontend/Check/Consts.lean`; `main`'s lifetime and the
lifetime bounds in `Frontend/Sugar.lean`, `Frontend/Parser.lean`, `Frontend/Syntax.lean` and
`Frontend/Print.lean`; `lib/aff.bc`; cells of no words in `Backend/Flat/Lower.lean`. No change to `Paper/`, `Support/` or `CDerives`'s indices.

Entry 21 (§22) is implemented: the positivity in `Core/Types.lean`, `Core/Relation.lean`,
`Core/RelationFacts.lean`, `Core/NuRel.lean`, `Core/Computation.lean` and `Core/Nu.lean`; the
closure in `Core/Aff.lean`, `Core/AffRules.lean` and `Core/AffPrograms.lean`; the checker's
decision in `Frontend/Check/Decide.lean` and parameterised `type` declarations in
`Frontend/Syntax.lean`, `Frontend/Parser.lean` and `Frontend/Check/Elab.lean`; `lib/aff.bc`; and
`Backend/Clos/Collapse.lean`. No change to `CDerives`.

Entry 18 (§19) is in progress (#186). Stages 1–3 are implemented:
- the machine: `perform`, `raise`, `hnd`, `ubind`, `ccatch` and `cfin`, and their steps, in
  `Paper/`;
- unique decomposition and determinism: `Core/Steps.lean` and `Core/Demonic.lean`;
- `F_Σ A` (`CTy.eff`) and its relation: `Core/Types.lean`, `Core/Relation.lean`,
  `Core/EffDefs.lean`;
- the effectful `wp` and the frames at `wpG`: `Core/EffWp.lean`;
- the six rules' compatibility: `Core/EffRules.lean`. `fundamentalC`, `fundamentalD` and
  `adequacyD` cover the extended `CDerives`;
- cancels: `Core/EffCancel.lean`;
- typed handled programs: `Core/EffExamples.lean`.

Stage 4 is implemented:
- the unwinding forms of the borrows: `Core/EffBorrow.lean`, with `[TR]` 6.150 and the family
  frames at `wpG` (`Core/Reborrow.lean`, `Core/SliceFrames.lean`);
- `F_Σ A` as an observation leaf: `Core/Types.lean`, `Core/Relation.lean`, `Core/NuRel.lean`,
  `Core/Nu.lean`, `Core/Computation.lean`.

Stage 5 is implemented:
- the six programs, typed and run: `Core/EffPrograms.lean`;
- §19's steps in `Support`'s interpreter: `Support/Dynamics/Interpreter.lean`;
- the abortive operations' lowering: `Backend/Clos/Unwind.lean`;
- the kernel programs at every stage: `Backend/Kernel.lean`, `bcc kernel`,
  `scripts/compile-kernel.sh`.

The lowering of control operations and cancels is implemented (#205): `Backend/Clos/Capture.lean`,
with every kernel program at every stage (*Lowering*).

Frame deadness (*Cancels*, decision D1 of 2026-10-08) is implemented: the dead region `Kont.dead`,
`κ`'s cancel branch, the cancel state of the kept error alone and `[cfin-cancel]` in
`Paper/S3_Dynamics/Definitions.lean`; the interpreter; unique decomposition and determinism with
`[cfin-cancel]` in `Core/Steps.lean`; `cancelOwed` at the dead region and the empty error table in
`Core/EffDefs.lean`, and the cancel lemmas, `ewp_handle` and `then_compatC` in
`Core/EffRules.lean`; the runs and the refutation of the abortive-row `[then]` in
`Core/EffCancel.lean`; the lowering keeps the first error with no mask (`Backend/Clos/Capture.lean`,
`Backend/Clos/Unwind.lean`). The typing of finalisers with effects (decisions D2, D3) is §27.

Entry 24 (§25) is implemented: the machine in `Paper/S3_Dynamics/Definitions.lean` (`hndVal`,
`capTag`, `kappaAt`, `kappaC`, `kappaCell`, `Head.hop`), the interpreter, `Core/EffRules.lean`
(`ewp_kappaCell`, `ewp_kappaC_resume`, `ewp_kappaC_cancel`, `ewp_handle`), `Core/Fundamental.lean`,
the checker (`rEffHandle`) and `Backend/Clos/Convert.lean`.

Entry 25 (§26) is implemented: `Core/Fundamental.lean` (`CDerives.lamDead`, `lamDead_compatC`),
`Core/Weaken.lean` and the checker (`lamIt`, `rLamDead`, `Frontend/Check/`).

Entry 23 (§24) is implemented: `Core/PolyLet.lean` (`letPoly_compatC`), `Core/EffFin.lean`
(`handleV_compatC`, `ewp_handle_vals`, `then_compatC`) and `Core/Fundamental.lean`
(`CDerives.letPoly`, `CDerives.effHandleV`, the theorems `CDerives.effThenA` and
`CDerives.effHandle`); the checker types a finaliser at `F 1` (`Frontend/Check/Steps.lean`,
`Frontend/Check/Rules.lean`, `Frontend/Check/Checker.lean`). The copy is the polymorphic let's
premise term in `Core/InsertDead.lean` and `Core/LetCopy.lean` (`CDerives.letPoly_copy`), read off
a checked program by `checkProgram_letPoly` (`Frontend/Check/Program.lean`).

Entry 26 (§27) is implemented in the kernel: cancel rows in `Core/Types.lean` (`OpSig.fin`,
`CTy.eff`'s `fin`, `CTy.rowOf`, `capB`); the entries' cancel obligations in `Core/EffDefs.lean`
(`OpEnt.fin`, `cancelOK`, `cancelTab`, `cancelObl`) and `Core/Relation.lean` (`finObl`); the order,
`⋈`, the cancel lemmas and the compatibility of `[sub]`, `[let]`, `[then]` and `[handle]` in
`Core/EffFin.lean`; the rules in `Core/Fundamental.lean` (`CDerives.effThen`, `effHandleV`); the
checker's empty cancel rows (`Frontend/Check/`); the typed cancel programs, and the programs the
typing rejects (`not_der_progT`, `not_der_progNCrecT`, `not_der_e7c`), in
`Core/EffCancelTyped.lean`, by inversions of `CDerives` that read the rows a computation is read at
(`der_hndJ`, `der_thenJ`, `der_performJ`, `der_raiseJ`, `der_letJ`, `JR.rowLe` in
`Core/Inversions.lean`). The backend rejects a finaliser that may suspend
(`Backend/Clos/Capture.lean`).

The facts a statement about every run of a program reads (§3, §13, §19), with no change to
`CDerives`, the machine or the relation: a run through an evaluation context splits where the
inner term stops stepping (`steps_plug_split`, `step1_plug_of_step`), and a context is determined
by the non-value it holds (`plug_inj_ctx`), in `Core/Steps.lean`; a typed term is closed at its
context (`closedAt_of_derives`), and a run from a closed term whose stored values are closed keeps
both closed (`closed_steps`), in `Core/Closed.lean`; `runM` computes a run at a finite memory,
deciding each step (`look`, `look_sound`), and every run it computes is a run of the machine
(`runM_sound`, `runM_val`), in `Core/Run.lean`.

The handler laws (§19 *Laws*) are machine lemmas in `Core/EffMachine.lean`, with no change to
`CDerives`, the machine or the relation: H-ret, H-op at the capture cell (`catch_unr`,
`catch_cell`, `catchEv_cell`, `kappaC_resume`, `kappaC_cancel`, `kappaC_cancel_lin`,
`use_frees_cell`), H-fwd (`catch_fwd`, `fwd_resume`, `fwd_abort`), `[unwind]`, `[then]` and
`[finalise]`, and an abort's absorption of the frames it passes (`abort_absorbs`).

Safety (§19 *Laws*) is stated of the runs of typed closed programs, with no change to
`CDerives`, the machine or the relation: `effSafe_closed`, `LiveOK` and `liveOK_closed` in
`Core/EffSafety.lean`, and leak freedom at a persistent answer (`leakFree_closed`) in
`Core/EffPrograms.lean`.

Decision R (§19 *Typing*) is implemented, with no change to `CDerives`, the machine or the
relation: `EffCtx`, `RowAt`, `CDerivesAt`, `CDerivesAt.toCDerives`, `CDerivesAt.ofEffFree`,
`sig_prefix_of_rowAt`, `hndTags_of_rowAt` and `EffCtx.NoUnrExn` in `Core/Tied.lean`; the checker
builds every derivation tied (`Frontend/Check/Tied.lean`, `Frontend/Check/Rules.lean`), and
`checkProgram_tied` and `checkProgram_tiedAt` read it off (`Frontend/Check/Program.lean`). The
restriction to affine abortive operations (§18) is the checker's (`elabRow`,
`Frontend/Check/Elab.lean`; `sigsOkB`) and the elaborator's (`Frontend/Elab/Effects.lean`).

The names a run raises (§19 *Typing*) are stated as a run invariant in `Core/RaiseNames.lean`,
with no change to `CDerives`, the machine or the relation: `Expr.RaiseOK`, `HeapRaiseOK`,
`raiseOK_step1` and `raiseOK_steps`; a tied term is at its effect context's names
(`EffCtx.Names`, decided by `rcE`; `raiseOK_of_derivesAt`), its runs from the empty memory stay at
them (`raiseOK_reach`), and every cancel they reach keeps errors of those names (`KCfinNamed`,
`CancelsNamed`, `cancelsNamed_of_derivesAt`).

A continuation's use (§19 *Laws* item 4) and the programs no derivation types (§19 *Programs*) are
stated by inversion of `CDerives`, with no change to `CDerives`, the machine or the relation: the
inversions (`fv_live`, `der_var`, `der_app`, `der_lam`, `der_swap`, …) and `refuses_R_clauses` in
`Core/Inversions.lean`, and `not_der_at05`, `not_der_at06`, `not_der_at08`, `not_der_at13` and the
typed control `at08Once` (the kernel program `at08-once`) in `Core/Rejections.lean`. Each inversion
is an induction on `CDerives`, so a rule added to `CDerives` adds a case to each
(`Core/Inversions.lean`, *Cost*).

The effect properties' programs (§19 *Programs*, *Laws* item 3) are `Core/EffTier1Programs.lean`,
each with a derivation tied to its effect context and a run computed by `runM`, with no change to
`CDerives`, the machine or the relation; those the backend compiles are kernel programs
(`Backend/Kernel.lean`, their counts in `corpus/kernel-counts.expected`).

The unwind and the cancel (§19 *Laws* items 5 and 6) are stated of Core's machine in
`Core/EffCancelRuns.lean`, with no change to `CDerives`, the machine or the relation. Read
prefix-closed over paths (`Path`): `unwind_prefix` (`UnwindTr`) and `cancel_prefix` (`CancelTr`),
at finalisers typed at rows of abortive operations (`FinRow`, `finAlone_of_finRow`,
`finOK_of_finRow`). On complete runs: `finaliserOrder_at` and `finaliserOrder_A` (`CancelRun`,
`UnwindRun`, `FinaliserOrder`), given `FinAloneAt`.

Entry 27 (§28) is implemented: the stratified table, the stop lemma and BOXED-κ's compatibility in
`Core/EffBoxed.lean`; the rule `CDerives.effHandleVB` and `stop_lemma` in `Core/Fundamental.lean`,
`CDerivesAt.effHandleVB` and `CDerivesAt.effHandleB` in `Core/Tied.lean`, a case in each induction
over either; the inversions at `clausesTyO` (`Core/Inversions.lean`); the checker
(`clausesReadBoxed`, `ansOutlivesB`, `rEffHandleB`, `TiedDer.effHandleB`, `Frontend/Check/`).

Entry 28 (§29) is implemented: `Core/PinDerives.lean` and `Core/PinFundamental.lean`, generated by
`scripts/gen-pin.py` (`CDerivesP`, `fundamentalC_pin`, `adequacyC_pin`, `adequacyD_pin`,
`adequacyD_pin_safe`, `CDerivesP.ofC`), `Core/PinLaw.lean` (`PinStop`, `PinLoop`, `PinLaw`); the
checker's derivations (`TiedDer`, `Frontend/Check/Tied.lean`), R1 (`Frontend/Check/Pin.lean`,
`withbor2r` in `Frontend/Check/Checker.lean`), the sugar (`relaxedC?`, `Frontend/Sugar.lean`), the
core form (`Frontend/Syntax.lean`, `Frontend/Parser.lean`, `Frontend/Print.lean`), and the reports
(`Pins.assurance`, `Frontend/Check/Program.lean`; `typingReport`, `Backend/Driver.lean`). No change to
`CDerives`, the machine or the relation.

Entry 29 (§30) is implemented in `Frontend/Elab/Effects.lean` (`blockArgs`, `blockCall`,
`blockParamCall`, `withBlocks`, the copies' blocks, `St.perTurn`, `HInfo.boxK`), `Frontend/Sugar.lean`
(`forData`'s `rowLoop`, `hndCtlC` at `clausesTyB`, the argument of an effectful call bound at its
parameter's type), `lib/async.bc` and `Backend/Clos/Unwind.lean` (`rcG`), with no change to
`CDerives`, `Core/`, `Paper/` or `Support/`.

---

## Changelog

- **0.57** (2026-10-15) — §30 (new): effectful blocks at the surface (#161, called-only: a
  closure passed at a parameter of function type performs at the sites where it is written, and
  the callee is copied at the block's row; its type names no effect), a counted loop whose body
  resumes at a `with`'s site as a loop at the row (`bounded_fix` over the count; §16 *Effectful
  bodies* narrowed, generators unchanged), BOXED-κ from a surface handler whose clause unboxes `k`,
  and `lib/async.bc` (`Async`, `spawn`, `resume`, `cancel`, `queue`, `push`, `run_until_empty`).
  The lowering of abortive operations reads a `sel` code's raised keys per projection. New corpus
  programs `async-scheduler` (A1, `24 6 0`), `async-map` (A4, `29 4 0`), `effects-hof-two-rows` and
  `effects-tunnel` (E1 and E6 from source, moved from `pending/`, `0 0 0`), `capture-await-raise`,
  `capture-store-raise`, `rec-await-exhausted`; rejects `block-stored`, `block-capability`. §15,
  §16, §18 and §28 *Open* updated. No change to `CDerives`, the relation, the machine, a kernel
  program, or an existing program's output or count.

- **0.56** (2026-10-15) — §29 (new): a borrow held across a suspension. R1 (`lendR`), with R2
  (`lendLoopR`) and `nilDead`, in the extended judgment `CDerivesP`, generated from `CDerives`;
  `PinLaw`, the named hypothesis of `fundamentalC_pin`, `adequacyC_pin`, `adequacyD_pin` and
  `adequacyD_pin_safe`. The checker emits R1 for a `mut` borrow block of an owned cell whose body
  performs a resuming operation (`withbor2r`), returns a `CDerivesP` derivation, and a `CDerives`
  one when no relaxed rule is used; `bcc check` prints the program's assurance and `bcc trusted`
  lists it. No change to `CDerives`, the machine, the relation or the statement of `fundamentalC`,
  `adequacyC` or `adequacyD`; the checker's soundness theorems take `pins = []`.

- **0.55** (2026-10-14) — §28 (new): BOXED-κ, `[handle]` whose capturing clauses receive their
  continuation boxed at `@d`, given that the handled computation's context and every non-abortive
  answer type of its row outlive `@d`. `CDerives` and `CDerivesAt` gain `effHandleVB`, its case in
  `fundamentalC` `handleV_compatCB`, by the stop lemma (`stop_lemma`), with no new invariant. The
  inversions read a clause tuple bare or boxed (`clausesTyO`), and every refutation of §19 and §27
  stays proved. The checker emits the rule at `handle_with` when the clauses' type boxes `κ`. New
  corpus programs `sched-a`, `sched-a-div`, `sched-b` (counts `63 18 0`, `31 5 0`, `64 18 0`) and
  rejects `sched-b-div`, `sched-c-equal`, `sched-c-outside`, `boxed-kappa-context`,
  `boxed-kappa-answer`. No change to the machine, the relation, an existing program's output or
  count, or the statement of any theorem.

- **0.54** (2026-10-13) — §26 *Baseline*: the checker emits `[λ-dead]` for `fun (x : 1) -> M` at
  `1 -o F_Σ B` whose body does not use `x`, and `[λ]` otherwise; every program erases as before,
  and a callback whose answer is a `!` promotion, which `[λ]` does not type, is accepted
  (`corpus/core-callback-dead.bc`, counts `0 0 0`). §24 *Theorems*: a term holding a closed
  λ-value is `[let-poly]`'s premise term for the let that binds it once, by weakening by consumed
  slots inside a context (`CDerives.insert_dead`, `CDerivesAt.insert_dead`); the let's body is
  computed (`Expr.unfill`, `subst_unfill`), and a derivation of the term gives the let's
  (`CDerives.letPoly_copy`, `CDerivesAt.letPoly_copy`); E1's, E2d's and E10's copies unfill to
  their lets' bodies (`threeUses_unfill`, `sumGenUses_unfill`, `timeoutUses_unfill`). §18 *Rows*
  and *Baseline*, §24
  *Baseline*: the checker's copies, a `def` checked at each use, are that premise term, and a
  checked program's derivation gives the let's (`checkProgram_letPoly`); the checker does not emit
  `[let-poly]`. §18 *Open* and §24 *Open*: the effect properties E1, E2d and E6 from source wait for
  effectful callbacks (#161), recorded as pending programs (`corpus/pending/effects-hof-two-rows.bc`,
  `effects-sum-gen.bc`, `effects-tunnel.bc`). `DecidableEq` on `Expr` is derived in
  `Core/LetCopy.lean`, where the checker reads it. No change to the machine, the relation,
  `CDerives` or the statement of any theorem.

- **0.53** (2026-10-13) — §24 *Lowering*: a `[let-poly]` let whose uses are at different rows is
  lowered per use, as its β-reduct. The backend finds the rows by converting every such let as its
  β-reduct, its uses marked, and comparing what the lowering's analysis finds of each use; a let
  used at one row converts as before, and every corpus program and every earlier kernel program
  compiles to the same WebAssembly (`Backend/Clos/Poly.lean`). §24 *Open*'s lowering gap is
  closed: `hofTwoRows`, `sumGen` and `timeoutProg` are the kernel programs `hof-two-rows`,
  `sum-gen` and `timeout`. §19 *Programs*: E4 under a handler of `tick` that resumes,
  `deepGenPlain`, typed and run (`dAt_deepGenPlain`, `deepGenPlain_run`), is the kernel program
  `deep-gen-plain`; the shape `poly-id` is a let whose uses differ in row only through what it
  answers. Their counts are measured, each zero (new rows of `corpus/kernel-counts.expected`; no
  existing row changes). §24 *Open*: a let used at different value types, and one used at one row
  with different closures. No change to the machine, the relation, `CDerives` or the statement of
  any theorem.

- **0.52** (2026-10-13) — §19 *Programs*: the effect properties as Core programs. E1, E2d, E4,
  E5 in both orders, E6, E7a/b/d, E8b, E9a/b/c and E10, each a closed term with a derivation tied
  to the effect context `ΞE`, which has no unrestricted abortive operation, and a run computed by
  `runM` to its answer at the empty memory (`Core/EffTier1Programs.lean`); a tied derivation
  weakens by consumed slots (`CDerivesAt.append_dead`). §19 *Laws* item 3: static per-site names,
  `tunnel`. §24 *Theorems*: `[let-poly]` types E1, E2d and E10's let-bound functions; §24 *Open*:
  their let forms are not lowered when the uses are under different handlers. §26: the programs'
  callbacks are `[λ-dead]`'s. §27 *Typing*: E5 and E9 are Core programs at an affine `exn`. New
  kernel programs `deep-gen`, `nested-log-outside`, `nested-fail-outside`, `tunnel`, `e7a`, `e7b`,
  `e7d`, `e8b`, `stored-k-resume`, `stored-k-cancel`, `stored-k-fin`, their counts measured (new
  rows of `corpus/kernel-counts.expected`; no existing row changes). No change to the machine, the
  relation, `CDerives` or the statement of any theorem.

- **0.51** (2026-10-13) — §19 *Laws* item 6 and §27 *Programs*: the rejections of decision D3 are
  Core theorems, each by inversion of `CDerives`. `progT` has no derivation at a row without `2`,
  `progNCrecT` none at all, and E7c (`e7c`) none at a row without its inner `exnᵢ`; at the row of
  `exnᵢ`, E7c is typed by a tied derivation (`Core/EffCancelTyped.lean`). The inversions read the
  rows a computation is read at: `[handle]`, `[then]`, `[perform]`, `[raise]`, `[let]` and `bind` at
  their conclusions, and the rules that conclude with their premise's term only grow rows
  (`Core/Inversions.lean`). §19 *Laws* item 5: `cancel_prefix`'s hypotheses are met by a program
  whose effect context has no unrestricted abortive operation, `progOutT` at an affine raise of `2`
  (`progOutTA`, `Core/EffCancelRuns.lean`). No change to the machine, the relation, `CDerives` or
  the statement of any theorem.

- **0.50** (2026-10-13) — §19 *Laws* item 4: a continuation is used as its qualifier allows. At a
  resuming linear or affine operation a clause that drops `κ`, resumes it twice, or cancels and
  then resumes it has no derivation, and at a linear one neither has a clause that cancels it;
  `forget κ` has none at `1`. §19 *Programs*: four programs no derivation types (`at05`, `at06`,
  `at08`, `at13`), each by inversion of `CDerives` (`Core/Inversions.lean`,
  `Core/Rejections.lean`), and `at08`'s typed control, the kernel program `at08-once`. §24 *Open*
  keeps OQ-7 alone: S5 at every instance of its parameter is in *Theorems*, the use of a continuation
  is §25's, and Core's row polymorphism by `[let-poly]` is in *Typing*. No change to the machine,
  the relation, `CDerives` or the statement of any theorem.

- **0.49** (2026-10-13) — §19 *Laws* items 5 and 6: a cancel is not interceptable and the cancelled
  region's frames are dead, and the finally law, read on every run. From a raise pending under
  finaliser frames, and from the start of a continuation's cancel run, every path is a prefix of
  the trace that fires the frames' finalisers innermost first, each running alone; a finaliser's
  raise supersedes an unwind's, a cancel keeps the first error and passes a running finaliser's
  `cfin`, and the canceller gets `()` or the kept error (`Core/EffCancelRuns.lean`). The hypothesis
  is a typing of each fired finaliser at a row of abortive operations; a finaliser that performs is
  *Open* (§27). §24 *Open* no longer lists other instances of S5's parameter. No change to the
  machine, the relation, `CDerives` or the statement of any theorem.

- **0.48** (2026-10-13) — §19 *Typing*: the names a run raises. A tied term is at its effect
  context's names, no step leaves them, and every cancel its runs reach keeps errors of those names
  (`Core/RaiseNames.lean`). No change to the machine, the relation, `CDerives` or the statement of
  any theorem.

- **0.47** (2026-10-13) — §19 *Typing* (decision R): a program gives each operation one
  signature. `CDerivesAt Ξ` is `CDerives` with `[perform]`, `[raise]` and `[handle]` reading rows
  tied to the effect context `Ξ`, and a tied derivation is a `CDerives` derivation. The checker
  builds every derivation tied to its program's effect context, and rejects a program whose rows
  give one operation two signatures. §18 (decision 63's restriction, 2026-10-12): an abortive
  operation is affine, so `multi ctl op(…) -> never` and an unrestricted operation answering `0` in
  a core row are rejected; §27 records E5 and E9 at an unrestricted `exn` as restricted out and no
  longer *Open*. §19 *Laws* item 9 states that a typed closed program's raises are caught. No
  change to the machine, the relation, `CDerives` or the statement of any theorem; every corpus
  program checks as before.

- **0.46** (2026-10-12) — §19 *Laws*: the equations and semantic choices the effect system is
  decided to satisfy, each with the Core theorem that states it: the deep handler laws at the
  capture cell and algebraicity at an abortive operation (`Core/EffMachine.lean`), and the safety
  of a typed closed program's runs (`Core/EffSafety.lean`, `Core/EffPrograms.lean`), over the run
  facts of `Core/Steps.lean`, `Core/Closed.lean` and `Core/Run.lean`. No change to the machine,
  `CDerives`, or any statement.

- **0.45** (2026-10-09) — §27 (decisions D2 and D3 of 2026-10-08): finalisers with effects. Each
  operation whose continuation may be cancelled carries a cancel row, what that cancel may do;
  `[sub]` lets cancel rows only grow, `κ`'s cancel branch is at `F_{F_i ⊕ Σ} 1`, and `[sub]` where
  the cancel is invoked asks a finaliser's raises and operations to have a live instance there.
  `[then]` types its finaliser at its own row, each cancel row of its computation above the cancel
  row combined with the finaliser's (`⋈`); its unrestricted premise is read at some depth, and the
  errors pending at the finaliser are persistent when the finaliser's row has an unrestricted
  operation. §24's `[then]` is a derived rule. §19's *Typing* and *Finalisers that perform
  operations* point to §27. No change to the machine, `wpTS`, `wpG`, `ewpTS`, `[let]`, the
  statements of `fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD` or any borrow rule, and
  every existing derivation types at empty cancel rows.

- **0.44** (2026-10-09) — §19 (decision D1 of 2026-10-08): deadness by frame. `κ`'s cancel branch
  runs the cancelled region with its handler frames and cancel delimiters removed (`Kont.dead`),
  so a dead frame catches nothing, and a finaliser's raises and operations reach the nearest live
  instance of their name. The cancel state is the kept error alone, the first winning (`N` and the
  by-name suppression removed). A cancel that reaches a running finaliser's `cfin` keeps that
  finaliser's cancel's error, the earlier one (`[cfin-cancel]`). `prog` now ends at a raise no
  handler catches, and leaves the compiled kernel programs; `cancel-reentered` and
  `cancel-propagated` join them. The lowering keeps the first error (the mask is removed).
  `then_compatC` takes its finaliser at the pure row (§24's rule); the abortive-row rule fails
  under dead regions (`not_thenAbort_compatC`). No change to the statements of `fundamentalC`,
  `adequacyC`, `fundamentalD`, `adequacyD` or any borrow rule, and every typed program runs as
  before.

- **0.43** (2026-10-08) — §26 (decision E): `[λ-dead]`, a λ whose binder is dead at `1 ⊸ F_Σ B`,
  so a closed callback body at any row is passed as `λ_. M`. No change to the machine, the relation
  or any borrow rule.

- **0.42** (2026-10-08) — §25 (decision S6): the capture cell. At a linear or affine operation
  `[op]`'s `κ` owns a unit cell, allocated by the ordinary allocator and freed when `κ` is used; a
  linear `κ`'s cancel branch has no step. The handler value carries its operations' qualifier tags,
  which `[handle]` writes. §19's *Terms and machine* and *Typing* revised, §24's *Open* revised. No
  change to the relation, the effectful `wp` or any borrow rule. §25's *Open*: S4's catch law fails
  as written at tier 1's typing; S6 there is reduced to two ownership properties of the cell.

- **0.41** (2026-10-07) — §24 (decisions D3, D5): the polymorphic let `[let-poly]` (a closed
  λ-value bound by substitution, so one function is used at several rows), the general `[handle]`
  (§19's printed rule: the handler a value form over a persistent context; the two-variable form is
  its instance), and `[then]`'s finaliser at the pure row (option A). §19's `[then]`, *As built*
  and *Finalisers that perform operations* revised. No change to the machine or the relation.

- **0.40** (2026-10-02) — §23 (#243, from #241): non-strict outlives. The box rule of the outlives
  judgment and the side condition of the borrows that lend a payload `mut` take `⊑`, extensions
  read against the paper's model (`Paper/` unchanged). `main` runs under a lifetime of its own,
  `'main`, and an undetermined lifetime argument is `dom`; a cell of no words allocates nothing; a generic function's lifetime parameter may be
  bounded by a type parameter, `where S: 'c`. §22's *Bounds* and *Open* revised. Decision 61.

- **0.39** (2026-10-02) — §22 (#239, from #236): the affine closure. §7's positivity admits an
  observation that takes a closed argument (`A ⊸ D`) and a boxed rest (`[@a] U X`), and the
  affine closure `Aff^c A B ≜ νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`, with observations `call` and
  `close`, is an instance: a library declaration (`lib/aff.bc`) with derived introduction, call,
  call through `Mut`, close and coercion rules. A `type` declaration may take type and lifetime
  parameters. §2's closure row is the new type; §7 and §12 name it. No new former, rule or index.
  Decision 60.

- **0.38** (2026-10-01) — §21 (#229, #216): closure conversion at the seams. A recursive group is
  the bounded fixed point of its generator, taken at the record of its members and called
  directly: the `rec` operation and its site are removed. A recursion may use an answering
  capability (its environment, passed with the argument), perform an operation that resumes, and
  have members with different result types. Layers are transformers of the generator, `with L
  { … }`. A handler whose operations are all abortive runs its clauses after it, so they use its
  arguments and the capabilities in scope (`default` takes an owned value); a handler whose
  operations resume has a state, its parameters that are not `!` and the capabilities its clauses
  use, and `k(v)` resumes. §20 revised; decision 24 revised; decision 59.

- **0.37** (2026-10-01) — §20 (#188, stage 3; #158): recursion as an effect. A function that
  calls itself, or functions that call one another, is a recursive group; its calls of itself are
  its `rec` operation, and a driver chosen at the call site runs it. `bounded`, the default, is
  the kernel's new constant `bounded_fix` (one `CDerives` rule and one machine step, sound by
  induction on the budget at every row): a native recursion with a budget of depth whose end
  performs `Exhausted` (`lib/rec.bc`), an abortive effect that unwinds. `deep`, the heap driver,
  keeps first-order frames in one growable buffer and is div. §16: a `for` over data whose body
  performs an operation that resumes is a div loop over the source's cursor. §19: a closed clause
  that resumes with an answer computed under a finaliser that cancels the continuation is a
  direct call; abortive payloads are variants. Decision 24 revised; decision 58.

- **0.36** (2026-10-01) — §15 rewritten (#188, stage 2): generators on the iteration effect.
  `Yield[T]` (`lib/yield.bc`, `ctl yield(x: T)`) is an ordinary library effect; a generator is a
  function that performs it. A `for` over a call of one is a handler site whose operation threads
  the loop's variables and whose clause is the loop's body, `break` and `return` cancelling the
  continuation; total when the generator does not loop. A call where `U (pull A B R)` is expected
  is the stored generator, codata whose handler keeps the continuation. A body at a row that loops
  is one state machine of `Loop_Σ` that runs nothing until observed; `while` and `loop` are loops
  of any div body, and a loop's body may loop except a counted loop's or a clause. The `gen`
  former, `gen fn`, `gen { }`, `yield from`, callbacks that yield, the generator machine and its
  fallback to nested binds, and `lib/gen.bc` are removed; delegation is a call. The adapters
  are generic generators over stored generators. Capture finds suspension per projection and
  keeps one code per suspension; a finaliser frame's clauses are one code. A generator that holds
  a capability across a `yield` is pending (affine continuations have no residual).

- **0.35** (2026-10-01) — §18 (#188, stage 1): control effects at the surface are §19's. An
  effect's operations are answering (`fn`) or control (`ctl`, `linear ctl`, `multi ctl`); a
  control handler names its body's type and its answer, and each `with` of one is a `handle` with
  a static name of its own, resolved lexically; a function with a row is copied per assignment of
  its effects to the handlers and sites in scope, with the sites' operations as its row. Errors
  are the library effect `Fail[E]` (`lib/fail.bc`) with `to_result`, `default` and `map_err`;
  the built-in `Fail`, `try`, `catch` and `map_err` forms and the sum schema are removed. An
  abortive operation in a counted loop's body is handled at the step and performed again after
  the loop; in a borrow block's body, the block is the unwinding borrow. The textual core reads
  `F[…] A`, `perform[n.i]`, `abort[n.i]`, `handle_with[n]`, `unwind` and the unwinding borrows,
  and the certifying checker builds §19's derivations, inserting the drop glue.

- **0.34** (2026-09-30) — §19, *Lowering* (#205): a tail-resumptive operation, whose handlers
  all have one closed clause that resumes in tail position and neither suspends nor raises, is a
  direct call of the clause. A tail call shares its caller's convention only when it closes a
  loop of tail calls or the caller has no resumption point of its own; any other tail call is a
  resumption point, so a call reaches one resume code and does not dispatch.

- **0.33** (2026-09-30) — §19, *Lowering* (#205): control operations are lowered to state
  machines. A code that may suspend answers its outcome; its state is a flat `n`-ary sum per
  resumption point, a caller's holding its callee's suspended computation; a handler drives its
  body; `κ` resumes or cancels, and a cancel runs the state's finalisers innermost first, keeping
  the first finaliser error of a name outside the region (decision C). Recursion through a
  resumption point allocates one frame object per level, a call of several suspending codes
  dispatches, and an unrestricted `κ` is copied. Every acceptance program compiles at every
  stage; the lowering adds no allocation or dispatched call to its hand-written equivalent's.

- **0.32** (2026-09-30) — §19, stage 5 (#186): the six acceptance programs, typed, run by
  `adequacyD` and observed by `Support`'s interpreter (which gains §19's steps). The backend
  lowers the abortive operations to branch-per-call propagation (`Unwind`). `bcc kernel` compiles
  `Core`'s kernel programs at every stage. The lowering of control operations is *Open*.
- **0.31** (2026-09-30) — §19, stage 4 (#186): the unwinding forms of `withbor` 1–3, `withload`
  and the slice borrows, at a callback row of abortive operations with closed argument types
  (`Row.Unwind`); the finaliser is a closed term at `src ⊸ F 1`, the source's destructor at the
  elaborator; `withswap` has none. `F_Σ A` is an observation leaf of `ν` codata, and
  `Loop_Σ A B` is positive.
- **0.30** (2026-09-30) — §19, *Cancels* (#186): a cancel is not interceptable. The region's
  handlers are dying and catch nothing. A finaliser's error during a cancel is re-raised at the
  canceller (the first, of a name outside the region; the rest are suppressed). Machine:
  `cfin`, `[finalise-cancel]`, `[cfin-ret]`, `[cfin-raise]`, `[cancel-raise]`. `[then]`'s
  finaliser is at `F_{Σ^abort} 1`. The case that motivates it is `Core/EffCancel.lean`.
- **0.29** (2026-09-30) — Entry 18 (§19, #186): native capture.
  - **Operations** are answering (a call on a capability, §18) or control (captured).
  - **Control operations are named per handler site**: static names, rows of names, and the
    nearest enclosing handler of the name; forwarding and named instances follow.
  - **Kernel additions:** the primitives `perform` and `hnd`; the machine steps `[ret]` and
    `[op]` (deep, over a context free of the name); the returner `F_Σ A`; the rules `[sub]`,
    `[perform]`, `[let]` (control-flow linearity at the unrestricted qualifier) and `[handle]`.
  - **Semantics:** the effectful `wp` `ewpTS` over protocol tables, with `wpTS = ewpTS` at the
    empty table.
  - **Continuations** carry a structural qualifier: linear, affine, or unrestricted (relevant is
    Open). Weakening is a continuation's destructor, unwinding. Abortive operations (answer `0`,
    weakening), used for errors (#168), unwind eagerly. Unwinding uses `ubind` finalisers and
    elaborator-inserted drop glue, and unwinding forms of
    the borrow constants (an unwind crosses a borrow, LIFO, without T1). Every held continuation
    has a `cancel` entry, and a finaliser that raises supersedes the pending unwind (K3 otherwise
    Open).
  - **Divergent effectful programs** are `ν` codata with effectful observations.
  - **Acceptance:** `Log` + `Fail` in both orders, logging and raising inside a borrow, an
    infinite logging loop, `take(n)` early exit, and cancelling a stored continuation.
  - Stated here; the library follows stage by stage.

- **0.28** (2026-09-30) — Effects S1c (§18, #154): the laws `handle_fold` (a handler is the
  state-passing fold of its clauses over the operations performed) and `loop_abort`; the
  acceptance of #18 restated as the laws, the counts and the reports. `bcc check`'s effects
  reports in four kinds (`effect`, `row`, `lowering`, `call`), the lowering shape in Koka's cost
  vocabulary, pinned by `corpus/reports/`. Generic functions with a row; a lend in a `Fail`
  handler's body rejected with a message.

- **0.27** (2026-09-30) — Effects S1b (§18, #153): `Fail`, the error effect: `raise`, `try`,
  `catch`, `map_err`, and written rows `with …, Fail[X]`. A function that raises answers a sum,
  a call of it is a branch, and an abort in a loop's body is the loop's exit (`count_try`). The
  abort law (`abort_passes`, `return_resumes`). Destructors run on abort paths; a value with no
  destructor cannot be abandoned. The library raises (`parse_i32`, `add_checked`, `mul_checked`,
  `str_from_utf8`, `from_utf8`); a fallible fold has the counts of its sum version. K4 recorded as
  open. No kernel, rule or checker change.

- **0.26** (2026-09-30) — Effects S1a (§18, #152): `effect` and `handler` declarations and
  `with h(e) { M }`, defined by elaboration: a clause is `!` code over a `mut` borrow of the
  handler's state run by `withswap`, a `with` is a `withbor` of the state's cell, an operation a
  call of its clause on the capability; rows inferred, a function with a row elaborated once per
  handler. The tail-resumptive law on the elaborated terms (`Core/Handlers.lean`). Borrow blocks
  of a cell or an owned array take `⊓Δ` as their bound, and hand back a cell lent to a nested
  `with`. No kernel, rule or checker change.

- **0.25** (2026-09-30) — Strings S4, revised: the `for` loop (§16). K0′, `count_try`, the
  counted loop with an exit, is a machine step beside `count_fold` (`countTry_compatX`), in the
  checker and the backend. `for x in y { M }` is Rust's pull desugaring, the source turned into an
  iterator by its type: over data (a count `a..b`, a view, `&a`/`&mut a`, an owned array, a sized
  iterator `sized D S A`) it is `count_try` over the length of the data, computed when the loop
  starts, and total; any other source is a drain, div. `break`, `continue` and `return` are the
  step's exits; `for … else { d }` gives the loop's value when the source ends; a generator that
  finishes with `0` never ends, and a loop over it has `break`'s value alone. The completeness
  lemma: the bound equals the number of elements (`Support/Dynamics/Completeness.lean`). Sized
  iterators and their adapters (`lib/iters.bc`); adapters of one name chosen by type; generic
  `&a`/`&mut a` at a view parameter (§9). `bcc check` reports
  each loop: total and its bound, or div. `absurd V` erases to `case V {inj₁ x. x | inj₂ y. y}`.
  §14 and §15 Open: the stale lines on generic and div functions corrected.

- **0.24** (2026-09-30) — Strings S5 (`docs/strings-slices-design.md`). §11: bytes are `U8`
  (`read_byte`, `write_byte`, the byte list `μX. 1 ⊕ (U8 ⊗ X)`), and two bulk externs,
  `write_all` and `read_into`, whose models are counted loops of the byte operations'
  (`writeAll_meets`, `readInto_meets`); their host implementations are one `fd_write` or
  `fd_read` per view. Entry 16 (§17): buffers (`lib/buf.bc`, stage A, a filler by type), text
  (`lib/text.bc`, `lib/textio.bc`), string and character literals, `box buf/string/array`,
  borrow blocks on buffers and literals, borrow blocks that hand back what they assign, lend and
  the capabilities they use, and template instances at types with lifetimes; literals are
  lowered to read-only data and literal views to pointers into it. No kernel, rule or checker
  change.

- **0.23** (2026-09-29) — §15, *Generic functions*: `fn f[A, …]` with a surface body is a
  template instantiated at each use, as generic generators are; `fn f<'a, 'b, …>` declares
  lifetime parameters; at a call, type arguments are inferred by first-order matching against
  the arguments and the expected result, each lifetime parameter from its own argument (the meet
  when two disagree), and `unbang` is inserted. `lib/slice.bc` is written in the surface, and
  its calls write neither types nor lifetimes. No kernel, rule or checker change.

- **0.22** (2026-09-29) — Strings S3 (`docs/strings-slices-design.md`). §9: a borrowed family
  is split at a run-time index into two families at its lifetime (`slice_split_imm`,
  `slice_split_mut`, the machine step `split`, K3), the empty family `slice_empty_imm`/`_mut`,
  and a `mut` family is written at an index keeping the rest (`slice_replace_mut`,
  `slice_swap_mut`, by Mut Anti-Frame, K5). §12: `ArrayMut @a A` has a destructor, derived from
  `slice_get_mut` and `forget`. The slice library `lib/slice.bc` (`include slice`), generic in
  the element type, with `sort`, `binary_search`, searches, comparisons and the iterators
  `iter_imm`/`iter_mut`. The backend lowers `split` to a compare and pointer and length
  arithmetic.

- **0.21** (2026-09-29) — Strings S1–S2 (`docs/strings-slices-design.md`). §9: the family
  relation carries the length bound `c < 2³¹`; slice borrows `slice_borrow_mut` and
  `slice_borrow_imm` lend an owned array as a family of leaf borrows with no cell (K2, from
  `experiments/PositiveArrays`), and `slice_get_mut`/`slice_len_mut` act on a `mut` family (K4);
  a borrow block on an array lends it so. §8: the byte `U8` (`Width.w8`), its literal and its
  conversions `wrap8`/`extend8_u`; the grouped operations take `0` at `w8`. Entry 15 (§16): the
  counted loop `count_fold`, a machine step (`count`) so that it is total at every host;
  `div_fuel` counts with it. The backend lays out byte slots, and an empty array allocates
  nothing.

- **0.20** (2026-09-29) — §14, §15: one state machine per body (#109 item 8). Every generator
  body and every div body is one `unfold` whose state has a summand per resumption point, and
  whose step is one code with a `case` on the state; `gen_bind`, `gen_bind_loop` and `div_bind`
  remain the library's binds, and the elaboration's for the shapes the machine does not cover.
  No generator or div body of the corpus dispatches a call. No kernel, rule or checker change.

- **0.19** (2026-09-29) — Entry 14 (§15): generators, replacing §14's spike subsection (#109).
  `return` and `break` anywhere in a generator's body, a `for` that keeps its finishing value,
  direct-style div calls, `yield from`, `gen { }` blocks and callbacks that yield; generic
  generators, instantiated per call, and the adapter library (`include adapters`); a generator's
  residual is what it holds, `K`; a borrow block that yields is a delegation, rejected by the
  borrow typing (a self-reference). No kernel, rule or checker change.

- **0.18** (2026-09-29) — §14: borrow scopes over loops, per observation (O1, step 1). A
  borrow block whose body loops, `let r = &x` over a loop, and a div function over a borrow are
  elaborated so that each observation borrows the owner again; `lib/lend.bc` has the combinators;
  a call of a function with a lifetime parameter takes the lifetime from its argument. No kernel,
  rule or checker change.

- **0.17** (2026-09-29) — §10: a use that copies recursive data is written `clone(x)`, and an
  unwritten one is an error at that use (#108, decision 39); a generator's loop hands on, at a
  `break`, only the variables what follows it reads. `bcc-counts` reports the deep copies a run
  makes. No kernel, rule or checker change.

- **0.16** (2026-09-28) — The surface's places and conditions (#54, stages 6–7 of
  `docs/typed-elaboration.md`): `&mut x` and `&x` lend a place, by type a move handed back, a
  borrow of a cell, or a cell scoped to the call for a value (`&c` retired for the exclusive
  lend); `*e`; `modify &mut x`; `let mut` with assignment, joins at `match`/`if` and threading
  through `for`; `bool` (`1 + 1`, `inr ()` true), `if`/`else`, `&&`, `||`; the prelude
  (`lib/prelude.bc`: `true`, `false`, `not`), and `include` of the embedded `lib/` modules
  (#59). No kernel, rule or checker change.

- **0.15** (2026-09-28) — Draft 0's expression layer (#54, stage 5 of
  `docs/typed-elaboration.md`): `fn` and `main ->` declarations, `let` with patterns, `match`,
  statements, forces `t!` and `f!(e)`, blocks and closures `{ … }`, borrow blocks and `modify`
  with lifetime and unit elision, integer literals and operators at their operands' width, calls
  of persistent functions without `unbang`, and n-ary tuples, in one grammar with the core,
  elaborated into core. §14's `div_defer`: a block whose body loops runs nothing until it is
  first observed. No kernel, rule or checker change.

- **0.14** (2026-09-28) — §11, §14: a `main` with no externs may return a loop, which the runtime
  drives with no capabilities (`run_io`'s loop wrapper at `Caps = 1`, `ioMainOf`), so a `main`
  that loops but uses no capability is no longer given `stdout` (#54, stage 4). The theorems
  (`IORun.loop_every_run`, `externs_loop_every_run`) are stated at the checked `run_io` and cover
  it unchanged; no kernel, rule or checker change.

- **0.13** (2026-09-28) — §14's specialization reads the callback's type from inference
  (#54, stage 3): any callback whose type is known, including locals, returned callbacks and
  closures, which are elaborated as div bodies when they loop. No kernel, rule or checker change.

- **0.12** (2026-09-28) — §14's elaboration on types (#54, stage 2 of
  `docs/typed-elaboration.md`). The residual is the components of the result with no destructor,
  read off the type; a call of a div function in direct style is any application whose type is a
  loop where that loop is not expected, at any depth, nested calls lifted in evaluation order;
  the variables a `for` threads, and bindings of injections, have inferred types. No kernel,
  rule or checker change.

- **0.11** (2026-09-27) — Entry 13 (§14): divergence as an effect. A div function returns a
  loop, `A ⇒ U(Loop B R)`, with the residual handing capabilities back; the delay bind
  `div_bind` and the fuel handler `div_fuel` as library code over `unfold`; divergence inferred
  in declaration order, `total def` and `div def` markers, `main` div when its body loops;
  direct-style calls, `for` in any function, and specialization of higher-order functions at
  a div callback's type, all elaborated before checking; the totality theorem
  (`total_every_alloc`, `total_run_prefix`, `total_every_run`, `total_no_infinite_run`). §11's
  restriction of `for` to the end of an ambient `main` is withdrawn.

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
