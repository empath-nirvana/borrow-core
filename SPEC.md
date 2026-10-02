# Borrow core — specification

Version 0.38 · 2026-10-01

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
(`vC_outlives`): that is what the side conditions on `A` and `B` pay for. The compatibility
lemmas are `sliceBorrowM_compatX` and `sliceBorrowI_compatX`.

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
Another control effect (async, #52) may reuse it by giving:

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

A type or lifetime that is not determined is an error at the call that names it.

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
- **Callbacks that yield** need effectful callbacks (#161): a closure that performs an operation
  is a computation passed as a value (`corpus/pending/yield-callback.bc`). So do adapters as
  handlers over a computation (`|>` at a computation parameter).
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
machine (§14, §15), one turn per element (`forDataDiv`, `Frontend/Sugar.lean`):

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
(the type `0`) at a qualifier with weakening is **abortive** (§19). An effect may take type
parameters (a control effect only).

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
block that is not run in place, and a function with a row passed as a value (effectful callbacks,
#161; for a fold's algebra that raises, K4 below); a lend `&mut x` in the arguments of a call that
threads a capability; an operation of an answering effect inside a clause of an answering handler;
a function with a row whose written result is a computation (a loop); a second instance of
an effect in a row; type parameters on an answering effect; an effect with both kinds of operation;
a `let mut` declared outside a control `with` and assigned in it, or a place lent in it; abortive
operations of two sites in one counted loop's body; a borrow of a buffer or a literal crossed by
an abort.

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
`fundamentalD` and `adequacyD` keep their statements and cover every elaborated program.

### Open

- Named instances and lexical resolution between two instances of an effect (S2, #155); bundles
  (#156).
- Effectful callbacks, stored or passed (#161), and with them functions over computations
  (`retry`, a handler that re-runs its body, and `|>` at a computation parameter).
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

- `Fail[E]` is `raise : E ↠ 0` at an affine or unrestricted qualifier.
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
  dropped" (#185, `forget_not_lolli`) is answered by the destructor `cancel`, not by a `forget`.
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
  has one protocol.

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
    handle_n e with H    ≜  hnd (n, H) e                    (`.app (.app (.prim .hnd) …) e`)
    M then x. N unwind D ≜  ubind (λx. N, λ_. D) M          (`.app (.app (.prim .ubind) …) M`)

`ubind` is `M to x. N` with a finaliser `D`, which runs instead of `N` when `M` unwinds.

`H = (h_ret, h_op)` is a pair of values, and `n` a literal. Evaluation is argument-first, so `e`
runs under the frame `hnd (n, H) [·]`. A context `K` is **free of `n`** (`Kont.NoHnd n K`) when
none of its frames is `hnd (n, H′) [·]`. It may hold handlers of other names. A context is
**unwind-clear** (`Kont.NoUbind K`) when none of its frames is `ubind _ [·]`. The head steps
below and the cancel steps (*Cancels*) do not allocate:

    (μ, hnd (n, H) v)                  ↦  (μ, h_ret v)                                     [ret]
    (μ, hnd (n, H) K[perform (n, v)])  ↦  (μ, h_op (v, κ))     K free of n, where          [op]
          κ = λy. hnd (n, H) K[y]
    (μ, hnd (n, H) K[raise (n, v)])    ↦  (μ, h_op v)          K free of n, unwind-clear   [unwind]
    (μ, ubind (N, D) v)                ↦  (μ, N v)                                         [then]
    (μ, ubind (N, D) K[raise (m, v)])  ↦  (μ, D (); raise (m, v))   K unwind-clear, m ≠ ⊥  [finalise]

- **The continuation.** The `[op]` step's `κ` is the pair of its entries:

      κ = ⟨ λy. hnd (n, H) K[y] ,  λ_. ccatch (hnd (n, H) K[raise (⊥, (N, none))]) ⟩

  - `⊥` is a reserved name that no program uses, and `N` is the list of names of the
    **cancelled region's** handlers: `n` and those of `K` (`Kont.hndNames`).
  - `ccatch e` is a delimiter that catches only `⊥`.
  - So cancelling resumes `κ` at the operation with an unwind. The unwind runs `K`'s finalisers
    and the unwinding forms of the borrows in `K`, passes the reinstalled `hnd (n, H)`, and stops
    at `ccatch` (*Cancels*).
- **Unwinding runs innermost first.** A `raise` goes to the nearest `ubind` (its finaliser runs,
  then it raises again from there) or to its handler, whichever is nearer.
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
  of `n`. §13's determinism gains the capture cases (`head_det_eff`).

### Cancels

A cancel is not interceptable. The frames of the cancelled region, `hnd (n, H) K`, are being torn
down: nothing in the region resumes, and **its handlers are dying**, so they catch nothing. A
cancel is `raise (⊥, s)` with a **cancel state** `s = (N, err)`: `N` names the region's handlers,
and `err` is the error kept so far (`none` at the start). No handler is named `⊥`, so the region's
handlers never catch the cancel itself. At a finaliser the cancel runs `D ()` under a sixth
primitive, `cfin s`, which catches every `raise` escaping `D`:

    (μ, ubind (N', D) K[raise (⊥, s)])   ↦  (μ, cfin s (D ()))                K unwind-clear   [finalise-cancel]
    (μ, cfin s v)                        ↦  (μ, raise (⊥, s))                                  [cfin-ret]
    (μ, cfin (N, err) K[raise (m, v)])   ↦  (μ, raise (⊥, (N, err′)))         K catching nothing of m   [cfin-raise]
          err′ = err if err ≠ none;  none if m ∈ N;  (m, v) otherwise
    (μ, ccatch K[raise (⊥, (N, none))])  ↦  (μ, ())                            K unwind-clear   [cancel]
    (μ, ccatch K[raise (⊥, (N, E))])     ↦  (μ, raise E)                       K unwind-clear   [cancel-raise]

- **An error raised by a finaliser during a cancel is re-raised at the canceller**, after every
  frame of the region has finalised, where live handlers catch it as any ordinary error. The
  canceller's outcome is "cancelled" (`()`), or "cancelled, and cleanup failed with `E`" (an
  ordinary `raise E` at the canceller's point).
- **Several failures:** the first is re-raised, and the rest are suppressed.
- **An error of a name in `N`** (a handler of the region only) has no live handler at the
  canceller: re-raising it would leave an operation no handler receives. It is suppressed.
- Ordinary unwinding (a `raise` of a name other than `⊥`) is unchanged: a finaliser's raise
  supersedes the pending one and is caught by the live handlers around the finaliser.
- `Core/EffCancel.lean` machine-checks both outcomes. In `prog` the finaliser raises the name of a
  handler inside the region, and the cancel answers `()`. In `prog₃` it raises a name handled
  outside the region, and that handler receives the error.

**Why this rule.** The finaliser's own raises are caught at `cfin`, next to `D`, before any frame
of the region sees them. So the region's handlers need no marking and no removal, and `κ` keeps
the frames it captured. The cancel state rides in the `raise`'s payload, so a cancel is an
ordinary abortive unwind for every existing frame, and `ubind`'s two finalise rules split on the
payload's name. `cfin` is one more catcher frame beside `hnd`, `ubind` and `ccatch`, so unique
decomposition and determinism extend case by case. The frames of a `raise` are the frame lemmas
of any abortive operation.

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

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_Σ A    Δ; x : A, Γ₂ ⊢ N : F_Σ B    Δ; Γ₂ ⊢ D : F_{Σ^abort} 1
    ──────────────────────────────────────────────────────────── [then]
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

- **As built** (`Core/Fundamental.lean`, `CDerives.eff*`; `Core/EffRules.lean`):
  - a row is a list of operations `(n, i, q, A_i, B_i)`, and `F_Σ R` is `CTy.effOf Σ R`;
  - `[sub]` is `RowLe` (every operation of `Σ` is `Σ′`'s);
  - `[raise]`'s argument type drops (`VTy.Drop`);
  - `[then]` asks `Σ`'s names to be nonzero and its keys unique, and `!Γ₂` at an unrestricted
    row;
  - `[handle]` takes `h_ret` and the clauses as variables, the clause of the `j`-th operation at
    index `j` (`Row.ofEff`, `clausesTy`), and `n ≠ 0`.
- **The linear `κ`** is the same `&` pair as the others: the machine builds one `κ` whatever the
  qualifier. Its cancel branch is at `⊤`, so the clause can only resume it.

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
- **A finaliser performs only abortive operations** (and answering calls): `D : F_{Σ^abort} 1`,
  where `Σ^abort` keeps `Σ`'s abortive operations. During a cancel, a non-abortive operation of a
  finaliser could reach a dying handler of the region. Its clause could answer without resuming,
  and the region would then continue as if not cancelled. A plain `[let]` at a row with an abortive or
  affine operation needs `Γ₂` to drop with nothing owned (borrows, `!`, data), since a cancel or
  an unwind abandons it.
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
  is `K[raise (⊥, (n :: names K, none))]` at the table of `F_Σ 1` extended by `⊥`. It is
  owed at `Σ`, the handler's row, because every finaliser error it re-raises has a name outside
  the region, and a finaliser's row names only the region's handlers and `Σ`. So `κ`'s type stays
  `U((B_i ⊸ F_Σ R) & F_Σ 1)`: the cancel entry's row `Σ` already holds the finalisers' abortive
  operations that a cancel re-raises. At an abortive operation the continuation is abandoned, so
  it must hold nothing owned:

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

A finaliser is a computation `D : F_{Σ^abort} 1`, run where its `ubind` stands, so its operations
reach the handlers outside that point:

- it may call answering operations (flush a log, close a socket through its capability);
- it may raise.

If a finaliser raises during an ordinary unwind, the new unwind **supersedes** the pending one:
the pending `raise (m, v)` is in the finaliser's continuation and is abandoned. During a cancel,
the first error of a name outside the region is kept and re-raised at the canceller, and the rest
are suppressed (*Cancels*). So an operation that raises must have an argument that drops with
nothing owned (a `NoOwn` value: data, borrows, `!`). The protocol's `NoOwn` share covers the
abandoned argument.

Richer policies are K3 (#162), and *Open*:

- richer reporting of suppressed finaliser errors (a count, a list, a chain), or a finaliser that
  must not fail (a row with no abortive operation);
- non-abortive control operations in a finaliser;
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
   - **Cancelling a continuation** (`cancel_compatC`) is resuming it into
     `raise (⊥, (N, none))`. Its obligations are the resumption's and the frame lemmas above;
     `ccatch`'s compatibility is `[unwind]`'s, and `cfin`'s is `[finalise]`'s with the kept error
     at the canceller's row. So cancelling a stored continuation needs nothing beyond what storing it
     needed. A continuation stored while it captures borrows is T1 (#172). Once T1 makes that
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
  resolved per code as the codes are monomorphic, and per projection: a call whose argument is a
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

**Cancel** is the state's destructor. The resume code takes `inr mask` and switches on the state:
the callee's `k` is cancelled first (innermost), then the point's finalisers run innermost first,
and every other variable is dropped; borrows' unwinding forms are finaliser frames, so their
lends end here. A finaliser's error is caught (`catchAll`), and the first error whose name is not
in the mask is kept: the canceller re-raises it (`reraise`), and every other one is suppressed,
decision (C) of *Cancels*. The mask is the names of the handler sites reachable from the cancelled
handler's body; it is the region's names `N` exactly when no handler site is reached again from
its own body, which is checked when a finaliser may raise.

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

**Not lowered**, rejected with a message: a name that has both control and abortive operations; a
cancel whose finalisers may raise under a handler site reached from its own body, or under a
handler named `64` or more.

**As built** (`Backend/Kernel.lean`, `bcc kernel`, `scripts/compile-kernel.sh`). Every
acceptance program, with its native variants, `Core/EffExamples.lean`'s two handled programs and
`Core/EffCancel.lean`'s two cancels, compiles through every stage with the same answer and
`live 0`, as do terms for the shapes above (100000 operations of a loop as direct calls, and as
suspensions resumed in tail position, both in constant stack; recursion through a resumption
point; two possible callees; forwarding with and without a cancel; a continuation resumed
twice). The counts (`corpus/kernel-counts.expected`) and the hand-written
equivalents (`corpus/capture-*-hand.bc`):

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
  (K3, #162): richer reporting of suppressed finaliser errors; non-abortive control operations in
  a finaliser.
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

---

## Changelog

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
