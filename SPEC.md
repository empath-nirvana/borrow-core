# Borrow core — specification

Version 0.91 · 2026-10-20

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

### What the checker returns: the typed term

The checker returns a **typed term** `t : TExpr` with its derivation, not an erased term alone
(`docs/compiler.md` §2.3). `TExpr` has one node per rule application: one constructor per rule of
`CDerivesP` (so per rule of `CDerives`, and R1, R2 and `nilDead` of §29), of the same name; one
**derived node** per fixed scheme; and the `use` node of a `def` (below). A node holds

- its judgment, a value type or a computation type;
- its rule's arguments other than its contexts, its proofs and the terms its premises type: binder
  types, rows, operation signatures, lifetimes and lifetime variables, a handler's name, qualifiers
  and cancel rows, constants' type arguments;
- at a split (`Ctx.SplitP`), the use masks of its two parts (`Masks`), as the checker computed
  them;
- at `[handle]` (`effHandleV`, `effHandleVB`), each operation's qualifier and the kind of its
  clause, as the checker classifies it (`ks`, §19 *Clause kinds*), and at every `handle` node the
  site as the elaboration of effects records it (`site`, §19 *Handler sites*) and the frames its
  handled computation holds (`inside`, §19 *The clause's names in the continuation*), which the
  typed rule pins (`inside = te.erase.hin`); the names each clause's own code performs or raises
  are read off the node's clauses (`handlerNames`);
- its source (`TInfo`): the span it was checked from; at a variable its name and whether the
  program writes the use `clone(x)` (§10); at a binding (`x <- M`, `let (x, y) = V`, a `case`'s
  arms) the names it binds;
- one child per premise, in the rule's order.

`TExpr.erase` is the term the node's rule concludes with, from its children's erasures. The
checked term is `Checked.e := t.erase`: the term the backend compiles is the term the derivation
types, by definition. `TDerivesAt Ξ Δ Γ t j` and `TDerivesP Δ Γ t j` are `CDerivesAt Ξ` (§19,
decision R) and `CDerivesP` (§29) with each premise at a child and the conclusion at the node; a
premise that types a term built from other arguments (`thunkV`'s `λN`) carries the equation
between the child's erasure and that term. They project to `CDerivesAt`/`CDerivesP` at
`t.erase` (`TDerivesAt.erase`, `TDerivesP.erase`), so a derivation fixes every field of every
node, and every theorem below, and §19's and §29's, holds of `t.erase` as stated. The node types,
the derivations, the projections and the erasure are generated from `CDerivesAt` and `CDerivesP`
by `scripts/gen-pin.py`, so a rule added to `CDerives` is picked up by rerunning it.

**A split's masks are fixed by its derivation.** A typed rule at a split has one premise its
`CDerives` rule does not: the node's masks are the ones its parts' contexts have
(`SplitMasks Γ₁ Γ₂ u₁ u₂`): a slot a part uses is live in that part's context, and a slot live in
both is used by both. The split is chosen at each liveness by `Fam`, after the node is built, and
`Fam.split` proves the relation at each (`split_lemma`): it gives a slot neither part uses to one
part, never both. So the slots a split gives to both parts, which `Ctx.SplitP` admits only at a
persistent type, are exactly those both masks hold (`TDerivesAt.split_masks`, `TDerivesP.copies`):
that is the copy set, and §10's check reads it off the masks.

Two facts are on the term without being fixed by its derivation: the witness of a side condition
stated as `∃ b, …` (`withbor2`'s, the unwinding and slice borrows', R1's), which is not an
argument of the rule and not a field, and the clause kinds at `[handle]`, which the checker reads
off the clauses' binding, not the rule's premise (`TDerivesAt.kinds_free`,
`Frontend/Check/TFacts.lean`).

**Derived nodes.** A fixed scheme is a node of its own, whose erasure is the scheme's term and
whose typed rule is the lemma that types it, its side conditions the lemma's premises: the
destructor of a type (`dtor`, `dtor_wf`; a recursive type's is a fixed point), a block's allocation
and release (`allocS`, `freeS`, `d_allocS`, `d_freeS`), a block borrow (`withborSM`,
`withborSI`, `withborSM_wf`, `withborSI_wf`) and a family's two-lifetime borrow (`withborF2M`,
`withborF2I`, `withborM2_wf`, `withborI2_wf`), each at a consumed context. A scheme the
elaborator writes is marked on the value it writes (the core form `Val.mark`, printed as the value
it marks, so `bcc desugar` shows the value): the checker checks `V` as written and builds the scheme's node over its typed term, with the
equation saying which instance of the scheme the term's erasure is. A string literal's table
(§17) is such a node (`litFn`, the bytes and `litFnE`), and so are four more, each over the
marked value's typed term with the rule that its erasure is the scheme's:

- `divLit op c`: a division by a literal at which it cannot fail (§39, `divLitB`, `safeDivB`); at
  a conforming host the operation answers at every dividend (`divLit_some32`, `divLit_some64`,
  `divLit_some8`), so the scheme's error arm is never taken;
- `walk m`: a counted walk of a view (§16), the `count_fold` or `count_try` over its length
  (`walkB`); its step runs only below the bound (`walk_fold_index_lt`, `walk_index_lt`), and below a view's length its read answers a leaf
  (`walk_get_leaf`, `walk_split_first`), from §16's completeness lemmas;
- `selfCall j n`: a recursive group's self-reference read for member `j` of `n` (§20, `selfCallB`);
- `lendCell m`: the lend of a cell allocated for it, `withbor (alloc v) cb` (§35, `lendCellB`),
  the one scheme of the three emitters of a scoped cell (a value lent to a call, `modify` of a
  value, a handler's state given as a value).

What each of the last three leaves to the scheme is recorded in `Frontend/Check/TFacts.lean`. The
fixed points of folds, `unfold`, `count_fold`, `count_try` and `bounded_fix`, and `swap`, are rule
nodes already. A drop is the rule nodes `unitE` over `lolliE` of the variable and the destructor's
derived node (`dtor`), and a finaliser the `[then]` node's third child, built of drops.

**No node holds an untyped term.** A rule argument that is a term fixed by an equation on a
child's erasure (`effHandleT`'s clauses, `reify`'s residual, `[let-poly]`'s value and body) is not a
field: the erasure reads it off the child's (`Expr.pairL`, `Expr.toVal`, `Expr.letBody`). So
`[let-poly]`'s node holds its value's and its copy's typed terms only, and its erasure is the let
of the copy unfilled (`Expr.unfill`). `scripts/gen-pin.py --check`, a gate step, fails if a node
has a field of type `Expr`, `Val` or a surface term.

### A `def` at its uses

A `def` is checked once per key: the declaration, its type arguments, the lifetime context, and the
context of externs it is checked at (the persistent externs it may name, §11). Each use is a `use`
node over the key's checked body, placed at the use (`Frontend/Check/TShift.lean`): its variables
moved past the slots bound between the externs and the use (`TExpr.shift`), which the body does
not name. The body's derivation is one there (`TDerivesAt.weaken`, `TDerivesP.weaken`): a slot
the body does not use may be live at the use, and the body's derivation takes it where its rules
can, as a leaf drops a persistent slot and `⟨⟩` takes any. Which slots it can take is the body's
**absorption** (`TExpr.absF`), read off its rules' premises on the context's live slots and
recorded on the `use` node; the use is given those, as the premises that checking the body at
the use's own context decides give them. Every program of the corpus checks as it did when the
checker checked each use apart, with the same output. A `use` node erases to its body's erasure, the body's erasure with its variables moved past
the use's slots, and its derivation projects to one of that term at the use's context
(`TDerivesAt.use_projects`, `TDerivesP.use_projects`): the term and derivation checking the body at
the use gives. A body that holds a relaxed lend (§29), whose rules are at fixed contexts, is
checked at each use.

**A larger lifetime context.** A key's body is placed at a use whose lifetime context is larger than
the one it was checked at (a use under a lifetime binder, or inside a borrow) by
`TDerivesAt.weakenΔ`/`TDerivesP.weakenΔ` (`Frontend/Check/TLife.lean`), not checked again, when
the larger context has every binding of the smaller and its other bounds mention none of the
body's binders (`ExtΔ`), the body has no rule that reads `⊓Δ` or takes a fresh variable
(`TExpr.domFree`), its type elaborates the same at the use, and the slots it is placed under
mention none of its binders. Two kinds of body are still checked once per lifetime context:

- one with a borrow, whose type `∀'x ⊏ ⊓Δ. …` the context changes (the borrow rules' type reads
  `⊓Δ`, so no derivation at a smaller context is one at a larger);
- one whose type has a lifetime binder: the binder is numbered from the context (`Δ.freshVar`), so
  the type elaborated at the use is another `VTy` than the one checked, and the checker compares
  types as they are. A renaming of typed derivations' lifetime binders would place it.

In #509's reproduction (`print_f64` twice) that is 179 keys and 249 checks, of which 36 are bodies
with a borrow and 34 bodies whose type has a binder.

**The elaborator's keys.** A `use` node records the elaborator's key of the `def` (`TInfo.key`,
`Frontend.DefKey`), when the elaboration generated it: a template instance's template and type
arguments, or a copy's function and keys (the handlers and sites that serve its effects, its
blocks'). Copies whose keys differ only in their sites' names have one `body`.

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

### Cell classes

A cell's contents change type at `swap` (`Ref A ⊸ B ⊸ Ref B ⊗ A`), so a cell is as wide as the
widest contents it holds over its lifetime. The checker carries, for each type `main` allocates a
cell at (`alloc A`, a leaf of `allocS σ`), its **class**: that type and every type a chain of the
program's swaps reaches from it, lifetimes erased (`Checked.cells`, `Frontend/Check/Cells.lean`).
Only `swap` of an owned `Ref` changes a cell's type: `withswap`, the slice swap and
`array_replace` keep it, and an array's slots are never owned `Ref`s. The edges are the typed
term's `swap A B` nodes, whose types the derivation fixes, and `fold_reuse`'s emptying swap
(§6), which puts `1` into a cell holding the recursive type. The class is closed under them
(`Checked.cells_closed`), so it holds every type such a cell can be given by the program's
swaps; that a cell holds only its class's types at run time is not proved
(`Frontend/Check/TFacts.lean`). It is an upper bound: it joins the cells of one type.
`scripts/check-cells.sh` compares the classes with the cell widths of the closure IR's layout
types (`Backend/Clos/Types.lean`) on the corpus and pins the table in `corpus/cells.expected`:
they agree on every program but three, where a class is wider (an `i32` cell, three words where
the layout types give one, because a cell holding `1` is refilled with a list elsewhere).

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
the operation has no answer.

### Operations

The language's integer operations (`HostOp`, `Support/Syntax/Integers.lean`), at each width `w`.
They are defined here, on bit-vectors of `w` bits, as `wasmHost` computes them
(`Support/Dynamics/Host.lean`, `Prim.bin`, `Prim.div`, `Prim.un`, `Prim.rel` on `BitVec`). Each is
named as the Wasm instruction that computes it; Wasm and native code are two implementations of
this section, and neither is its reference.

| group | operations | type (at `I32`) |
|---|---|---|
| literals | `lit` | `I32` |
| binary | `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `shr_s`, `shr_u`, `rotl`, `rotr` | `I32 ⊗ I32 ⇒ I32` |
| partial | `div_s`, `div_u`, `rem_s`, `rem_u` | `I32 ⊗ I32 ⇒ I32 ⊕ 1` |
| unary | `clz`, `ctz`, `popcnt`, `extend8_s`, `extend16_s` | `I32 ⇒ I32` |
| tests | `eqz`; `eq`, `ne`, `lt_s`, `lt_u`, `le_s`, `le_u`, `gt_s`, `gt_u`, `ge_s`, `ge_u` | `I32 ⇒ 1 ⊕ 1`; `I32 ⊗ I32 ⇒ 1 ⊕ 1` |
| conversion | `wrap`, `extend_s`, `extend_u`, `extend32_s` | between widths |
| byte | `wrap8`, `extend8_u` | `I32 ⇒ U8` (the low 8 bits), `U8 ⇒ I32` |

What each computes, on `w`-bit vectors `a`, `b`:

- `add`, `sub`, `mul` wrap: the result mod `2^w`. `and`, `or`, `xor` are bitwise.
- `shl`, `shr_s` (arithmetic), `shr_u` (logical), `rotl`, `rotr` **mask the amount**: they shift
  or rotate by `b mod w`, the low 5 (6) bits of `b`, read unsigned. A shift is never undefined, and
  `<<` is total at every amount; this is also what x86 and ARM shift instructions do.
- `div_s`, `div_u` truncate toward zero and `rem_s`, `rem_u` take the sign of the dividend; each
  answers `inj₂ ()` at a zero divisor, and `div_s` also at `INT_MIN / -1` (`rem_s` answers `0`
  there). The surface raises where these answer `inj₂ ()` (§39).
- `clz`, `ctz` count leading and trailing zero bits, `w` at `0`; `popcnt` counts set bits;
  `extend8_s`, `extend16_s` sign-extend the low 8 (16) bits.
- the tests compare `a` and `b` as integers, read signed (`_s`) or unsigned (`_u`).
- `wrap` keeps the low 32 bits, `extend_s`/`extend_u` sign- or zero-extend 32 bits to 64,
  `extend32_s` sign-extends the low 32 bits of a 64-bit vector; `wrap8` keeps the low 8 bits, and
  `extend8_u` zero-extends a byte.

The grouped operations are at `w32` and `w64`. At `w8` they exist as names and take `0`
(`hostArg`), so none is applicable, and `Host.call` has no argument shape for them: arithmetic
on bytes is done at `I32`. The surface elaborates an operator at `u8` to the `i32`
operation on `extend8_u` of its operands, narrowing an arithmetic result by `wrap8`, and reads
the byte literal `b'c'` as `u8[n]` (`docs/decisions.md` 43).

`A ⇒ B` is the call-by-value function type `U(A ⊸ F B)`. Typing: `CDerives.lit` gives a literal
its width's type, and `CDerives.hostOp op` gives `host op` the type `!(hostArg op ⇒ hostRes op)`.
Partial operations return a sum where they have no answer (where Wasm traps), because a trap
would abandon linear resources.

### Semantics

The value relation at `int w` holds exactly at a literal of width `w` and the empty resource. Every
theorem holds for every host `ℍ`, so nothing about arithmetic is proved. The concrete host
`wasmHost` (on `BitVec`) is used only by the interpreter and by `decide`-checked evaluations.
`Host.Conforms ℍ` (`Support/Dynamics/Host.lean`) states what an implementation of the operations
is: `wasmHost` at every integer operation, and at every float operation up to §37's NaNs.
Compiler correctness will be stated with the target's own operations as the host. Agreement
between engines is tested on the corpus, not proved.

### Open

- Floats (`F32`, `F64`) are §36, by the same scheme.
- The surface's integer `/` and `%` take the partial operations' sum apart and raise
  `Fail[DivError]` where it has no answer (§39).
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
recursive data at an unwritten use is rejected at that use (`Frontend/Check/Copies.lean`,
decision 39). `clone(x)` elaborates to the core form `clone(x)`, which the checker checks as `x`;
its typed node records the written copy. A copy at a type that copies as words (`I32`, `1 + 1`,
their products) stays implicit. The check runs after the checker, on the typed terms it returns
(`main`'s, and each `def`'s without parameters, checked at its declaration), so it only rejects
more programs: `checkProgram_sound` and every theorem are unchanged. Which variables a split
copies is read off its node's masks (§3): the slots both parts use, which the derivation gives to
both.

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
is checked once per key and placed at each use (§3), where the extern is `main`'s slot, as for
any `def`.

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
every extern `main` reaches (§34) with its level and its implementation; an unproved boundary is
the program's trusted base.

| extern | model | host implementation |
|---|---|---|
| `stdin`, `stdout`, `stderr` | proved (7): cells with the model content | runtime cells holding the fd; assumed (1), checked against the model on the corpus |
| `read_byte`, `write_byte` | proved (7) | WASI `fd_read`/`fd_write`; interpreter-checked (2): the flat-IR interpreter runs the lowering against scripted streams |
| `write_all`, `read_into` | proved (7) | WASI `fd_write` of the view, again after a short write; `fd_read` into the view until it is full or the input ends; interpreter-checked (2) |
| `mk_input`, `mk_output`, `take_input`, `take_output` | proved (7) | none: the model's harness, not compiled |

An extern the compiler has no implementation for is reported as assumed and not compiled.

### Lowering

The runtime binds the three cells holding file descriptors 0, 1 and 2, each a word of the
program's data (§35), runs `main`, takes back the cells `main` returns and prints the result. `read_byte` is WASI `fd_read` of one byte from
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

`lib/io.bc` is ordinary library code, in scope in a program whose `main` uses the capabilities
ambiently (below), or that includes it. Its helpers over cells are written over the platform's
handlers (§34): `putb(o, b)` is `with wasi_stdout(&mut o) { print_byte(b) }`, the cell lent to
the clause, which calls the extern.

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
  mentions `stdin`, `stdout` or `stderr` gets the I/O library (included first, as `include io`,
  §34), the operations, and an `extern` for each capability it mentions (in the order `stdin`,
  `stdout`, `stderr`). `main : F A`
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
  taking a `Mut` borrow: `Env` (lookup by name into a borrowed array), `Fs` (open yields an
  `Input`/`Output`, close consumes it), `Net`, `Random`. `Clock` and `Args` are built, as
  effects (§34).
- **Exit.** The exit status is `main`'s result at `A = I32`; not yet passed to the host.
- **Handlers.** A capability's meaning is its model and its operations are externs, not rules,
  so a capability can be served by any value meeting the extern's type: the host, the model
  (`bcc interp`'s handler), or a user-defined handler, such as a mock input or a recording output:
  the streams are effects whose outermost handler is the platform (§34). Nothing in the typing
  depends on the host.

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
- `Env`, `Exit`, `Fs` and the rest are designed only; `Args` and `Clock` are §34's.
- `|>` pipelines (#59) are §33's.

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

The elaborated term, with drops inserted, is what the checker returns, as the erasure of its typed
term (§3), with its `CDerives` derivation (`checkProgram_sound`). The drop is `unitE` over `lolliE` of the variable and
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

### The loop node

The surface has one loop, `'ℓ: L { M }; N` (`Comp.loop`), whose source `L` is what the program
writes (`docs/loops.md` §2.1):

- `for x in V`: `V` is the source, and `x` its element. Which source it is, a count, data
  (§16), a call of a generator (§15) or a drain, is decided from `V` and its type;
- `while c`: the condition `c`, tested before each turn;
- `loop`: no source, so the loop ends only by an exit.

The label `'ℓ:` is optional, and its spelling provisional (`docs/loops.md` §2.8). It is parsed
and carried on the node; `break`, `break e` and `continue` leave or restart the innermost loop,
and no exit names a label yet. A message about a loop names the construct written: a `while` is
reported as a `while`, never as a `for`.

### Inference and markers

A function is div when its type says so (`A ⇒ U(Loop B R)`), or when its body **loops**: on its
spine (the tail positions of binds, `let`s, `case` arms and loops) it has a loop that is not a
counted loop (a `while`, a `loop`, or a `for` over a source that is not sized, §16), or it runs
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

**Moves.** The code of a point that a move calls is a `!` function of its state, defined before
the step; the code of any other point is its arm of the step. A move to a join calls its
function. At the empty row every move to a summand is a skip: each observation is one iteration,
or one observation of a callee, as with the delay bind, and `div_fuel` counts the same
observations; no move calls a summand, so each summand's code is its arm. The body runs its code
up to its first state when called, and a move there is the machine at that state (the `unfold`
of the step, from the state). At a row (a generator, §15) the observations perform the row's
operations; a move forward, from the step's own code or to a later point, is a call, and a move
back to a loop's head a skip, so each observation runs one turn of a loop; the body runs nothing
when called, its first state holding the parameter. A function calls only the functions of
points after it in the body, so none calls itself and every observation ends. A terminal that is
a value finishes with it (`inl V`).

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

The borrow is the block's parameter and every copy of it or of its parts on the block's spine
(`let b2 = b`, `let mut v = v`, the pattern's names; §41 *Binder identity*): each block of the
rewrite binds them again at its start. It applies when what the loop holds between steps outlives
`'x`. Otherwise it reports where it does not: an iterator that holds the borrow; a stretch before the loop that hands on something
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
holds it across its loop. `|>` is §33's.

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

### The effect `Div` in the kernel

Divergence is also an effect the kernel handles (decision 67; `docs/pipeline-architecture.md`
§3.2). The kernel has it; the frontend keeps the elaboration above, with no `Div` in any row it
writes, until B2 (#563's successor) elaborates loops to it.

**The effect.** `Div` is the reserved name `divEff = 2³² − 1` with one linear operation

    tick : 1 ↠^lin Next        Next = 1 ⊕ 1        next = inl (),  close = inr ()

(`Core/DivDefs.lean`, `tickSig`). A row **holds `Div`** when the operation it finds at
`(divEff, 0)` has `tick`'s signature (`CTy.divAt`, `Row.divB`). `tick`'s continuation is linear:
it has no cancel, so closing a loop is a resume with *close*. `tick` is not abortive, so it is in
no unwind-only row, and no borrow callback's row holds it (`Row.Unwind.divB`).

**The constants** (`Core/Fundamental.lean`, each a rule of `CDerives`):

    iterate   : !U(!U(S ⊸ F_Σ(B ⊕ S) & F_Σ R) ⊗ S ⊸ F_Σ(B ⊕ R))        Σ holds Div
    div_fuel  : !U(U(1 ⊸ F_{tick, Σ} A) ⊗ I32 ⊸ F_Σ A)                  Div ∉ Σ
    reify_res : !U(U(1 ⊸ F_{tick, Σ}(B ⊕ R)) ⊸ F_Σ U(Loop_Σ B R))      Div ∉ Σ,  res : !U(B ⊸ F_Σ R)

- **`iterate`** is a primitive with one machine step, `iterate (f, s) ↦ iterNext f s`
  (`Support/Dynamics/Iterate.lean`):

      (f s).1 to r. case r { inl b → inl b
                           | inr s′ → tick () to n. case n { inl _ → iterate (f, s′)
                                                           | inr _ → (λq. inr q) ((f s′).2) } }

  The step is `unfold`'s: one turn, or the close handing back the residual `R` (*The residual*).
  The primitive ticks at each back edge, so every turn after the first is guarded whoever wrote
  the step. The backend replaces it by its fixed point before conversion (`expandIter`).
- **`div_fuel (t, k)`** is a term (`divFuelV`): a deep handler of `Div` around `t ()` answering
  *next* to the first `k` ticks, the budget read unsigned, and *close* to every tick after. Its
  counter is `bounded_fix`'s (§20), counted by the machine.
- **`reify_res t`** (`reifyV res`) makes a loop value of `t ()`: a deep handler of `Div` whose
  clause answers the loop at the tick, its *next* resuming `κ` with *next* and its *close*
  resuming it with *close* and then closing what follows. `res` hands back the residual of a
  finished result; it is a closed term of the constant, typed by a premise at the empty context.
- The callbacks are `U(1 ⊸ F_{tick, Σ} A)`, the kernel's form of a thunk of a computation at a row
  (§26).

**The relation.** `ewpTS` is a least fixed point, so a computation that ticks forever is not in
it. At a row that holds `Div` the relation is a greatest fixed point over **segments**
(`Core/DivDefs.lean`):

    cwp T Q   ≜  gfp W. ewpTS · (opTable T∖tick ∨ Π_W) Q
    Π_W(tick)  =  λ_. λκ. ∀ n : Next. W (κ n) ∧ Closing (κ n)
    Closing   ≜  ewpTS · (opTable T, tick answered close only) Q

A segment, up to the next tick, is an `ewpTS` run; a tick stops it and owes its continuation, at
each answer, to the candidate and to `Closing`. `Closing` says that after a close the computation
reaches its end through finitely many ticks, each answered *close*: it is what `div_fuel`'s
totality and `reify`'s close read. Without it the candidate admits `Ω = fix self. tick (); self ()`,
which ignores every answer (S0's `omega_cwp0`), and `div_fuel` would not be total. No step index is used. The relation at an
effectful type is `effWp` (`Core/Relation.lean`): `cwp` at a row that holds `Div`, `ewpTS`
elsewhere, so every clause at a row without `Div` is §19's unchanged.

**The rules at a row that holds `Div`.** `[sub]`, `[perform]` (of `tick` and of other names),
`[raise]`, `[let]` and bind are proved at `cwp` (`Core/DivRules.lean`, `Core/EffFin.lean`). Core's
frame lemmas are stated once at a table `opTable T ∨ Π`: `ewp_frame_plain_or`, `ewp_frame_then_or`
and `ewp_handle_or` (`Core/EffRules.lean`, `Core/EffFin.lean`), with `ewp_frame_plain`,
`ewp_frame_then` and `ewp_handle` their instances at `Π = ⊥`.

- **`[then]`** at a row holding `Div` (`cwp_then`): finalisers are total (decision 69). The typing
  rule that ensures it is that the finaliser's row `Σ_D` does not hold `Div` (`effThen`'s `hSD`).
  A finaliser may still perform operations and raise.
- **`[handle]` of another name around a computation that ticks** is typed only when its clauses
  resume `κ` in tail position (decision 68, a temporary restriction #564 lifts): `effHandleT`
  (`Core/DivHandle.lean`) writes the clauses out from a tuple `gs` of answering functions
  `g : !U(A ⊸ F_{Σ_N} B)`, `Σ_N ≤ Σ` a row of linear operations, as `λ(x, κ). (λw. κ.1 w) (g x)`,
  and an abortive operation's clause as `g : !U(A ⊸ F_Σ R)`. `effHandleV` and `effHandleVB` ask
  the handled row not to hold `Div`. A handler whose clauses are all abortive is `effHandleT` at
  an η-expanded clause tuple.

**What is proved.**

- `fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD` and `total_every_run` keep their
  statements, and cover the new rules.
- `divFuel_every_run` (`Core/DivPrograms.lean`): for a closed callback `t` at the row of `Div`
  alone and every budget, every run of `div_fuel (t, k)` continues to a value.
- `runtime_every_run` (`Core/DivRuntime.lean`): a closed `M` typed at `F_{Div} A`, under the
  runtime's clause `λ((), κ). κ next`, from the empty memory: every configuration a run reaches is
  an answer or takes a step. The run is infinite in general; the proof is an invariant of
  configurations.
- `divResidual` (`Core/DivPrograms.lean`, kernel program `div-residual`): a loop whose state is a
  cell, closed by `div_fuel 3`, which hands the cell back. Its derivation is tied
  (`dAt_divResidual`), every run continues to a value (`divResidual_runs`), and each stage prints
  `3` and `live 0`.

### Baseline

The constants of *The effect `Div` in the kernel* are the rules and the relation clause added;
the rest of this entry adds none. `fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD` and
`total_every_run` keep their statements, and every theorem of §§1–13 is preserved. The runtime's
obligation for a looping `main` is §11's.

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
- **`[handle]` of another name at a clause given `κ`** around a computation that ticks
  (`handle_general`, #564).
- **Finalisers are total, as a theorem** (decision 69): every run of a finaliser terminates, the
  handler clauses its operations reach included. `[then]`'s premise keeps the finaliser's own row
  free of `Div`, so its own run is a least fixed point (`ewpTS`): it performs finitely many
  operations, each segment finite. A clause it reaches runs at the handler's outer row: at
  `effHandleV` and `effHandleVB` that row is free of `Div` and the clause's run is a least fixed
  point too, but an `effHandleT` clause's answering function is at a row `Σ_N` that may hold
  `Div`, and may tick without end. Not proved.
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
  (`io_hwf`): its observation is `handle_with[n](V_r, V_c) ((nu_out l).1)`, and its close closes
  `g`'s loop under a handler of its own.
- **A body that performs a control operation, or may loop** (a `while`, a `loop`, or a `for`
  over anything but a count), is not a clause: the clause would hold the continuation across the
  operation, and an affine continuation has no destructor (its cancel performs at the site's
  row, so it cannot be drop glue), and a clause is total. The `for` then observes `g`'s stored
  generator instead (below), a loop of the enclosing body.

When the body performs nothing else, the clause resumes in tail position, and the operation is a
direct call of the clause (§19, *Lowering*): `corpus/gen-produce.bc`, `gen-fib.bc` and
`gen-pipeline.bc` allocate nothing and dispatch no call. A body that branches resumes at the end
of each arm, and is a direct call too; a body with `break` or `return` in an arm cancels there,
and is a suspension (`corpus/for-yield-branch.bc`).

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
the first whose parameters the arguments match. A `poly` family (§36) is chosen otherwise: one case
per type, the most specific, and a second case at a type is an error.

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
- **Callbacks that yield** to a `for`'s site: a block takes the loop's threaded variables and
  hands them back at each call (§32, `corpus/yield-callback.bc`). `|>` chains the adapters as
  functions over stored generators (§33). Adapters written as handlers over a computation would
  hold the continuation across their own `yield` (*A body that performs a control operation*,
  above), and are not provided.
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
step, and it is total (`forData`, `Frontend/Sugar.lean`; all of it elaboration into core). With
no exit it is `count_fold` (*The step and its exits*, below):

| source, by type | the bound | the element at step `i` |
|---|---|---|
| a count `a..b` (syntax; `i32`s) | `b − a`, from index `0` | `a + i` |
| a count `k..b`, `k` a literal in `[0, 2³¹)` | `b`, from index `k` | `i` |
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

A count counted from a literal start is counted by the machine's counter itself: the counter is
the element, and the count's start is not in the loop's state. Any other start is counted from
`0` over the count's length, as the machine's counter is unsigned (`len`, above) and a negative
start would be past every bound. At every count `k..b` whose length `b − k` does not overflow
the two agree, and where it overflows (`1..-2147483648`) the count from `k` is the empty loop,
as the count is.

**The step and its exits.** The loop's state is the source's cursor and the variables the body
reads or assigns (a capability the body uses included: an effect of the body is the function's,
and the loop hands the capability back). The step binds the counter and the state's variables
from its argument. A step with no exit (no `break` or `return e` in the body, no abortive
operation, and a source that does not end before its bound: every source but a sized iterator)
is `count_fold`'s: it answers the next state at the end of the body and at `continue`, and after
the loop the threaded variables are bound from its last state (one variable directly, as
`x <- loop`). Any exit makes the loop `count_try`: the step answers `inl` of the next state at
the end of the body and at `continue`; `break e` and `return e` answer `inr` of the threaded
variables and the way out. After the loop the threaded variables are rebound and the loop's value
is `e`, or the `else` value when the source ended. `return e` in the body of a loop of a surface `fn` (or
`main ->`) returns from the function from any depth of its loops: each counted loop leaves by its
exit, and the loop around it by its own (`DivSt.exits`); the loop is first moved onto the
function's spine (`normExits`). A core `def`'s `return V` is the core's. `break` and `continue`
are the innermost loop's, labelled or not (§14, *The loop node*).

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
`buf_of_array`, `array_tab`, and `array_set` (an owned array's slot written, the old element
dropped). `push` on a full buffer grows it to twice its capacity (at least
8): a new array of fillers (`tab`), each element moved by `array_replace`, and the old array
dropped with the fillers left in it. Every operation is `tab`, `array_replace`, `array_size`,
`count` and `drop`, so buffers are sound under every allocator by §9 and §13 with nothing new.
A **priority queue** is a buffer too (#490): `heap_push(h, k, x)`, `heap_pop(h)` and
`heap_peek(h)` (#198: a copy of the least element, the heap unchanged) keep `buf (i32 * A)` a
binary min-heap by the `i32` priority, each sift a counted loop of 32 steps, and read an element
by taking it out and putting it back, so `A` is persistent.

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
§18), the integers written in a view folded into a state (`fold_i32s`, `fold_i64s`: each run of
digits, negative after a `-`, every other byte a separator; #490), and buffers of views
(`view_at`, `sort_views`). Every loop is a
`count_fold` bounded by a length, so the library is total. `lib/textio.bc` (`include textio`)
writes and reads text over the standard streams: `write_str`, `write_string` and `write_lit` in
one `write_all`, and `read_all`, which reads the input in chunks into the string's spare
capacity (`read_into`) and runs until the input ends (a div function, §14).

### Literals

A string literal `"…"` is the persistent value `(n, t)` of `lit`: `n` its length in bytes and `t`
a `!` function with no captures from an index to its byte (`0` past the end). The elaborator
writes `t` as a compare of the index with the length, then a search on the index down to one
byte (`Frontend.Sugar.litValue`): an ordinary core term, typed by the checker, and marked as the
literal's table, so that its typed node is the derived node of the bytes (§3, `litFn`). A literal holds no
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
  `litTable?`, `litClosure`), whose body is a load (`litByte`). The bytes are emitted once, in the
  program's data before the heap, at an address the target chooses (`Backend/Flat/Syntax.lean`,
  `dataBase`; the Wasm target's data segment is from `16384`). Every literal is one code, so a call of one is
  direct.
- **Literal views point into the data.** The erased shape of a literal view — the array lent by
  `withbor`'s term to a callback that first copies the family, then dropped — is recognised
  (`litView?`), and its `tab` is `litTab`: when the tabulator is the literal code's closure and
  the length at most the literal's, the array is `(address, n)` in the data and nothing is
  allocated; otherwise it is `tab`. Copying the family is typable only at an `imm` family, so no
  write reaches the array; `$free` skips addresses below the heap.
- **Buffers** are `(ptr, cap, len)`: an array's two words and the length. Growth allocates the
  new block, moves the elements one by one and frees the old block; each function that may grow
  says so (§35).

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
within it, checked, and gives the type arguments of an effect the function performs directly. A
row may hold several instances of one effect, and handlers and a row's entries may be named,
`with n = h(…) { M }`, `n.op(v)`, `with src: E` (§38). All spellings are provisional
(decisions 51, 55).

**Errors** are the library effect `Fail[E]` (`lib/fail.bc`), `ctl raise(e: E) -> never`, handled
by ordinary handlers: `to_result` (`inl` the value or `inr` the error), `default(d)` (the value,
or `d`, an owned value) and `map_err(f)` (the error `f(e)` raised to the handler around the
`with`). Nothing in the elaborator knows them.

**Iteration** is the library effect `Yield[T]` (`lib/yield.bc`), `ctl yield(x: T)`: a function that
performs it is a generator, a `for` over a call of one handles it, and a call where a stored
generator is expected stores it (§15). The elaborator knows it only as an iteration effect, by its
structure: one control operation that resumes and answers `()`.

### Elaboration

All of it is in `Frontend/Elab/Effects.lean` (resolution, before the rest of the sugar, with the
types of operations' arguments read first, §38) and `Frontend/Sugar.lean` (assembly, where types
are known); the checker sees only core.

**Answering effects** are capabilities. With the capability `c : Mut 'l S`:

| form | elaborates to |
|---|---|
| a clause `op(x) = M` of `h` | `fn h__op<'l>(c: mut 'l S, x: A) -> mut 'l S * B = let r = modify c { s -> M; (s, r) }; (c, r)`: `!` code run on the lent state by `withswap`, the `FnMut` row of §2 |
| `with h(e) { M }` | `borrow mut (alloc(e)) { 'l, c -> M' }`: a `withbor` of the state's cell whose callback's parameter is the capability; the cell is dropped after |
| `with h(&mut c₀) { M }` | `borrow mut c₀ { 'l, c -> M' }`, and `c₀` is rebound |
| `op(v)` in `M` | `let (c, r) = h__op(c, v)`, `h` the innermost handler of `E` (or the one named, §38) |

The capability is threaded as a `let mut` variable is: bound again after each call, handed out of
each arm of a `match` or `if` that uses it, out of a borrow block, and through a `for`'s body.

**Control effects** are §19's. Each `with` of a control handler is a **handler site** with a
static name `n` of its own, and an operation is resolved lexically to the innermost site of its
instance (§38): `perform[n.i](v)`, or `abort[n.i](v)` for an abortive operation. The site is
`handle_with[n]((V_r : T_r), (V_c : T_c)) M`: the return clause `V_r` and the tuple `V_c` of the
operation clauses, `!` closures at the types `[handle]` gives them (`T_r`, `T_c`), the handler's type
parameters matched against the body's type and its arguments' types. The node holds its clauses:
its erasure is `hnd (n, (qs, (V_r, V_c))) e`, and the clauses are the `handle` node's own
(§19 *Clause kinds*). The clauses run outside the site: their operations go to the sites around the
`with`.

**Rows.** A function's **row** is the set of effect instances it performs: those of the operations
it calls and of the functions it calls, less those a `with` inside it handles. It is inferred in
declaration order, an operation's instance read off its argument's type (§38). A function with a row is elaborated once per assignment of its effects to what
serves them in scope (the handlers of its answering effects, the sites of its control effects), as
a generic function is once per instance (decision 45): the copy `f__…` takes the capabilities
first and hands them back first, and its type has the sites' operations as its row,
`A ⇒ F[n.i …] B`. A call of `f` is a call of that copy, a computation of its own:
`g <- return f; a <- return v; (force g) a`. A function with a row that is never called is not
elaborated. Resolution is lexical: an operation goes to the innermost handler of its instance around
it, or to what the enclosing function's copy was given (§38).

**A call's binding.** A call lifted out of the value it is in is bound before it: `r <- C`, or,
when it hands back capabilities, `t <- C; let (c₁, (…, r)) = t`, and the value refers to `r`.
When the value is the call's answer alone, the call takes its place: `x <- return V` binds `x`
as the call's binding binds `r`, and a terminal `return V` in tail position is the call itself,
when the call hands back the capabilities the computation hands back (in order) or the
computation hands back none. This holds at every call that is bound so: a function's copy, a
block parameter (§32), an answering operation, a resume (§19), a handler site, a stored
generator's site. A parameter that is the function's only one is its lambda's binder, not bound
again from a tuple (`Parser.paramVar`), as is an answering clause's only parameter; a clause's
value terminal is handed on as itself, `(s, (V : B))`.

The checker checks a copy, as any `def`, at each of its uses, so a program holding a closed
function at its uses is §24's `[let-poly]` read by substitution: the program's derivation gives the
rule's derivation of the let that binds the function once (`checkProgram_letPoly`, §24
*Theorems*). The copies for two assignments of names are two functions, each performing at its own
names.

**Where an abortive operation may stand.**
- *In a counted loop's body* (`for` over data, §16): `count_try`'s step is pure, so the step
  handles the operations of the names its body performs itself, each leaving the loop by its exit,
  and after the loop the operation is performed again at the same name; of several sites, each
  (§38). A body with a control
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
and a function with a row passed as a value other than at a parameter of function type, where
it is the block that calls it (§33; stored callbacks, #161 part B; for a fold's algebra that
raises, K4 below); a lend `&mut x` in the arguments of a call that
threads a capability; an operation of an answering effect inside a clause of an answering handler;
a function with a row whose written result is a computation (a loop); type parameters on an
answering effect; an effect with both kinds of operation; an unrestricted operation that answers
`never` (`multi ctl`, above); a `let mut` declared outside a control `with` and assigned in it, or
a place lent in it; a borrow of a buffer or a literal crossed by an abort. Several instances of one
effect are §38's, with what it does not provide.

### Reports

`bcc check` prints, after the declarations' types, what the elaboration did (#126), in four kinds,
each in source order; the library's own are not printed:

| line | says |
|---|---|
| `effect L:C: E: op, …` | an effect and its operations, with their kind and qualifier |
| `row L:C: f: E, Fail[X]` | a function's inferred row, with the instances' type arguments |
| `lowering L:C: …` | each handler: an answering handler is a **call** (`fun`); a control `with` (and a `for`'s or a stored generator's site) is a handler site with its static name, each operation abortive (a branch per call, `final ctl`) or with its qualifier and its clause's kind, read from the checked `handle` nodes of its name (§19 *Clause kinds*); each copy made for a handler or site |
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
- **A resume in every arm** (`tail_resumes`, `TailResumes.step`). A control clause whose every
  path ends in one resume `R N` in tail position, through `case` arms, `let (x, y)` bodies,
  sequences, `let x = e` bodies, the right unit `let x = R N in return x` and a `let` of a closed
  value (its `β`-step), runs as the clause with its resumes removed, then one resume: each step of
  the one is matched by steps of the other at the same memory, and when that answers `r`, the
  clause reaches `R r` under right-unit frames (`RetFrames`), which hand on `R r`'s answer
  unchanged (`RetFrames.answer`, `tail_resumes_answer`). It is the clause whose resume is its last
  call, which §19 lowers as a direct call.

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

- Bundles (#156): no program needs one, since a function is given its effects by its row (§34).
  Named instances and resolution by instance are §38.
- Effectful callbacks stored (#161 part B, §33 *Open*). Functions over computations (`retry`, a
  consumer of generators, `|>` at a computation parameter) are §33. Blocks passed and called
  are §30: E1 (a higher-order function under two handlers) and E6 (a wrapper whose handler the
  callback's raise passes) run from source (`corpus/effects-hof-two-rows.bc`,
  `corpus/effects-tunnel.bc`), and E2d (a consumer of generators at two rows) does too, its
  generator a computation parameter (`corpus/effects-sum-gen.bc`, §33).
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
  **Named instances fall out**: the surface's are §38.
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
  - at a handled row that holds `Div` (§14), `[handle]` is `effHandleT`, whose clauses resume `κ`
    in tail position; `effHandleV` and `effHandleVB` ask the handled row not to hold `Div`, and
    `[then]` asks it of the finaliser's row (decisions 68 and 69).
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
- **The relation.** `cC (F_Σ A) ls δ e ≜ ewpTS ls e Π_Σ (λ ls″. 𝒱⟦A⟧(ls″)δ)` at a row `Σ` that
  does not hold `Div`, and `cwp` at `Σ`'s table at one that does (`effWp`, §14); `cC (F A) = wpTS`
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

  At a row without `Div` this is the whole story. At a row that holds `Div` (§14, *The effect
  `Div` in the kernel*) the relation is the greatest fixed point over segments, `cwp`, with
  `Closing`: a computation that ticks forever is in it, each segment between two ticks a finite
  `ewpTS` run. `ν` stays the relation of loop *values* (`Loop_Σ`, `reify`'s answer); `cwp` is the
  relation of a computation that loops, at the type `F_Σ A`.
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
   - At a row that holds `Div`, the same cases at `cwp`'s segments (`ewp_handle_or`): a forwarded
     tick is the coinductive case, its continuation the candidate's (`cwp_handle_tail`, §14).
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
resumes `κ` once on every path, in tail position, with an answer computed without `κ`, and it
neither suspends nor raises, a `perform` of the operation calls the clause's code with its resumes
removed. A path runs through the arms of a `case` and the bodies of `let`s; each must end in
`k.resume y` and use `κ` nowhere else. A clause with an arm that raises out of it, cancels or drops
`κ`, stores `κ`, resumes it twice, or resumes it under a `catch` or finaliser frame is not
tail-resumptive: it is a state machine. An error raised and caught inside the clause is a branch
inside it and does not end a path. The resume commutes out of the arms (§18 *Laws*,
`tail_resumes`), so such a clause is one whose resume is its last call. Nothing
suspends or resumes, and no continuation is materialised. A clause that captures values, or
whose handlers differ, is a state machine like any other: resumed in tail position, it still
runs in constant stack.

**Clause kinds.** At `[handle]` the checker classifies each operation's clause and records the
kind, with the operation's qualifier, on the `handle` node (`ks`; `Frontend/Check/Kinds.lean`).
The clauses are the components of the node's own handler pair `(h_ret, hs)`, which the elaboration
writes inline (§18), so the classification reads the derivation of the node's own premise; a
clause a program names by a `def` is read through its `use` node, the `def`'s body at the use. A
clause the node does not hold, a variable that a program writing core binds to it, is `stored`.
`handle_with[n](hr, hc) M` takes values: the elaboration writes the clauses, a program in core may
write variables. An abortive operation is one whose
signature gives its clause no `κ` (`clauseTy_abortive`). A control clause is
`!thunkv λp. let (x, κ) = p; M`, and its kind is how `M` uses `κ` on its paths, through `[⊕E]`,
`[⊗E]`, `[1E]` and `[let]`, to `[app]` of `[&E₁]` of `[force]` at `κ`'s slot (the resume), that
resume under the right unit (`x <- κ.1 v; return x`, which is how a named handler's `k(v)` in
tail elaborates), or `[&E₂]` of it (the cancel). A `[let]` of `return κ` (`kk <- return (unbox k)`,
a BOXED-κ clause's) is an alias: `κ` moves to the new binder, and the body must not use the old
slot (`OnPaths.rebind`, `TailResumesAt.rebind`). A handler with a state (§21) answers `λs. S`, and
`S` resumes, then applies the function it answers to the new state. The first kind that holds,
from the most particular:

| kind | the paths of `M` | premise (`Core/ClauseKinds.lean`) | law |
|---|---|---|---|
| `abortive` | — (no `κ`) | `isAbortive o` | `catch_abort`, `abort_absorbs`, `unwind_prefix` |
| `tail` | each ends in one resume in tail position, or under the right unit; `κ` used nowhere else | `TailResumesAt 0 M M'`, which with `κ` closed is `TailResumes` (`TailResumesAt.subst_kappa`); `M'` does not use `κ` (`kappa_free`) | `tail_resumes`, `op_tail` |
| `tail+state` | each answers `λs. S`, and each path of `S` resumes, then applies the answer to the new state in tail position | `OnPaths (StateFn StateLeaf) 0 M` | `handle_fold`'s equation for the hnd encoding, stated in its unit |
| `resume-or-cancel` (± state) | each resumes in tail position, or cancels `κ` and goes on without it | `OnPaths (TailLeaf ∨ CancelLeaf)` | `kappa_cancel_steps`, `cancel_prefix` |
| `once` (± state) | each resumes or cancels `κ` once, in evaluation position, never under a `λ` | `OnPaths Once` | its own law and unit |
| `stored` | anything else: `κ` may be kept | — | the state machines |

`classify_sound` (`Frontend/Check/KindsSound.lean`): the kind recorded gives its premise at the
clause's erasure. `classifyHandler_sound`: at a `handle` node, the kind of the operation `j` gives
its premise at the `j`-th clause of the erasure of the node's pair, the clause the handler runs for
it. There is one definition of tail-resumptive: `effHandleT`'s clauses (§14,
`tailClause`, `λ(x, κ). (λw. κ.1 w) (g x)`) meet the `tail` kind's premise, and an abortive one the
`abortive` kind's (`tailClause_premise`), so an `effHandleT` node's kinds are read off its rule
(`tailKind`), not classified. `classifyHandler_quals`: the qualifiers recorded are the signature's. The
derivation does not constrain the kinds (`TDerivesAt.kinds_free`): the rule's premises type the
pair and carry no kinds. `bcc kinds <file>` prints every `handle` node with its kinds;
`bcc check`'s report of each handler site is rendered from them (§18 *Reports*). `tick` (§14) is
not a kind yet; the inductive `ClauseKind` and its premises are where it goes.

The backend does not read the kinds yet: it still recognises tail-resumptive clauses itself
(`tailClause?`) and builds a cancel arm for every `κ`. The gate compares the two for every
operation of every corpus program (`scripts/check-kinds.sh`, pinned in `corpus/kinds.expected`):
`abortive` against a branch per call, `tail` at every handler of the name against a direct call,
any other kind against a machine. The disagreements are the backend's stricter conditions: a
clause that captures values is a machine (*Open*), and so is an operation whose name has two
handlers with different clause codes, or whose clause resumes under the right unit. The backend
never makes a direct call of a clause whose kind is not `tail`.

**The clause's names in the continuation** (`Core/ClauseNames.lean`, `Core/ClauseOwn.lean`). A
tail-resumptive clause run as a direct call at the `perform` runs its work inside the continuation
`K` between the `perform` and its handler. That is H-op only when no frame of `K` catches a name
the work performs or raises. Condition 2 is stated over those names, the names the clause's own
code performs or raises, not over its row `Σ`:

- **The clause's names** (`Expr.own`, `handlerNames`): the names of `perform` and `raise` at
  literal names in the clause's body, through every `λ` it holds, the primitives that run no code
  they are given (memory, integers and the host, an array's index and split, `primOwn`), and the
  arguments of a call of `κ`, of an alias of it or of its resume's answer, whose code is the
  continuation's. Where the clause may run code it does not hold (an application of another
  variable or of a computed function, a primitive that runs a function it is given, an operation
  at a name that is not a literal) it has no names of its own, and condition 2 is over its row.
  They are read off the clause the node's erasure holds, the one `[op]` runs (`clauseExpr`,
  `BoLo.clauseAt`).
- **What they bound** (`tail_work_names`, `tail_clause_names`): `Fo N e`, *first-order at `N`*,
  says that `e` applies only code it holds (a `λ` in place, those primitives, the curried
  `store`) and performs and raises only literal names of `N`; a value is first-order whatever
  code it holds in a data position, which the term never applies. `Fo` is closed under the
  substitution of any value and under every step of the machine, from any memory (`Fo.subst`,
  `Fo.steps`), and a first-order configuration performs and raises only names of `N`
  (`Fo.perform_mem`, `Fo.raise_mem`). At a `handle` node whose kind for an operation is `tail`
  and whose names for it are `ns`, the clause's work `M'`, its body without its resumes
  (`TailResumesAt 0 M M'`), is first-order at `ns` (`fo_of_tail`): every run of the work, at any
  values of its variables (the operation's argument and the handler's captures), from any
  memory, performs and raises only names of `ns`. That is the code the direct call runs inside
  `K`.
- **The condition** (`UnhandledNames ns K`): no frame of `K` catches a name of `ns`. At no names
  it holds in every `K` (`unhandledNames_nil`); otherwise the program's record decides it
  (`steps_unhandledNames`, `Checked.unhandledNames`). Over a row's names it is `UnhandledIn Σ K`
  (`unhandledIn_iff_names`, over `Kont.Catches`, which holds at every handler frame of the name).
- **The rows do not decide it** when `Σ` is not empty (`unhandled_not_decided`): one `[handle]`
  node, the same tail-resumptive clause, the same rows and types, over two typed handled
  computations whose `K` holds no handler of a name of `Σ` in one and a handler of one in the
  other. Where a clause has names, what decides it is the frames `K` may hold
  (`Core/HandledNames.lean`, `Frontend/Check/Handled.lean`):

- **A set of frames** (`HIn`) is the names of handler frames, whether a finaliser (`ubind`,
  `cfin`, which catch every raise) and whether a handler whose name is not a literal; `ccatch`
  holds the name `0`. `Expr.hin e` is every frame `e` holds.
- **The record at `[handle]`**: the node's `inside`, its handled computation's erasure's frames,
  through the bodies of `use` nodes and a recursive group's generator. The typed rule pins it
  (`TDerivesAt.inside_eq`, `TDerivesP.inside_eq`).
- **The record at the program**: `Checked.flows`, what may flow in a run of `main`
  (`ClauseKinds.flows`): the frames of every `λ` that is not applied in place (a `def`'s body, a
  recursive group's generator, a clause, a closure), of every handled computation (a continuation
  captures them), the name of every handler a continuation may capture (a name the program
  performs, and `Div`'s), and `0`. A `λ` applied in place, `(λx. N) M`, runs where it stands.
  Code that flows into a handled computation from outside it (a closure bound before it, a
  continuation captured at another handler, a recursive call, a value read from memory) holds
  only frames of this record, so the record covers the call graph and recursion without unique
  names: a second handler of a name that a recursive call puts into `K` is one of its frames.
- **The run invariant** (`steps_frame_of_node`, `Checked.frame_of_node`): in a run of `main` from
  the empty memory, every handler frame of every configuration has the name of a handle node of
  `main`'s erasure, or `0`, or `main` holds a handler whose name is not a literal. Its proof is
  that no step leaves the frames of `main` and `0` (`steps_hin`): a step's head reduction builds
  frames only from its redex and the values it reads, and a continuation only from the frames it
  captures.
- **The theorem** (`steps_unhandledIn`, `Checked.unhandledIn`): in such a run, at every
  configuration that holds `hnd H K[p]` (at an operation it catches, where its clause runs), a
  row `Σ` none of whose names `Checked.flows` may catch (`cond2B`) is unhandled in `K`. Its proof
  is the flow invariant (`steps_flowInv`): what flows from a configuration and its memory stay
  within `flows`, and the names it performs within those `main` performs and `Div`'s.

What the record does not decide: it is not per node. A bound per node is stated, not proved
(`Checked.FramesPerNode`, `Frontend/Check/TFacts.lean`): the frames under a handler frame of a name
within its nodes' `inside`, `0` and, where code flows in, the record of what may flow when only a
clause that may keep `κ` lets its handled computation's frames flow (`Checked.flowsKept`). It needs
that a clause that keeps no `κ` never lets `κ` leave it, and a typing invariant of the run (a
value of a type with no `U` holds no code), which Core does not have. No direct call depends on it.
`bcc handled <file>` prints `main`'s flow record and each `handle` node's `inside`, outer row,
the names of each clause (`names n.i […]`, or `row`) and whether condition 2 holds over them;
`scripts/check-handled.sh` pins them for the corpus, with each operation the backend lowers, in
`corpus/handled.expected`: condition 2 holds at every direct call of a clause the backend makes,
each of whose clauses performs and raises nothing. It fails at eight nodes, every one a clause
that cancels `κ` and then raises (`deadline`, `scaled`), none a direct call.

**Handler sites.** The elaboration of effects records each handler site it makes
(`Frontend.SiteRec`): the effect it serves and its type arguments, the handler (a control
handler's name, or the function a `for` or a stored generator runs), the name the `with` gives it
(§38), the kind of site (a control handler's `with`, a `for`'s site, a stored generator's), its
operations, and the handler's state, the parameters its clauses are passed as a state (§19
*Handler state*). The record travels with the site's sugar (`HInfo.site`, `ItInfo.site`), so an
instance of a template carries it at the instance's types, to the `handle` node the typed
elaboration assembles, which carries it (`Comp.handle`'s `site`) with its types in the frame of
the node's code: a control handler's at the handler's lifetimes and type arguments there, and a
`for`'s or a stored generator's, written over its callee's type parameters, at the type
arguments of the callee's instance at the call (`siteAtCall`). A `handle_with` the program writes
in core has none, and neither has a handler a counted loop makes of the abortive operations of a
site around it. The checker elaborates the record at the node to core types and puts it on the
node (`site`, `HSite`), and checks it against the node: it names the node, and its operations are
the node's `E` (a `for`'s site's with the threaded variables beside each argument and as each
answer, `recOps`; `siteOf_ops`). A `for`'s site is checked against the kinds at the nodes of its
name, none `stored` (the loop's body is the clause, resumed or cancelled in place), and a stored
generator's site against them, one `stored` (`siteKindMismatch`). A mismatch is an internal
error. The derivation does not constrain the record (`TDerivesAt.site_free`), and the checker has no
effect declarations, so that the operations are `eff`'s at `args` is the elaboration's
(`Frontend/Check/TFacts.lean`). `bcc sites <file>` prints every `handle` node's site with its
kinds.

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

A group may be generic in types and lifetimes (§31): its members take the same type and lifetime
parameters, and its generator, layers and copies are generic in them.

**Not provided**, each rejected with a message: a member whose body has a `while` or a `loop`
(§21 *Open*); and a call of itself inside a handler of an effect
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
- A recursion under `deep` that performs an effect; recursion through a site (#173). A recursion
  whose body loops: §21 *Open*. Generic recursion: §31.
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
- Effects under `deep` (§20 *Open*; separate, per the spike). Generic recursion is §31.
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
  `sum-gen` and `tunnel` are the three as Core terms; at the surface they are
  `corpus/effects-hof-two-rows.bc` and `effects-tunnel.bc` (§30), and `corpus/effects-sum-gen.bc`
  (§33).
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

`handle_with[n](V_r, V_c) M` (§19) reads the clauses' type as BOXED-κ's when it can
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
  `top` (§30); `lib/async.bc`'s `spawn` is its first library user. A handler with a lifetime
  parameter boxes it at the meet of the lifetimes in scope at the `with` (§32, `spawn_in`).

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

**Not provided**, each rejected with a message saying so: a block given to a member of a recursive
group of several functions, or under a heap driver (§20). A block given to a generic function is
§31's; a block that uses an answering capability or a `for`'s threaded variables is §32's. A
named function with a row given at a block parameter is the block that calls it (§33).

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

Rejected: `corpus/reject/block-stored.bc`, and `corpus/reject/block-capability.bc` until §32.
Every program runs at the source stage, the closure and flat IRs and WebAssembly with `live 0`,
and passes `scripts/falsify.sh`'s four modes.

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
  data, boxed at a bound, whose row is inferred and never written (§32 *Open*).
- **`s.spawn { … }`**: spawning by a scheduler handle, which needs a provided effect (a port,
  decision 57) or an operation whose argument is a computation (the draft spec's OQ-61).
- **A handler's lifetime parameters**, so that a clause boxes `κ` at a bound other than `top`
  (a queue inside a lend, `corpus/sched-b.bc`'s `'d`): §32.
- **Blocks with answering capabilities** and **blocks at a `for`'s site** (threaded variables):
  §32.
- **Rank 2**: a block parameter has one row per copy; a function that calls one parameter at two
  rows that cannot share one is not expressible.
- **One copy per closure** (`docs/surface-callbacks.md` OQ-S6): two blocks of one row given to
  one copy are one code each, called through the closure's dispatcher where the flow cannot tell
  them apart.
- **Tasks that hold a borrow across `await`** under `lib/async.bc`'s scheduler: a task of `spawn`
  holding a relaxed lend, `cancel` of one (A6) and a scheduler that logs (A5) are §32's; L0 (U3)
  is not built.

## 31. Entry 30 — generic recursion, blocks to generic callees, and the inference gaps

### Motivation

§15's templates were refused where they met §20's recursion, §30's blocks and core `def`s with
type parameters: a recursive `map[A, B]` over a `List[A]` was rejected, a block with a row given
to a generic function was rejected, a generic `fn` called inside a core `def[A]` at `A` was
instantiated at a type it did not know (#136), and a pair given as the last argument of a generic
function was taken apart (#135). Each is elaboration: no `CDerives` rule, relation clause, machine
step or kernel type is added. The inventory is `docs/generics-inventory.md`.

### Generic recursive groups

A recursive group (§20) may be generic. Its members take the **same type parameters** and the
**same lifetime parameters** (by name); otherwise the group is rejected with a message. Then:

- the generator `g__step__…`, each layer's transformer (§21) and each member's copy are templates
  in the group's type parameters, made once per copy (per row and blocks, as in §18 and §30) and
  instantiated per use at the call's types (§15): a call from outside is a call of the copy, whose
  type arguments are read off the arguments as at any template;
- the group's lifetime parameters are the generator's and the copies' `all 'a < @.`, outside the
  capabilities' lifetimes (§21); a call of a member inside the group is at the group's own type and
  lifetime parameters, through the self-reference;
- under the heap driver (§20), the machine's source `g__mach_src` is a template, and each of its
  instances `g__gN__mach_src` is made into its machine `g__gN__mach` (`recMachine`), its frames at
  the instance's types; a member's copy `x__deep` names the machine at its type arguments,
  `g__mach[T, …]`, which is the machine of the source's instance at `T, …`.

A recursive function in a library module takes part in recursive groups as one of the program's
does; its reports are not printed, as a library copy's are not.

**Not provided**, each rejected with a message:

- **Polymorphic recursion**, a member calling itself at other type arguments: the self-reference
  is at the group's own types, and the call is a type error at its argument.
- **A recursive template sharing its name** with another function (`map` of `lib/list.bc` and of
  `lib/iters.bc` in one program): templates of one name are chosen by the arguments' types (§15),
  after the effects are elaborated, but a recursive group is found by name before that. A call of
  the shared name is rejected (`corpus/reject/rec-name-clash.bc`); a program that includes both
  modules and calls neither is accepted.

### Blocks to generic callees

A block with a row (§30) may be given to a generic function: the copy for the block is a template,
its block parameter at `!U(A ⊸ F_Σ B)`. At the call, type arguments are matched through the row
(`matchC` at `CTy.eff`), and a block, whose synthesized type has no row, is matched by its result
against the parameter with the row taken off (`pureArrow`); it is elaborated at the parameter's
type once that is known.

### Inference

- **A nested template call whose parameters leave a type parameter open** (`nil()` in
  `cons(7, nil())`) is typed last, as an injection is, from its parameter's type with what the
  other arguments determined. The effects elaboration binds a plain call whole, its arguments'
  calls in it (`liftCalls`), so that the typed elaboration still sees the nesting.
- **A pair as the last argument** of a generic call is one argument (`argOf`, #135).
- **A core `def` with type parameters whose body calls a template** is a template itself,
  instantiated where it is used (#136): its body is elaborated only at known types.

A type parameter that only a block's result determines (the start `nil()` of a `fold` whose block
answers a list) is not inferred: inference does not look into a block's body. It is written,
`nil[i32]()`.

### The library

`lib/list.bc` (`include list`): `List[A] = mu X. 1 + (A * X)`, `nil`, `cons`, and the recursive
templates `map`, `filter` (its `A` persistent: the predicate takes the element and the element is
kept) and `fold` (from the left). `lib/async.bc` includes it for `List`.

### Programs

`corpus/list-generic.bc` (`map`, `filter`, `fold` at several types, pure blocks),
`list-blocks.bc` (blocks that recurse and that raise, given to the generic `map`), `async-map.bc`
(A4, now the generic `map`: output and counts unchanged), `rec-generic-mutual.bc`,
`rec-generic-layer.bc`, `rec-generic-deep.bc` (three times the budget, under `deep`),
`rec-lifetimes.bc` (recursion with a lifetime parameter, generic and not), `generic-pair-arg.bc`
(#135), `generic-in-def.bc` (#136), `text-lend-lifetime.bc` (#167's S5 case);
rejects `corpus/reject/rec-generic-params.bc`, `rec-name-clash.bc`, `double-use-in-callee.bc`
(#145: reported at the use).

### Baseline

No change to `CDerives`, the relation, the machine, the checker or the backend. Every elaborated
form is typed by the existing rules; `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD`
keep their statements and cover every elaborated program. Every existing corpus and kernel program
keeps its output and counts.

### Open

- Templates of one name when one is recursive (above): module-qualified names, or choosing among
  them before the effects are elaborated (`docs/generics-inventory.md`, D1).
- Inference into a block's body (D3).
- Members of a group with type parameters of other names (D4).
- `data` declarations with constructors and patterns (#54 stage 8), generic or not.

---

## 32. Entry 31 — logged and scoped tasks, blocks that use capabilities, a handler's lifetimes

### Motivation

Three pieces §28 and §30 leave open (`docs/async-capabilities.md` §1, §2.3; #52):

1. **A5 and A6 on `lib/async.bc`.** §29's programs schedule stored generators inline; a scheduler
   that logs (A5) and a task cancelled while it holds a relaxed lend (A6) were not built on the
   library (§30 *Open*).
2. **Blocks that use a capability**: an answering handler's state, or the variables a `for`'s site
   threads (§30 *Not provided*; `corpus/pending/yield-callback.bc`).
3. **A continuation boxed at a bound other than `top`** from a surface handler (§28 *Open*, §30
   *Open*), so that a task may hold a borrow from outside, as `corpus/sched-b.bc` does in the
   core text.

Each is elaboration into core terms the checker already derives, and `lib/async.bc`: no
`CDerives` rule, relation clause, machine step or kernel type is added, and `PinLaw` is unchanged.

### `log`, and the logged scheduler

`Async` is `effect Async { ctl await(); ctl log(x: i32) }`. `log` is affine, resumes, answers `1`
and takes closed data, so `Row.ResumeO` admits it (§29) and a `log` inside a relaxed lend is R1.

- `spawn`'s clause of `log` resumes at once: a task run by `spawn` logs nothing. **PROPOSED**
  (the alternative is to give `log` an effect of its own, which needs a handler of two effects).
- `with spawn_logged { M }` answers the task stopped: `Stopped[A] = A + ((1 + i32) * LTask[A])`,
  `LTask[A] = box top U (nu X. F (A + ((1 + i32) * box top U X)) & F 1)`. Its clauses of `await`
  and `log` keep `κ` (BOXED-κ at `top`) and answer `inr (inl (), t)` or `inr (inr x, t)`, `t` the
  rest; the return clause answers `inl v`.
- `lpush(q, s)` records the entries a task logged before its first `await`; `run_logged(q)` runs
  the queue round robin until no task is pending, each pending task resumed once per round and run
  past its logs (`drain`), so a `log` lets no other task run. It answers the tasks' values in the
  order they were queued and the entries in the order they were logged. The drain and the rounds
  are unbounded, so `drain`, `lround`, `run_logged` and `reverse` are div (§14). The spellings
  are provisional.

### Blocks that use capabilities

A block (§30) whose body uses capabilities, an answering handler's state or a `for`'s threaded
variables, **takes them first and hands them back first**: its type at the copy is
`!U(C ⊗ A ⊸ F_r (C ⊗ B))`, `C` the capabilities. The callee's copy for the block takes them after
its own row's, and each call of the block parameter passes them and binds them again, as a call of
a copy with capabilities does (§18). So the block's operations are those of where it is written
(§30): its `tick` is the state of the `with` around it, its `yield` the operation of the `for` it
is inside.

- A handler or a `for` of the same effect inside the copy does not shadow a block's capability
  (`Cap.blk`): the copy's own operations go to its innermost handler, the block's to the
  capability it was given.
- A copy's key adds the answering handlers the block uses (`b{j}n{…}{handler}`).
- A `for`'s threaded variable has a type that is a parameter of the copy (§15); a block's is
  renamed in the copy (`W` to `Wb`) unless the copy's own row is served at that `for`, so that it
  is not the caller's parameter of the same name (`Blk.inCopy`).
- The typed elaboration types a closure argument at its parameter's type when that is known and
  the closure's synthesized type does not show it: a block whose result is the threaded variable,
  which an operation answers (`Frontend/Sugar.lean`).

A closure that is not a block argument still performs no operation of a capability
(`corpus/reject/effect-in-closure.bc`).

### A handler's lifetime parameters; tasks over an outer borrow

    handler h[T, …]<'d, …>: E[…], A -> R = { … }

At each `with h { … }`, each lifetime parameter is the meet of the lifetimes in scope there
(`Δ.meetOfDom`, `dom` of §23), substituted in the handler's types and clauses (`HInfo.lives`,
`hndCtlC`). A clause that keeps its continuation receives it boxed at that lifetime: the site's
clause tuple is `clausesTyB Σ R d E` (§28) at `d` the meet, and the checker types it by
`effHandleVB`, whose premises are decided as at §28 (`corpus/reject/spawn-in-unscoped.bc`). A
bound on a handler's lifetime parameter, and a lifetime written at the `with`, are not provided.
**PROPOSED**: the instantiation at the meet (a written lifetime would need syntax at the `with`).

`lib/async.bc` declares `type TaskIn[A]<'d> = box 'd U (nu X. F (A + box 'd U X) & F 1)`, the
handler `spawn_in[A]<'d>` (`spawn` boxed at `'d`), `resume_in`, `cancel_in`, `queue_in`, `push_in`
and `run_in(q, rounds)`, which runs the queue round robin for at most `rounds` rounds, a counted
loop: a total computation, which runs inside the scope of the borrows its tasks hold. A task still
pending after the last round is cancelled and `run_in` performs `exhausted()` (`lib/rec.bc`), as a
recursion that spends its budget does. A borrow `'r` outlives the meet only below a scope of its
own (the `Imm` rule is strict, §23), so the tasks are spawned inside a unit cell's borrow, as
`aff-capture.bc`'s `'w`.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/async-logged.bc` | A5: two tasks log their cell before and after an `await` while lending it (R1), and raise and handle an error inside the lend | `([30, -2], [3, 2, 3, 2])`, `assurance: PinLaw (R1 at 23:11)` | `22 4 0` |
| `corpus/async-cancel.bc` | A6: a task holding a relaxed lend and an owned cell is cancelled by another task | `[2]`, `live 0`, `assurance: PinLaw (R1 at 24:11)` | `10 3 0` |
| `corpus/async-scoped.bc` | two tasks read an outer `imm` borrow across their `await`s, spawned at a bound below it | `[84, 126]`, unconditional | `25 4 0` |
| `corpus/yield-callback.bc` | a block that yields to its caller's `for` (moved from `pending/`) | `30` | `0 0 0` |
| `corpus/block-yield-inner.bc` | the same, given to a function with a `for` of its own | `30` | `0 0 0` |
| `corpus/block-capability.bc` | a block that uses an answering capability (moved from `reject/`) | `6` | `1 0 0` |
| `corpus/block-capability-inner.bc` | the same, given to a function with a handler of its own | `105` | `2 0 0` |
| `corpus/list-capability.bc` | the same, given to the generic recursive `map` | `[11, 22, 33]` | `7 0 0` |
| `corpus/async-workers-scoped.bc` | #479's worker pool: workers hold an outer `imm` borrow across their `await`s | `([63, 92], 155)`, unconditional | `43 7 1` |

Rejected: `corpus/reject/spawn-in-unscoped.bc`. Every program runs at the source stage, the closure
and flat IRs and WebAssembly with `live 0`, and passes `scripts/falsify.sh`'s four modes.

Adapted from `docs/async-capabilities.md` §1: A6 answers `[2]`, not `[cancelled, 2]`, since a task
is a linear value and the victim is held by the task that cancels it, not by the queue; and its
finaliser log `[10, 11]` is not written: the lend's finaliser is typed pure at the empty context
(R1's `· ⊢ d : Ref T ⊸ 1`, §29), and the backend does not lower a finaliser that performs a control
operation (§27 *Open*). `live 0` and `--check tags` show that both cells are freed and the lend
ends before its cell is.

### Lowering

Nothing is lowered specially: a block's capabilities are arguments and results, and `spawn_in`'s site is §19's handler with a clause that keeps
`κ`.

### Baseline

No change to `CDerives`, the relation, the machine, `PinLaw`, the checker, the backend or a kernel
program. `fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD` cover every program above
that uses no relaxed rule, and `fundamentalC_pin` and `adequacyD_pin` the two that use R1. Every
existing corpus and kernel program keeps its output and counts; the reports of
`corpus/async-scheduler.bc` and `corpus/async-map.bc` name `log` in `spawn`'s lowering line.

### Open

- **Stored callbacks with their row** (`docs/async-capabilities.md` §2.3): a closure that performs
  control operations stored in data or returned, its type `U(A ⊸ F_Σ B)` carrying the row of the
  sites where it is written, and a function given such a value copied at its row (§14's
  specialization at a callback's type, at a row as at `div`). Not built: the inference of the row
  of a type written without one (a `let` annotation, a type parameter, a data type's component)
  is a design question, and with it the join of rows across the elements of one data value. §33
  *Open* lists the options, with §33's type `!(A => B with E…)`.
- **`div` callbacks in data and in a fold's algebra** (`corpus/pending/callbacks-in-data.bc`,
  `map-div-fold.bc`): a fold whose algebra is div (the children's loops sequenced, then the
  algebra run as a div body), and a data type at the join of its elements' effects; unchanged.
- **An `imm` relaxed lend** (OQ-2): `corpus/pending/async-borrow.bc`'s `fold_imm` whose algebra
  yields stays pending.
- **A function with a row passed as a value**: at a parameter of function type it is the block
  that calls it, and a computation parameter serves what its type provides (§33). Passing it by
  name, served where the callee calls it, was built and taken out: it makes `f(g)` and
  `f({ x -> g(x) })` handle effects differently, so who handles an argument's effects would be
  decided by syntax, not by type.
- A6's finaliser log; a lifetime written at a `with`.

---

## 33. Entry 32 — computation parameters and `|>`

### Motivation

#161, part A (§18 *Open*, §30 *Open*, §32 *Open*). A function that handles the effects of a
computation it is given: a generator consumer, `retry`, a timeout, the reconciler chain
`timeout |> retry |> log`. A block given at a parameter of function type keeps its effects where it
is written (§30, E6), and a named function passed by name was refused, because serving it where the
callee calls it made `f(g)` and `f({ x -> g(x) })` differ in who handles (§32 *Open*). Here the
callee says, in its parameter's type, which effects it serves for the argument (decision 57's
provided row), and `f(g)` is `f({ x -> g(x) })` at every parameter. `|>` is decision 50's.

Everything is elaboration into core terms the checker already derives (`Frontend/Elab/Effects.lean`;
the kernel program `sum-gen`, `dAt_sumGen` in `Core/EffTier1Programs.lean`, is the shape: a thunk
`U(1 ⊸ F_{yield ⊙ r} 1)` passed to a function that forces it under its own `handle`). No `CDerives`
rule, relation clause, machine step or kernel type is added.

### Laws

Each is stated of the elaborated terms and holds by the deep-handler laws already proved (§19
*Laws* item 1) or by the elaboration's definition:

1. **`m |> h ≡ with h { m }`.** The elaboration rewrites `m |> h[As](e, …)`, `h` a handler, to
   `with h[As](e, …) { m }` before anything else (`resolvePipes`): they are one term, and its
   meaning is the handler's (H-ret, H-op; `catch_ret`, `catch_step`). Holds by definition
   (`corpus/pipe-handlers.bc`: `a` and `b`).
2. **Chains are associative.** `m |> s₁ |> s₂` is `(m |> s₁) |> s₂` (`|>` associates to the left),
   applied innermost first: `s₂` around `s₁` around `m`. A chain of handlers grouped as one stage,
   a function whose computation parameter provides their effects (`both(c) = c(()) |> s₁ |> s₂`),
   elaborates to the same nested sites, each named by the port of its effect, so `m |> s₁ |> s₂`
   and `both(m)` are one term up to static names (`corpus/pipe-handlers.bc`: `a` and `c`). Holds
   for handler stages. A chain grouped across a stage that is itself a function over a
   computation (`both(c) = c(()) |> retry(…)`) calls `c` inside the block given to `retry`, where
   `c`'s provided effect is served at `retry`'s port, not `c`'s own: that is a computation
   parameter passed on, not provided yet (*Ports*, below; *Open*). So associativity of function stages
   holds of the chain as written, not yet of a regrouping into a function.
3. **Operations a stage does not handle pass to the next stage.** For a handler stage, H-fwd
   (`catch_fwd`, `fwd_resume`, `fwd_abort`): an operation of another name passes the site. For a
   function stage, an operation of the computation outside the parameter's provided row is resolved
   where the computation is written (*The argument*), which is inside the next stage; and an
   operation the stage provides but does not serve itself goes to the stage's own row, served by
   its caller, the next stage. Holds (`corpus/reconcile-chain.bc`: the step's `note` and `sleep`
   pass `timeout` and `retry`; `timeout`'s 408 passes to `retry`; `pipe-handlers.bc`: `a` and
   `e`).
4. **A plain block keeps lexical handling.** §30's rule is unchanged: a block at a parameter whose
   type has no provided row performs everything where it is written (`corpus/effects-tunnel.bc`
   unchanged; `corpus/comp-param.bc`'s `pass`; `corpus/reject/block-raise-lexical.bc`). Holds.

### The computation parameter

A parameter whose type is a function type with a provided row is a **computation parameter**:

    fn retry[A](times: i32, base: i32, f: !(i32 => A with Fail[i32])) -> A with Fail[i32], Clock

**PROPOSED** spelling: the row is written after the function type inside parentheses,
`(A => B with E₁, E₂[T, …])`, and `!(…)` for a persistent one; it is the surface type former
`VTy.rowed`, read by the parser and printer and elaborated away by `Frontend/Elab/Effects.lean`.

- **The provided row** is what the callee serves for the argument. A call `f(v)` in the callee
  performs the provided effects at that point of the callee, resolved lexically there as an
  operation is (§19 *Names*): to the innermost `with` of the effect in the callee around the call,
  or, when none is, to the callee's own row, served by its caller.
- **Every other effect of the argument tunnels**: it is resolved where the argument is written, as a
  block's are (§30).
- A function with a computation parameter is elaborated only through its copies, one per row of
  the argument's tunneled effects (§30's key, `b{j}n{…}`), never as written; a call of it is a call
  of its copy, and it is not a value. Its row (§18 *Rows*) has the provided effects of the calls of
  the parameter outside the callee's handlers, besides its own.

### Ports

For each control effect `E` of a computation parameter's provided row, the copy fixes one static
name, its **port** (decision 57), at which the argument performs `E`:

- when the copy calls the parameter outside every `with` of `E`, the port is the site of `E` in the
  copy's own row, its caller's;
- otherwise the port is a fresh name, and each `with` of `E` in the copy whose body calls the
  parameter (outside a `with` of `E` inside it) has the port as its static name (`Cx.portIn`).

**PROPOSED, provisional until a port can be relabelled** (decision 57 leaves the relabelling
open): today one port serves every call, so a parameter called both inside a `with` of `E` and
outside one is not provided (`corpus/pending/comp-param-two-sites.bc`), nor are two parameters
that provide `E` at two ports under one `with`. This is the current behaviour, not a rule of the
language: the abortive case can be relabelled by a site whose clause raises again at the other
name (decision 57, R2c), and the resuming case needs inlining or a `rename` primitive; neither is
built (*Open*).

The kernel checks each port as any site: `[handle]` asks the port to be absent from the site's
outer row, which a fresh name is. The argument's type names the port where the argument is
written, outside the port's site; a value has no row, so nothing is performed there, and decision
57's site freshness (R3) reads a provided port as bound.

### The argument

- **A block written in place** is elaborated where it is written, its operations of the provided
  effects at the copy's ports and the others at the sites around it, the capabilities it uses taken
  first and handed back first (§32). The copy is made first, so that its ports are known
  (`blockCall`).
- **A function named** at a parameter of function type, a computation parameter or a plain block
  parameter whose function has a row, is the block that calls it: `g` is `!{ a -> g(a) }`
  (`{ a -> g(a) }` at a parameter that is not `!`; `etaArgs`). So `f(g)` and `f({ x -> g(x) })`
  are one argument at both kinds of parameter (`corpus/comp-param.bc`). Elsewhere, a function with
  a row passed as a value is refused as before (§18 *Not provided*).
- **The call** binds the argument at the copy's parameter type, `!U(C ⊗ A ⊸ F_{ports ∪ T} (C ⊗ B))`
  (`C` the capabilities, `T` the tunneled sites, in the order of the argument's row), so the block
  is checked at its row (§30).

**Not provided** yet, each refused with a message that says so; the programs that wait on them are
in `corpus/pending/`, not `reject/`:

- a provided answering effect (an answering effect is a capability, and the callee's handler of it
  would lend its state to the argument: decision 57's R2d);
- a computation parameter's argument that uses a capability, called inside a control `with` of the
  callee (`corpus/pending/comp-param-capability.bc`, #487): the `with`'s body is lent the capability
  anew, at a lifetime of its own, and the argument takes it at the copy's (*Open*);
- a block parameter passed on to a computation parameter (*Ports*);
- a `for` over a call of a computation parameter (`corpus/pending/comp-param-for.bc`): a `for`'s site
  threads the loop's variables through its operation (§15), at a type only the callee knows; a
  handler serves the parameter's iteration effect instead (`gen(()) |> h`);
- a computation parameter of a recursive function (§20).

### `|>`

`e |> s` is an operator of the lowest precedence, below `||`, associating to the left; each stage
`s` is a spine: a name, or a name applied to its other arguments (decision 50: `e |> f(a, …)` is
`f(e, a, …)`, the piped value first). By the stage (`pipeStage`, before the rest of the
elaboration):

- **a handler** `h`, `h[As]` or `h[As](e₁, …)`: `with h[As](e₁, …) { e }` (law 1);
- **a function whose first parameter is a computation parameter**, which takes `1`: `f(!{ () -> e },
  a, …)`, `e` suspended (`{ () -> e }` at a parameter that is not `!`);
- **any other function**: `f(e, a, …)`. A generator's call piped into an adapter is at its stored
  generator parameter, and is stored there (§15; `corpus/gen-pipeline-pipe.bc`).

**PROPOSED**: a handler stage given a lent place (`|> h(&mut c)`) is rejected, with a message to
write `with h(&mut c) { … }`, which hands the place back; the parser gives `with`'s body the
variables it assigns and the places it lends, and a stage is resolved after parsing. A first
parameter that is a computation parameter taking an argument is rejected at `|>`.

### Elaboration at the row

One fix in the typed elaboration (`Frontend/Sugar.lean`): an annotated binding `x : A <- M` whose
head performs operations of the current row elaborates `M` at `F_Σ A` (`Σ` the row), as the
checker reads it when `F A` fails (*Choices beyond draft 1*, §19 *Effectful binds*), so a `with`
inside it handles its body at the row around it. A counted loop at a resuming row (§30) binds its
step's result so; a `with` in its body was elaborated at the empty row before
(`corpus/reconcile-chain.bc`'s `retry`). Every existing program elaborates to the same output and
counts.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/retry-block.bc` | `retry` serves its computation's `Fail` at its port: the service is retried | `((inl i32[200], i32[30]), (inr i32[503], i32[10]))` | `2 0 0` |
| `corpus/effects-sum-gen.bc` | E2d from source (moved from `pending/`): `any(gen) = gen(()) \|> any_true` at `Yield` alone and with `Fail`, which passes `any`'s handler | `(inr (), inr ())` | `0 0 0`, as the kernel's `sum-gen` |
| `corpus/comp-param.bc` | `guard` (a computation parameter) and `pass` (a plain block parameter), each given a block and a named function | `((inr i32[7], inr i32[7]), (inr i32[8], inr i32[7]))` | `0 0 0` |
| `corpus/pipe-handlers.bc` | laws 1–3 for handler stages: `\|>` is `with`, a chain grouped as one stage, the order of a chain | see the file | `0 0 0` |
| `corpus/gen-pipeline-pipe.bc` | the adapters chained with `\|>` | `i32[320110]` | `0 0 0` |
| `corpus/reconcile-chain.bc` | `step() \|> timeout \|> retry(3, 10) \|> logged`, with a fake clock, a fake service and a journal | see the file | `28 3 0` (§34) |

Rejected, a rule of the language: `corpus/reject/block-raise-lexical.bc` (a plain block's `raise`
is not the callee's). Pending, each waiting on an *Open* item: `corpus/pending/comp-param-two-sites.bc`,
`comp-param-capability.bc`, `comp-param-for.bc`. `corpus/reports/comp-param.txt` and
`effects-sum-gen.txt` pin the reports: each copy's ports (`its `Fail` at the port 6, served by its
`with` here`), each call of a computation parameter (`its `Fail` served here by the site 6`) and
each call that passes one (`its computation performing `Fail` at the port 6 of `guard``). Every
program runs at the source stage, the closure and flat IRs and WebAssembly with `live 0`, and
passes `scripts/falsify.sh`'s four modes, except that `gen-pipeline-pipe` is `check: no-source`:
the source interpreter takes about twenty minutes over it (§15 *Open*).

**`corpus/retry-block.bc` changes its output on purpose**: its `retry` now takes `f: !(i32 => A with
Fail[i32])`, so the block's errors are `retry`'s, and the program retries, answering
`((inl i32[200], i32[30]), (inr i32[503], i32[10]))` where it answered
`((inr i32[503], i32[0]), (inr i32[503], i32[0]))`. Its counts are unchanged.

`reconcile-chain`'s clock, service and journal are control effects whose handlers fold the
computation's answer: an answering capability cannot be used by an argument called under the
callee's handler (#487), which reproduces without any construct of this entry (*Open*). Its
service with a state and its operations that answer values, which the backend failed on (#485,
#486), are §34's: the backend fixes and the program are there.

### Lowering

Nothing is lowered specially: a copy is a `def`, a port a static name, the argument a closure, and
`|>` is gone before the typed elaboration.

### Baseline

No change to `CDerives`, the relation, the machine, `PinLaw`, the checker, `Core/`, `Paper/`,
`Support/` or `Backend/`. Every elaborated program is checked by the unchanged checker, so
`fundamentalC`, `adequacyC`, `fundamentalD` and `adequacyD` cover it with no hypothesis (none of
the programs above uses a relaxed rule). Every existing corpus and kernel program elaborates, checks
and runs as before, with the same output, counts and reports, except `retry-block`'s output (above).

### Open

- **Relabelling a port** (decision 57, R2c): a computation parameter called inside and outside its
  callee's handlers (`corpus/pending/comp-param-two-sites.bc`), passed on to another computation
  parameter, or two of one effect under one site. Abortive: a site whose clause raises again at the other name, typable today. Resuming:
  inlining, or a `rename (p, m)` primitive (one frame, one compatibility lemma).
- **A capability used by the argument under the callee's handler**: the argument would take its
  capabilities at lifetimes of its own, `!U(∀'x. Mut 'x S ⊗ A ⊸ F_Σ (Mut 'x S ⊗ B))` (decision 57,
  R2a), instantiated at each call (#487). Built and taken out: the checker compares types without
  α-conversion of lifetime binders (*Incompleteness* 2), and the argument's type, elaborated where
  it is written, has other binders than the callee's parameter type instantiated at the call.
  The same limit holds of §32's blocks.
- **Provided answering effects** (R2d) and a `for` over a call of a computation parameter
  (`corpus/pending/comp-param-for.bc`).
- **Stored callbacks with a row** (part B, §32 *Open*). The same type, `!(A => B with E…)` in a
  `let`, a data type or a type parameter, needs choices this entry does not make:
  - *where its ports are fixed*: by the stored type, one per type declaration (decision 57, R6:
    every `with` of `E` around a call of a stored value of that type takes the port; two types'
    ports of one effect under one `with` are rejected), or per binding (each `let` its own ports,
    which a value of the type cannot leave);
  - *its tunneled row*: none (a stored callback performs only what its type provides, and its
    creator's handlers are out of reach once it is stored, which R3's site freshness asks), or
    fixed at the binding and checked at each call to be in scope there;
  - *its captures*: `!` values only (§2's promotion, #9 to widen), or a box at a lifetime
    (`[@c] !U(…)`, §28), with the answering capabilities passed in by each caller (R6);
  - *the join of rows* across the elements of one data value: written, or the union inferred.
  Each is a decision about what a stored value means, not an elaboration detail: §32 *Open*
  remains, with these options.
- **Associativity across function stages** (law 2): it needs the relabelling above.

---

## 34. Entry 33 — IO as effects: the platform as the outermost handler

### Motivation

#156, the IO capability pass. §11 gives a program its standard streams as capabilities, cells with
opaque content lent to externs, and a helper that does I/O takes the cell as an argument. Effects
are in the kernel (§19), and an answering operation is a call on a capability value (§18): a
function that performs `print_bytes(v)` is given the capability by its row, as a function that
calls `putb(o, b)` is given `o` by its parameter. This entry makes the standard streams, the clock
and the arguments answering effects whose outermost handler is the platform package, a library
module that serves them with the externs. `main` is the only place they are ambient; every other
function is given them by its row; a test serves them with a handler of its own (a fake clock, a
buffer for an output), by the handler alone.

What exists and is reused, no new mechanism where one serves:

- an answering effect is a capability (§18 *Elaboration*; `Frontend/Elab/Effects.lean`, `withBlk`,
  `opCall`, `clauseDef`): `with h(&mut c₀) { M }` is a borrow of the cell `c₀`, and an operation
  is a call of the clause on the capability, which hands it back;
- a function with a row is copied for what serves it, taking the capabilities first and handing
  them back first (§18 *Rows*), so a function's row is the capabilities it is given, and a written
  row is a promise checked against the inferred one;
- §11's capability externs `stdin`, `stdout`, `stderr`, cells the runtime allocates and `main`
  hands back (`Frontend/Check/Externs.lean`, `stdExterns`; `Backend/Driver.lean`, `extImpls`),
  the operations `read_byte`, `write_byte`, `write_all`, `read_into` and their models
  (`Core/Stdio.lean`), and `bcc trusted` (`trustedReport`);
- §11's ambient `main` (`Frontend/Sugar.lean`, `ambientMain`), which adds the capability externs
  `main` uses and hands them back by name;
- tasks over an outer borrow (§32, `spawn_in`), blocks and computation parameters that use
  capabilities (§32, §33), and the per-observation lend of a borrow block over a loop (§14,
  `Frontend/Elab/LoopLend.lean`).

### Laws

Each effect's equations, on the runs of a handled computation. A handler is lawful when the runs of
every body it handles satisfy them. The platform's handlers are lawful by the host's contract
(*Assurance*), the model's by its definition (`Core/Stdio.lean`), and a fake handler by
construction: its clauses are a fold over the operations that keeps the equations termwise.

- **`Stdout`, `Stderr`.** What a run writes is the concatenation, in order, of what its operations
  write: `print_byte(b)` writes `[b]` and `print_bytes(v)` the bytes of `v`. So
  `print_bytes(v) ≡ print_byte(v[0]); …; print_byte(v[n-1])`, and `print_bytes` of an empty view
  writes nothing. The two streams are separate: a write to one leaves the other as it was.
- **`Stdin`.** The input is a byte list fixed before the run. `input_byte()` answers its next byte
  and consumes it, or `inr ()` at its end, and keeps answering `inr ()` after it. `input_into(v)`
  is `input_byte` into the slots of `v` from its start until it is full or the input ends, and
  answers the view and how many bytes it read, which is less than `v`'s length only at the end.
- **`Clock`.** `now()` answers an `i64` time in nanoseconds since an arbitrary fixed origin,
  monotone within a run: a later `now()` answers no less than an earlier one. `sleep(ns)` takes an
  `i64` duration in nanoseconds and waits at least `max(ns, 0)`: a `now()` after it answers at
  least the `now()` before it plus `max(ns, 0)`, or `2^63 − 1`. Times saturate at `2^63 − 1`
  (about 292 years), a sum that would pass it answering it, so the
  laws hold in every run. The time a run spends computing is unspecified: a handler may count it
  (the platform) or not (a fake clock, the model).
- **`Args`.** The arguments are a list of byte strings fixed before the run. `arg_byte()` answers
  their bytes in order, each argument followed by `0`, then `inr ()`, and `inr ()` after it.

`corpus/io-laws.bc` runs each law's two sides under a fake handler and compares them.

### The effects

`lib/sys.bc`, the system interface (**PROPOSED** spellings and shape, *One-way doors* below):

    effect Stdin  { fn input_byte() -> u8 + 1; fn input_into<'b>(v: array_mut 'b u8) -> array_mut 'b u8 * i32 }
    effect Stdout { fn print_byte(b: u8); fn print_bytes<'b>(v: array_imm 'b u8) }
    effect Stderr { fn eprint_byte(b: u8); fn eprint_bytes<'b>(v: array_imm 'b u8) }
    effect Clock  { fn now() -> i64; fn sleep(ns: i64) }
    effect Args   { fn arg_byte() -> u8 + 1 }

- **Answering, every one.** Each operation answers at once and its clause runs in place, a call on
  the capability (§18): the least general kind that serves the programs. None suspends. A program
  whose own computations wait on time with a control operation serves it with a handler whose
  clause calls `sleep` (`corpus/reconcile-clock.bc`'s `on_clock`).
- **One effect per stream.** `Stdout` and `Stderr` are two effects with the same operations: they
  were written when a row held one instance of an effect, and a row may now hold two, named (§38),
  so merging them into one effect is a later change of the library (§38 *Open*). A writer that does not care
  which stream it writes to takes §11's output cell, or is written once over a block (§30) given
  `print_byte` or `eprint_byte` (`lib/io.bc`'s `dec_each`).
- **Bytes, and a view per call**, as §11's operations: a byte, and a view for one system call per
  view. Text, numbers and lines are library code.
- **`Args` is a byte stream**, each argument followed by `0`, as WASI's `args_get` and
  `/proc/self/cmdline` lay them out; `next_arg` (`lib/textio.bc`) reads one into a string. The
  program's own name is not an argument.
- **Operations with lifetime parameters.** An answering operation may take lifetime parameters,
  `fn print_bytes<'b>(v: array_imm 'b u8)`. Its clause `h__op` takes them after the capability's,
  `fn h__op<'l, 'b>(c: mut 'l S, v: array_imm 'b u8) -> mut 'l S * B`, and each call instantiates
  them as a call of a function with lifetime parameters does. A control operation does not take
  them (a parse error).

### The platform package

A platform is a library module that serves the system interface with externs. `lib/wasi.bc` is
WASI preview 1's:

    include sys
    extern read_byte, write_byte, write_all, read_into                     (§11)
    extern clock_now : !(all 'a < top. mut 'a clock => mut 'a clock * i32)
    extern clock_sleep : !(all 'a < top. mut 'a clock * i32 => mut 'a clock)
    extern read_arg : !(all 'a < top. mut 'a args => mut 'a args * (u8 + 1))
    handler wasi_stdin(&mut i: input): Stdin = { input_byte() = { let (j, r) = read_byte(i); i = j; r }; … }
    handler wasi_stdout(&mut o: output): Stdout = { print_byte(b) = { o = write_byte(o, b) }; … }
    handler wasi_stderr(&mut o: output): Stderr = { … }
    handler wasi_clock(&mut c: clock): Clock = { now() = { let (d, t) = clock_now(c); c = d; t }; … }
    handler wasi_args(&mut a: args): Args = { arg_byte() = { let (b, r) = read_arg(a); a = b; r } }

- **A handler whose state is lent**, `handler h(&mut s: S): E = { … }`: each clause is given the
  state lent, `s : mut 'l S`, the capability itself, and hands back the borrow it ends with:

      fn h__op<'l>(c: mut 'l S, x: A) -> mut 'l S * B = let s = c; M; (s, r)

  where §18's clause runs on the state's value, swapped out of the cell (`withswap`). It is what a
  handler over an opaque state needs: its externs take the state lent, and its value cannot be
  inspected. A clause is then a call of the extern on the capability, with no swap. A control
  handler's state is not lent (a parse error).
- **The capabilities.** `stdin`, `stdout`, `stderr` (§11), `clock : ref clock` and `args : ref
  args`, two new opaque kinds (*The models*). Each is an extern of `main` when `main` uses it, a
  cell the runtime allocates, which `main` hands back.
- **The ambient table** (`Frontend/Elab/Effects.lean`, `platformEffects`): each effect of the
  interface with its capability and its platform handler, `Stdin → stdin, wasi_stdin`, … . It
  names the one platform there is. **PROPOSED**: a second platform (`posix`, over libc's `read`,
  `write`, `clock_gettime`, `nanosleep` and `argv`, the externs' contracts unchanged, decision 25)
  is a second module and table, chosen by a build option; neither is built.

### `main`

`main` is the only place the effects are ambient. An effect of the interface that `main`'s body
performs (its inferred row, §18) and that no `with` in it handles is served by the platform's
handler of it, and its capability becomes one of `main`'s capability externs, handed back as §11's
are. So `main -> A` performing `Stdout` elaborates to `main : F (ref output ⊗ A)`.

- **`main` holds the cells.** A platform capability is the cell itself, threaded by name as §11's
  are, and each operation lends it to the clause for one call: `borrow mut stdout { 'x, m ->
  wasi_stdout__print_byte(m, b) }`, which is §11's `putb`. A function called from `main` is copied
  for the cell (`f__wasi_stdout_cell`), and lends it the same way. The cell, not a borrow of it,
  because a loop without a bound (§14) holds what it threads between observations, and a borrow
  cannot be held there: a function that loops over the input (`read_input`, `next_arg`, a `while`
  in `main`) threads the cell, as §11's `for b in bytes stdin` does. Inside a control `with`, whose
  body may be abandoned, the cell is lent for the body (§18), and the body's operations are calls
  on that borrow.
- **No other function is given an effect it does not name.** A function's copy takes exactly the
  capabilities of its row, and a written row that leaves out an effect the function performs is
  rejected (`corpus/reject/io-unlisted.bc`).
- **§11's capability values stay.** A `main` that names `stdin`, `stdout` or `stderr` uses the cell
  as before (§11 *Sugar*). The I/O library is then included first, as `include io`, since its
  helpers are written over the platform's handlers. A `main` that both names a stream's cell and
  performs its effect is rejected with a message (the cell is the effect's capability).

### Tasks

A task performs the effects its body performs; they are resolved lexically where it is spawned
(§30). **PROPOSED**: a task of a handler whose clauses keep the continuation boxed at the handler's
lifetime (`spawn_in`, §32) is *given* the capabilities its body uses: its continuation holds them,
where the body of any other control `with` is lent them anew (§18), since it may be abandoned. A
task outlives its `with`, so the capabilities are lent for the innermost borrow block around the
spawn, whose lifetime bounds the tasks (§32's `borrow mut d { 'd, … }`): the block takes a borrow of
each, gives it to the task, and does not hand it back; after the block the capability is `main`'s
again. A capability is a `mut` borrow, so one task holds it at a time, until it ends or is
cancelled (a borrow has no destructor to run, so a cancel is safe). Two tasks given one capability
in one block are rejected with a message (`corpus/pending/io-two-tasks.bc`), and so is a task
spawned outside every borrow block. `corpus/io-task.bc`: a task writes to standard output across
its `await`s.

### The library

- `lib/io.bc`: `include wasi`; §11's helpers over cells, each the platform's handler lent the cell
  around one operation (`fn putb(o: Out, b: u8) -> Out * 1 = with wasi_stdout(&mut o) {
  print_byte(b) }; (o, ())`), so that an extern is called only by a platform handler; `put_dec`
  and `bytes` over those; and over the effects, `dec_each(x, put)` (the digits of `x` given to a
  block), `print_dec`, `eprint_dec`, `ns_of_ms` (milliseconds as the clock's nanoseconds), and at
  `i64` `dec64_each` and `print_dec64` (#490).
- `lib/textio.bc`: `include text`, `include io`; §17's helpers over cells; and over the effects,
  `print_lit`, `print_str`, `print_string`, `eprint_lit`, `eprint_str`, `read_input` (the whole
  input into a string, in chunks of `input_into`), `next_arg` (the next argument appended to a
  string, and whether there was one).

### The models

Two new opaque kinds (§11 *Opaque host types*), each a leaf with its model, `Imm̲ = Unk`, no
destructor:

- `clock`: `clock.Holds v ⇔ ∃ t, v = i64[t]`, the time in nanoseconds. Its representation is `I64`
  (`vC_clockRep`).
- `args`: `args.Holds v ⇔ BytesV v`, the arguments not yet read, as an input's. Its representation
  is `Bytes` (`vC_argsRep`).

| extern | type | model |
|---|---|---|
| `clock_now` | `!(all 'a < top. mut 'a clock => mut 'a clock * i64)` | `withswap` answering the time and keeping it |
| `clock_sleep` | `!(all 'a < top. mut 'a clock * i64 => mut 'a clock)` | `withswap` adding `max(ns, 0)`, saturating at `2^63 − 1` |
| `read_arg` | `!(all 'a < top. mut 'a args => mut 'a args * (u8 + 1))` | `read_byte`'s, at `Args` |
| `mk_clock`, `take_clock` | `!(1 => ref clock)`, `!(ref clock => i64)` | `alloc i64[0]`, `free` |
| `mk_args`, `take_args` | `!(Bytes => ref args)`, `!(ref args => Bytes)` | `mk_input`'s, `take_input`'s |

`clockNow_meets`, `clockSleep_meets`, `readArg_meets`, `mkClock_meets`, `takeClock_meets`,
`mkArgs_meets`, `takeArgs_meets` (`Core/Stdio.lean`): the Fundamental Property of each model at the
representation, as §11's, and `stdModel` gains them, so `io_every_run` and `IORun.every_run` cover
a program that uses them. `run_io` makes the clock at time `0` and the arguments from their bytes
(written into the wrapper as a literal), and takes them back; its type does not change.

### Lowering

Zero cost against §11's direct extern calls. An operation is a direct call of the platform's clause,
which is a direct call of the extern on the lent cell, lent by `withbor2` as §11's `putb` lends it:
no allocation, no dispatched call, no copy. `corpus/io-upper-effects.bc` is `io-upper` over the
effects, at `io-upper`'s counts (`2 0 0`), and every §11 program keeps its counts.

- `clock_now` is WASI `clock_time_get` of the monotonic clock, in nanoseconds since the clock's
  first use (the origin), saturating; `clock_sleep` is `poll_oneoff` on one relative clock
  subscription of `ns` nanoseconds (`clock_gettime` and `nanosleep` in libc). The cell's content is the model's and
  the runtime does not read it. The closure and flat IRs' interpreters run the model: the cell
  holds the time, and a sleep adds to it.
- The arguments are read once, at their first use, with `args_sizes_get` and `args_get`, into
  memory the runtime takes from the top of the heap, which is no object and is never freed, and
  counts as one allocation (§35); the clock's and the arguments' cells are words of the program's
  data (§35); the
  `args` cell holds the stream `0xFFFFFFFF`, which `$getc` and `$getv` read from there
  (`Backend/Wasm/Runtime.lean`). `bcc interp … -- arg…`, `bcc run <file> arg…`,
  `bcc-counts <file> -- arg…`, and `<name>.args` (one argument per line) in
  `scripts/compile-corpus.sh` and `scripts/falsify.sh`.

**Two backend fixes**, found by this entry's programs (#485, #486; `corpus/answers-two-types.bc`,
`corpus/loop-row-answer.bc`, and `corpus/reconcile-chain.bc` without its simplifications):

- A code that suspends at operations of different answer types was resumed at one layout type,
  which did not unify (#485). A program whose layout types fail is lowered again with the control
  operations' answers carried as variants, one per operation, as their payloads are
  (`Backend/Clos/Capture.lean`, `Ops.wrapsAnswers`; `Backend/Driver.lean`, `lowerEffects`): each
  operation's `κ` puts its answer in its variant, and a resumption point takes it out. A program
  that compiled before is lowered as before, with its counts.
- A resume code's cancel arm injected the cancel's `()` from one binder at every point, and the
  layout types key an injection's type by its payload's variable, so one point's injection took
  another's type and its padding (#486): each injection now copies the binder first, as does the
  resume arm's.

### Assurance

| extern | model | host implementation |
|---|---|---|
| `clock` | proved (7): a cell holding the time | a runtime cell; the time is the host's monotonic clock; assumed (1) |
| `clock_now`, `clock_sleep` | proved (7) | WASI `clock_time_get`, `poll_oneoff`; assumed (1): the real clock is not checked against the model |
| `args` | proved (7): a cell holding the arguments | a runtime cell over the arguments, read once; interpreter-checked (2) |
| `read_arg` | proved (7) | the arguments in memory (WASI `args_sizes_get`, `args_get`); interpreter-checked (2) |
| `mk_clock`, `take_clock`, `mk_args`, `take_args` | proved (7) | none: the model's harness |

`bcc trusted` lists the externs `main` reaches, now that a library brings in a platform's
externs the program may never use: an extern is in a program's trusted base when it occurs in
`main`'s erasure. `corpus/trusted/*.txt` pin the reports of six I/O programs, and
`scripts/check-corpus.sh` compares them.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/io-effects.bc` | the streams as effects: the whole input read, a report written by a function given `Stdout` by its row, a note on standard error | `lines 3`, `bytes 29`; `done` on standard error; `(i32[3], i32[29])` | `4 0 0` |
| `corpus/io-upper-effects.bc` | `io-upper` over the effects, at its counts | `io-upper`'s | `2 0 0` |
| `corpus/needs-stdout.bc` | helpers given standard output by their rows (moved from `pending/`, which waited on PR #100's `needs`) | `Hi`, `Hi`, `i32[6]` | `1 0 0` |
| `corpus/io-args.bc` | the arguments, one per line of `io-args.args`, an empty one among them | `1 alpha` … `4 δ`, `i32[4]` | `7 0 0` |
| `corpus/io-task.bc` | an async task writes to standard output across its `await`s, given `Stdout` by its spawn's borrow block | `<abc>`, `[3, 2]` | `29 7 0` |
| `corpus/reconcile-clock.bc` | the reconciler chain run once with the platform's clock and once with a fake clock swapped in by a handler | see the file | `34 8 0` |
| `corpus/io-laws.bc` | the laws, each under a fake handler | `hello, laws` twice, then the laws all hold | `11 0 0` |
| `corpus/answers-two-types.bc` | #485 | `(i32[201], i32[1])` | `1 2 0` |
| `corpus/loop-row-answer.bc` | #486 | `(i32[3], i32[33])` | `0 0 0` |

`corpus/reconcile-chain.bc` loses its simplifications around #485 and #486: its service is a
handler with a state, its clock's `sleep` answers the time slept, and its answer gains the service's
count of requests, `((((inr i32[408], i32[30]), i32[0]), [80, 80, 80, 4]), (((inl i32[200],
i32[20]), i32[1]), [20, 9]))`, at `28 3 0` (from `25 0 0`: the service's continuations, and the
calls of its answer, a function of its state). Rejected: `corpus/reject/io-unlisted.bc`. Pending:
`corpus/pending/io-two-tasks.bc`. Every program runs at the source stage, the closure and flat IRs
and WebAssembly with `live 0`; `reconcile-clock`'s real clock is compared, not printed, so its
answer is the same at every stage.

### Reports

`bcc check` reports each platform capability of `main`, `lowering L:C: main: `Stdout` is served by
the platform's `wasi_stdout` on the cell `stdout`, which each operation lends`, each operation on a
cell, `call L:C: print_byte (Stdout) → `wasi_stdout__print_byte`, on the cell `stdout` lent to it`,
a lent handler as `a direct call on the lent capability, its state lent to the clause`, and a
borrow block that gives its tasks capabilities, `borrow block: the tasks spawned in it are given the
capabilities of `Stdout`, lent for the block`. The system interface's, the platform's and the I/O
library's own declarations are not reported, however the program brings them in, and a library
function's copies are the library's for the loop reports. `corpus/reports/io-effects.txt`,
`io-task.txt` and `needs-stdout.txt` pin them.

### One-way doors

The IO model's user-visible shape and what `main` is given are not settled here: each is built as
proposed and listed with its options in #156.

- **What a program sees.** Per-stream answering effects with byte and view operations (built);
  one output effect with named instances for the two streams (§38 *Open*); or capability values
  only (§11), effects for tests alone.
- **What `main` is given.** Every interface effect its body performs, served ambiently (built); or
  a bundle record of capabilities `main` takes as a parameter (`docs/platform-design.md` §2.8);
  or effects named in `main`'s written row.
- **The arguments.** One byte stream, each argument followed by `0` (built); or a count and an
  indexed argument (`arg_count`, `arg_len`, `arg_into`).
- **Tasks and capabilities.** One task holds a capability, lent for the scope that bounds it
  (built); or the capability threaded through `await`, so that tasks share it.

**Decided by the user** (2026-10-16): the clock's time is **`i64` nanoseconds, monotonic**, since an
arbitrary fixed origin, saturating at `2^63 − 1`. A process such as the Kubernetes operator runs for
months, past the `2^31 − 1` milliseconds (about 24.8 days) of an `i32` clock. There is no
`Instant` type: a time and a duration are both `i64`.

### Baseline

No change to `CDerives`, the relation, the machine, `PinLaw`, the borrow rules, the Fundamental
Property or adequacy. `Opaque` gains `clock` and `args`, leaves with their models, and
`Core/Stdio.lean` their externs' models and proofs, so `fundamentalC`, `adequacyC`, `fundamentalD`,
`adequacyD` and §11's end-to-end theorems keep their statements and cover the new kinds. Every
existing corpus and kernel program keeps its output and counts but `reconcile-chain`'s (above); the
reports change only where a message changed (`corpus/reject/include-unknown.bc` lists `sys` and
`wasi`; `corpus/pending/effects-generic-store.bc` names the lent handler's form).

### Open

- **Concurrent writers.** Two tasks cannot both be given one capability. The options: thread the
  capability through `await` (the scheduler holds it between turns and gives it to the task it
  resumes, as a `for`'s site threads its variables, §15); serve a task's output at the scheduler (a
  port, decision 57); or a shared output capability, which needs interior mutability.
- Named instances (§38) for one output effect at two streams; redirecting a function's
  `Stdout` to standard error (an operation of an answering effect inside an answering clause, §18
  *Not provided*).
- A capability used by a computation parameter's argument under the callee's handler (#487): the
  reconcilers' services and journals are control effects because of it.
- Choosing the platform module at build time; `posix`.
- `Env`, `Fs`, `Net`, `Random`, the exit status (§11 *Designed, not built*). I/O errors (§11 *Open*).

---


## 35. Entry 34 — implicit allocations: frame slots, static cells, one box a node

### Motivation

A sweep of every heap allocation the source does not write (#500) found two kinds. Some are
pointless: a cell whose life the typing already scopes to one borrow, and the capability cells
every I/O program allocates. Others are needed but unstated: the boxes of recursive data, closures
on a type cycle, a buffer's growth, the heap driver's frames. The target is C's and Rust's: a
compiler temporary whose address is taken is a slot of its function's frame, a process-wide
object is static, and a tree allocates one object a node. This entry removes the pointless
allocations in the lowering and marks the rest. No allocator effect, arena or row is introduced
(those stay the eventual `Alloc` handlers).

### Language

No change: no type, rule, term, typing, elaboration or semantics. The kernel term of every program
is the one it was, and every program's output. Only the backend changes, below the model.

### Lowering

- **Scoped cells are frame slots.** Three elaborations allocate a cell for one borrow: the lend of
  a value to a call (`f(&x)`, `f(&mut x)`, `Frontend/Sugar.lean`, `lendBorrow`), `modify &mut x
  { … }` of a value (the same), and a handler's state given as a value (`with h(e) { … }`,
  `Frontend/Elab/Effects.lean`, `withBlk`). Each erases to `let (c, r) = withbor (alloc v) cb;
  b` with the owner `c` used once in `b`, by its `free`. The closure conversion recognises the
  shape (`Backend/Clos/Convert.lean`, `markScoped`: the borrow of a fresh cell, its owner freed
  through `let`s and no other `λ`) and marks the two as one scope (`scopedAlloc k`,
  `scopedFree k`), which every stage runs as `alloc` and `free`. When no resumption point of the
  code lies between them (`Backend/Clos/Capture.lean`, `crossedScopes`: a `perform`, an `await`
  or a call of a code that may suspend while the scope is open), the flat IR places the cell in a
  slot of the code's frame (`Backend/Flat/Lower.lean`, `frameScopes`; `Flat.Exp.slot`,
  `Stmt.unslot`, `Fn.frame`). The slot is no allocation and no live range. The Wasm module then
  has a stack of 1 MiB between the data and the heap, as clang and rustc lay out the shadow
  stack: `$sp` is lowered by a function's frame on entry, with a trap past the stack's end, and
  raised back before each return and tail call (`Backend/Wasm/Lower.lean`, `lowerFn`). A raise
  returns through the frame and drops the cell with it. LLVM's counterpart is an `alloca`.
- **A suspension inside a scope.** A code that may suspend is a state machine whose state holds
  the variables live at its resumption point, and whose resume code is a new call with a frame of
  its own (§19 *Lowering*); a slot open at the point would be held in the state past its frame.
  Such a scope keeps a heap cell (`Clos.Prog.suspendedScopes`). No program has one: the typing
  refuses a resuming operation across a borrow block's body (a continuation held across a lend is
  T1, #172), and a lend in the arguments of a function that threads a capability. A scope between
  two suspensions is framed in each code that runs it: `corpus/async-lend-slots.bc`.
- **Capability cells are static.** `stdin`, `stdout`, `stderr`, `args` and `clock` (§11, §34) are
  each a word of the program's data, after its literals (`Backend/Clos/Convert.lean`,
  `staticWord`; `Op.staticCell`): the prologue stores the descriptor there, and the epilogue's
  `free`, of an address below the heap, frees nothing.
- **One box a node.** A recursive type boxes the fields that close its cycles: the back edges of
  one depth-first search over the pair and sum fields (`Backend/Clos/Types.lean`). Where that
  boxes two fields or more of one cycle, a sum's payload is boxed instead when that boxes fewer
  (`sumBoxes`). A tree `μX. 1 + X ⊗ (A ⊗ X)` boxed its two children, two objects a node with the
  empty children's among them; it is now a tag and a pointer to an object holding the node, its
  children inline, so one object a node and none for an empty child, as Rust's
  `Option<Box<Node>>`. A linear shape (a list) boxes one field either way and keeps it at its
  recursive position, which pointer reversal reads (Backend README, *Stack*). Sum boxing keeps
  the tag word, where Rust uses the null pointer.
- **The arguments' memory is counted.** The runtime's one reservation of the arguments' memory at
  their first read (§34 *Lowering*) counts as one allocation in `$allocs`, at the flat IR and in
  Wasm alike; it is still no range and never freed.

### Implicit allocations that remain

Each is needed, and is now said where it arises:

| allocation | where it is said |
|---|---|
| a buffer's growth: `push`, `reserve`, `grow`, the string `push_*`, `to_string`, `string_of_lit` | `lib/buf.bc`, `lib/text.bc` (each function's comment) |
| the heap driver's frames, `with deep` | `lib/rec.bc` (`deep`'s comment) |
| a boxed field or payload of a recursive type | Backend README, *Representation* |
| a closure of a recursive closure type that captures | `bcc-counts --sites` (`recursive-types`); Backend README, *Representation* |
| a deep copy at a type holding recursive data | `clone`, written (§10); `bcc-counts` (`copies`) |
| the arguments' memory | `$allocs`, above |
| a scoped cell a suspension crosses | `bcc-counts --sites` (`scoped-cells … allocated`) |

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/async-lend-slots.bc` | lends of a `let mut`, a `modify` and a handler's state as a value in a task, between its `await`s: every scoped cell framed | `[45, 67]` | `22 6 0` |

Every count that changed is lower but one: `io-args` counts the arguments' memory (`7 0 0` before,
`6 0 0` now: two capability cells fewer and the reservation). `rec-tree` is `127 0 0` (from
`254`), `tree-map` `29 0 2` (from `58`), `rec-deep` `30040 0 0` (from `60040`); every I/O program
loses its capability cells; every program that lends a value loses its scoped cells. The counts
quoted in the tables of earlier entries are as of their versions; `corpus/counts.expected` has
the current ones.

### Baseline

No change to `CDerives`, the relation, the machine, `PinLaw`, the checker, the elaboration or a
kernel program (`corpus/kernel-counts.expected` unchanged). Every corpus program keeps its output.
The flat-IR interpreter checks every access to a frame slot against its scope and its call's frame
(each call has fresh frame addresses), as it checks every heap access against the live ranges, and
the falsifier passes on the corpus.

### Open

- A scoped cell a suspension crosses: its slot would live in the suspended state, which then
  needs a stable address (a pinned frame). Typing excludes it today.
- A sum's boxed payload with a null-pointer niche (the tag word dropped), as Rust's `Option<Box>`.
- An owned fold over a tree still recurses natively (Backend README, *Stack*).
- Placing the objects that remain by escape analysis (stack, frame arena or heap): the scoped
  cells are placed by the elaborator's scope, not by an analysis.

---

## 36. Entry 35 — `poly` families: one case per type; operators as families; the hash map

### Motivation

The generics design pass (#489) agreed three things this entry builds (#508). **One provider per
type**: every map or set at a key type uses the same equality and hash, so two of them agree and
an operation over both is coherent; a different hash function is a different type. **Operators
are a family chosen by type** (the user's decision of 2026-10-17), whose cases at the integer
widths are the machine instructions; a different arithmetic is a different type, not a scoped
handler. This replaces decision 54's `Num[T]` effect. **The map is a plain value**, a trial: it is
passed and handed back, `map_insert(&mut m, k, v)`, and `get` answers a view through the map lent
as a family, as `get` of `lib/slice.bc` does (no block form). The pending map programs of #490 and
the LeetCode corpus (#194, #201, #203) are the tests.

Everything here is elaboration and library code over existing core terms (§15's
monomorphization): no `CDerives` rule, relation clause, machine step, kernel type or checker change.

### `poly` families

**Declarations.** A family is declared by its signature, with one type parameter, the type its
case is chosen by, and no body:

    poly f[T]<'a, …>(x₁: A₁, …, xₙ: Aₙ) -> B

A case gives the body at a type `H`, its head, generic in its own type parameters `P, …` (each
named by `H`); `'h, …` are lifetimes `H` names. The family's parameters `x₁, …` are in scope in
`S`, at their types with `T := H`:

    poly f[P, …]<'h, …> at H = S

Each operator has a family, which the elaboration declares when a program gives the operator a
case; its parameters are `a` and `b`: `poly (+) at H = S`, and likewise `(-)`, `(*)`, `(==)`,
`(!=)`, `(<)`, `(<=)`, `(>)`, `(>=)`. Arithmetic is `(a: T, b: T) -> T`, a comparison
`(a: T, b: T) -> bool`. Internally the families are named `op_add`, `op_sub`, …; a program may not
declare one. The printed forms are `poly def f[T] : A = V` (the code `V` has the hole
`io_poly_body!` for its body) and `poly def f[P, …]<'h, …> at H = V`.

**Elaboration** (`Frontend/Sugar.lean`, `polyDecls`). A family is the template (§15) of its
signature, whose body is never elaborated. A case is the template `f__at{k}[T′, P, …]` of the
family's signature with `T` renamed `T′`, and body `S`. The families and cases of the program and
of every module it includes are collected before any declaration is elaborated (`PolyTab`), so
which case a call reaches does not depend on the order of declarations or of calls.

**The selection rule.** A call `f(W)` of a family, or `f[U](W)`:

1. **The type.** `T` is the written `U`, or else is read off the arguments by §15's first-order
   matching against the family's parameter types, in which `view 'a T` matches as `T` (an `i32`,
   a pair of them or a view is its own view, so `equal(x, y)` at such a type writes no `T`). What
   matching elaborated is elaborated again at the chosen case's instance.
2. **The candidates** are the cases whose head matches `T`: first-order matching with the case's
   type parameters as placeholders, a lifetime the head names matching any lifetime.
3. **The choice** is the candidate **at least as specific as every other**: its head is an
   instance of each other candidate's (matched by it). With none, the call is an error,
   "`f` has no case at `T`". Coherence (below) makes a choice exist whenever there is a candidate.
4. **The call** is a call of the chosen case's instance at `T` and the type arguments matching
   found, made and shared as a template's instance is (§15); every argument, its lifetimes and
   `unbang` are filled as for any call of that instance.

A family's lifetime parameter that its instance's type does not mention once elaborated (`'a` in
`view 'a T` at `T = i32`) is left out of the instance (`dropPhantoms`), and its other mentions in
the parameters' written types read `top`, on which `view 'a i32 = i32` does not depend. A
parameter the case's body names is kept. Otherwise a call in a function with no lifetime in scope
would have no lifetime to give it (§15).

**Coherence** (`polyCheck`), checked over every case of the program before anything is
elaborated, each an error at the case's declaration:

- **A second case at a type** — two cases of one family whose heads are equal up to renaming
  their type parameters — is "a second case of `f` at `H`, the first at `L:C`: a family has one
  case per type". It is never resolved by order (`corpus/reject/poly-second-case.bc`).
- **Two cases that overlap and neither is more specific** — heads with a common instance (found
  by unification, lifetimes ignored), neither an instance of the other — is "the cases of `f` at
  `H₁` and at `H₂` both apply at `U`, and neither is more specific" (`poly-overlap.bc`).
- A head names each of its case's type parameters; a head elaborates.
- **An operator's machine cases.** A case of an operator's family whose head has a common instance
  with an integer type (`i32`, `i64`, `u8`) is rejected (`poly-machine-case.bc`): those types have
  the host's instructions as their case.

So for every type there is at most one choice, and it is a function of the type: one provider per
type. A family's cases are global to the program: there are no modules (#63), and so no orphan
rule.

**What changes for existing programs: nothing.** No existing program declares a family. Templates
of one name declared by two modules (`map` of `lib/adapters.bc` and of `lib/iters.bc`) are not a
family and keep §15's rule, the first whose parameters the arguments match. The one corpus file
whose text changes is `corpus/reject/include-unknown.bc`, whose expected message lists the library
modules, two more now.

### Operators

`a + b` (and every operator of §15) at operands of an integer type is the host's instruction at
that width, as before: every existing program elaborates to the same code. At operands of another
type `T` — the type of an operand that is not a literal — it is the call `op_add[T](a, b)` of the
operator's family when the program gives a case that `T` selects; otherwise it is elaborated as
before (and fails to type, as it did). So `poly (+) at Complex = …` makes `a + b` work at
`Complex`, in generic code too: `dot[T]` of `corpus/poly-operators.bc` multiplies and adds at its
type parameter, its instance at `i32` with the instructions and at `Complex` with the cases.

A different arithmetic is a different type. There are no `data` declarations (§31 *Open*), so a
case is at a structural type: `type Complex = i32 * i32` gives the case at `i32 * i32`, which every
pair of `i32`s then has.

**`==` and `equal` are distinct.** The operators' families are not the providers' below. A type
may have `(==)` and no `equal` case, or the other way round. The float widths (#499) are meant to
get the host's comparisons as machine cases of the operators' families and no case of `equal`,
`hash` or `order`: `x == y` compares floats, and a map keyed by a float is rejected at its use
(`equal` has no case at `f64`), which is expressible because the two are distinct families.

### The providers: `lib/key.bc`

    poly equal[T]<'a, 'b>(x: view 'a T, y: view 'b T) -> bool
    poly hash[T]<'a>(x: view 'a T) -> i64
    poly order[T]<'a, 'b>(x: view 'a T, y: view 'b T) -> i32        -- -1, 0 or 1

Each takes its operands as views (§1's `Imm̲`): a map reads a key it stores in place, through the
`withload` of its slot, so a key need not be persistent, and a key that is its own view (an
integer, a pair of them, `text 't`) is passed as it is. A buffer's view is its array's view and
its length.

| head | `equal` | `hash` | `order` |
|---|---|---|---|
| `i32`, `i64`, `u8` | `==` | the word, one step | signed; bytes unsigned |
| `1` | true | 0 | 0 |
| `A * B` | both components | the two hashes combined | lexicographic |
| `A + B` | the same side, then its payload | the side's tag and the payload | `inl` before `inr` |
| `array_imm 'h A`, `array A` | the lengths, then each element | the length, then each element | lexicographic |
| `buf A` | the initialised prefixes | the prefix | the prefixes, lexicographic |

`bool` (`1 + 1`), `text 't` (`array_imm 't u8`) and `string` (`buf u8`) are covered. `buf A` is
`array A * i32`, which `A * B` also matches; the buffer's case is the more specific, so a buffer
is compared by its contents and not its capacity (`corpus/poly-providers.bc`). An element is read
through `borrow imm *p` (below). The hash is FxHash's step over 64-bit words: deterministic on
every run and every engine, so a map's order of iteration is reproducible.

**No case** at a function (`!`, `U`), a cell, a borrow (other than through a view), an opaque host
type, or a recursive type (`μ`): a case at a recursive type would call its own instance, a
recursion the effects elaboration groups by name before types (§31's D1), which is not provided.

**Laws** (stated; checked by the corpus programs, not proved): over runs that finish, `equal` is
an equivalence, `equal(x, y)` implies `hash(x) = hash(y)`, and `order` is an order in which every
two values are comparable, with `equal` as its equivalence. The cases above are structural, so the
laws hold by construction from the integers' cases. A user's case is that type's own
correctness, like any function. Integer laws need the host's (decision 10).

### Elaboration that the map uses

Each elaborates into existing core terms:

- **A load through a borrow**, `borrow imm *g { 'y, v -> S }`, `g : imm 'a A`, is
  `withload['a, 'y, A, B] g (Fun 'y < dom. fun (v : view 'y A) -> S)`, `B` free of `'y`; the
  block's value is `((), B)`, nothing handed back. It reads any content, where `*g` copies a
  persistent one.
- **A record lent fieldwise**, `borrow imm r { 'x, v -> S }` at a place whose type is a tree of
  `⊗` of owned arrays and persistent values (at least one array; a buffer `array A * i32` keeps
  §17's form, its prefix): each array is lent by its own `slice_borrow_imm` (§9), nested left to
  right, the last at `'x` and the others at lifetimes `'x_0`, … of their own; the persistent fields
  are as they are; `v` is the record of the families and fields, and the record is rebuilt from
  what the borrows hand back. The result may name none of the lifetimes. Two families at one
  lifetime would need a family to be shortened (`[Imm 'k A] ⊑ [Imm 'x A]`), a kernel constant this
  entry does not add, so a view of such a record carries a lifetime per array. `imm` only, and not
  at a body that performs an operation.
- **A lend to a function with several lifetime parameters**, `f(&k, …)` at a parameter `imm 'q A`
  or `mut 'q A` (or a family's): the lent parameter's lifetime is the lend's own, and the others
  are applied inside it at the lifetimes the call gives them (§15). Before, a lend needed the
  callee to have one lifetime parameter.
- **The type of a place lent at a parameter of its own type** (`map_lookup(&m, k)`, which moves
  `m` in and hands it back, §15) is matched against that parameter, so `m`'s type gives `K` and
  `V`.
- An operator's operands are typed with the instances made so far in scope (`hash(a) == hash(b)`
  at `i64`).

### The map and set: `lib/map.bc`

    type Map[K, V] = (array (1 + (i32 * K)) * array V) * i32
    type MapRef[K, V]<'k, 'x> = (array_imm 'k (1 + (i32 * K)) * array_imm 'x V) * i32
    type Set[K] = Map[K, 1]

| function | type | |
|---|---|---|
| `map_new[K, V](cap)` | `Map[K, V]` | room for `cap` entries before it grows |
| `map_insert(&mut m, k, v)` | `V + 1` | the value displaced; a key already present keeps its first key |
| `map_lookup(&m, k)` | `V + 1` | a copy of the value (`V` persistent) |
| `map_contains(&m, k)` | `bool` | |
| `map_remove(&mut m, k)` | `V + 1` | the value taken out |
| `map_len(&m)` | `i32` | |
| `map_get(r, k)` | `imm 'x V + 1` | a view of the value, `r : MapRef[K, V]<'k, 'x>` |
| `map_iter(r)` | `sized … (K * imm 'x V)` | every entry in slot order, the key copied out of its slot (a key that is its own view) |
| `map_size(r)` | `i32` | |
| `set_new[K](cap)`, `set_insert(&mut s, k)`, `set_contains(&s, k)`, `set_remove(&mut s, k)`, `set_len(&s)` | | `set_insert` answers whether `k` was new |

`r` is the map lent as a family, `borrow imm m { 'x, r -> … }` (above); while it is lent the map
cannot change, so no view outlives a growth (linearity, as §17's *No view across growth*).

**The table.** Open addressing with linear probing over a power-of-two table at most half full,
grown by doubling; each slot holds `inl ()` or `inr (h, k)`, the key with its slot hash, and the
value at the same index, the filler of `V` where there is no entry (so `V` has a filler: integers,
views, arrays, buffers, and pairs and sums of them). Removal shifts the entries after the hole
back over it, each whose probe sequence passes it (Knuth's algorithm R), so a search never meets a
tombstone. A probe compares slot hashes, then `equal` on the two keys' views. Every loop is
counted by the table's size; a search ends at an empty slot, which a half-full table has.

**Keys and values.** A key sought is given by value and dropped after the search: it is lent to
the search, a cell of the caller's frame (§35). A key may be a view (`text 't`): the map's type
then mentions `'t`, and the map cannot outlive what its keys borrow. A linear `K` or `V` makes the
map linear: it has a destructor exactly when its keys and values do (§12). A replaced key is
dropped, so `K` has a destructor or is persistent.

**Generic `data`.** `Map`, `MapRef` and `Set` are generic `type` abbreviations, transparent: there
are no `data` declarations (§31 *Open*), so the representation is not hidden outside the module.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/poly-operators.bc` | `(+)`, `(*)`, `(==)` at `Complex`; a generic `dot` at `i32` (the instructions) and at `Complex` (the cases) | `(32, ((-9, 12), true))` | `0 0 0` |
| `corpus/poly-providers.bc` | `equal`, `hash` and `order` at strings of two capacities, views, sums; specificity of `buf A` over `A * B`; a family of the program's | `(111, (7, -1))` | `2 0 0` |
| `corpus/map-views.bc` | views of buffer values, two at once, read through `borrow imm *v`; `map_iter`; 200 colliding keys, every third removed | `(106, (52, (133, 13267)))` | `24 0 0` |
| `corpus/aoc/2024-01.bc`, `2024-11.bc`, `2022-21.bc` | #490's map days: counts, interning to indices, keys that are views of the input | the Rust answers | `5 0 0`, `271 0 0`, `12 0 0` |
| `corpus/leetcode/arrays/0001-two-sum.bc`, `0217-contains-duplicate.bc`, `strings/0049-group-anagrams.bc`, `graphs/0128-longest-consecutive-sequence.bc`, `heaps/0347-top-k-frequent-elements.bc` | a map, a set, `string` keys, `map_iter` | as their headers | `19`, `13`, `70`, `15`, `31` allocations, no indirect call or copy |

`corpus/aoc/2024-11.bc` is `-- check: no-source`: the source interpreter takes about half an
hour over it, and its golden is that interpreter's output, written once from it.

Rejected: `corpus/reject/poly-second-case.bc`, `poly-overlap.bc`, `poly-machine-case.bc`,
`poly-no-case.bc` (`equal` at a function). Still pending: `corpus/pending/aoc-2020-07.bc`, behind
#491 and #492 (with both written around, its map gives the Rust answers);
`lc-0070-climbing-stairs-memo.bc`, behind the `memo` layer (an effect with type parameters).

Each program edited from its pending form keeps its algorithm: `include map`, and `map_get(&m, k)`
read `map_lookup(&m, k)`, the copy; `0347` visits its entries with the map lent (`map_iter(r)`), and
`0049` makes a new group's key again for its insertion, since the lookup drops the key it is given.

### Baseline

No change to `CDerives`, the relation, the machine, `PinLaw`, the checker or the backend, and no
kernel program changes (`corpus/kernel-counts.expected` unchanged). `fundamentalC`, `adequacyC`,
`fundamentalD` and `adequacyD` keep their statements and cover every elaborated program. Every
existing corpus program keeps its output, golden and counts.

### Not provided

- **The bounds layer** (`ability Key[K] { poly eq[K]; poly hash[K] }`, `gives`, `given`; spelling
  provisional): bounds checked at the call, grouping, associated types. A later unit (#489). A
  type with no case is an error at the instance, inside the library.
- **A hasher type parameter** (`HashMap[K, V, S]`): there are no defaulted type parameters. A
  seeded (keyed) hash, and `entry`.
- **`data` declarations** and so newtypes and a hidden representation (§31 *Open*).
- **A lookup by a key at another lifetime than the map's** (Rust's `Borrow`, a literal against
  `Map[text 't, …]`), and a one-lifetime `MapRef`: both need a family shortened, a kernel constant.
- **A key lent to a lookup** (`map_lookup(&m, &k)`): a call lends one place. The key is given by
  value.
- **Cases at recursive types** (a list's equality): see above.
- **`borrow mut` of a map as a family** (`get_mut`), and a fieldwise `mut` lend.
- **`map_iter` at a key that is not its own view** (`string`): the key is copied out of its slot.
- **`!=` from `==`**, or any family's case derived from another's.
- Swiss tables and other performance work; laws proved in Lean.

### Open

- Whether the plain-value map stays (the trial; an instanced effect `with m { … }` is the other
  form, #489).
- Module-qualified families and an orphan rule, once there are modules (#63).
- `T` read off arguments whose view is not themselves (a buffer's view): the call writes `T`.
## 37. Entry 36 — floats: `f32` and `f64`

### Motivation

Programs compute with real numbers: a median, a mean, a distance. The LeetCode corpus computed
twice a median as an integer and printed `.5` by hand (#498). This entry adds IEEE 754 binary32
and binary64 by §8's scheme (#499): two more widths of `VTy.int`, literals, and the float
operations as host operations.

### Types and literals

    A ::= … | F32 | F64                                   (VTy.int .f32, VTy.int .f64)

`Width` gains `f32` and `f64`, and `IntLit` gains `f32 n` and `f64 n`, a float given by its bit
pattern `n` (`UInt32`, `UInt64`). Nothing else in the kernel changes: the relation at `int w`
holds exactly at a literal of width `w` and the empty resource (`Val.IsInt`), so the floats are
persistent, `Imm̲ 'b F = F`, they outlive every lifetime, and every theorem stated for the widths
holds for them unchanged. A float holds no resource.

The core syntax writes `f32[n]` and `f64[n]` (`n` the bits). The surface writes a decimal,
`1.5`, `2.5e-3`, `1e10` (a fraction or an exponent makes it a float), read as the float nearest
its value, ties to even (`Frontend/FloatLit.lean`, exact arithmetic): an `f64` unless an `f32`
is expected. An integer literal where a float is expected is that integer as a float.

### Operations

The language's float operations (`Support/Syntax/Integers.lean`), at each float width `f`, on the
floats' bits, as `wasmHost` computes them (`Support/Dynamics/Floats.lean`): IEEE 754 binary32 and
binary64, round to nearest even, each operation named as the Wasm instruction that computes it.
As at §8, Wasm and native code are implementations of this section.

| group | operations | type (at `F64`) |
|---|---|---|
| binary | `fbin f o`: `add`, `sub`, `mul`, `div`, `min`, `max`, `copysign` | `F64 ⊗ F64 ⇒ F64` |
| unary | `fun1 f o`: `abs`, `neg`, `sqrt`, `ceil`, `floor`, `trunc`, `nearest` | `F64 ⇒ F64` |
| tests | `frel f o`: `eq`, `ne`, `lt`, `gt`, `le`, `ge` | `F64 ⊗ F64 ⇒ 1 ⊕ 1` |
| to a float | `convert f i sx` (`f64.convert_i32_s`, …), `demote`, `promote` | `I32 ⇒ F64`, `F64 ⇒ F32`, `F32 ⇒ F64` |
| to an integer, partial | `trunc i f sx` (`i32.trunc_f64_s`, …) | `F64 ⇒ I32 ⊕ 1` |
| to an integer, total | `trunc_sat i f sx` (`i32.trunc_sat_f64_s`, …) | `F64 ⇒ I32` |
| bits | `reinterpret_i f`, `reinterpret_f f` | `F64 ⇒ I64`, `I64 ⇒ F64` |

`trunc` returns a sum where it has no answer (a NaN, an infinity, an integer part out of range), as
the integer division does (§8): a trap would abandon linear resources. `trunc_sat` is total: `0`
at a NaN, the least or greatest integer out of range. `min` and `max` answer a NaN when either
operand is one and order `-0.0` below `0.0`; `nearest` rounds to the nearest integer, ties to
even. `§8`'s grouped integer operations at a
float width take `0`, as at `w8`. `host[op]` names a float operation as its Wasm instruction with
`_` for `.`: `host[f64_add]`, `host[f32_sqrt]`, `host[f64_lt]`, `host[f64_convert_i32_s]`,
`host[i32_trunc_f64_s]`, `host[i64_trunc_sat_f32_u]`, `host[f32_demote_f64]`,
`host[i64_reinterpret_f64]`, `host[f64_reinterpret_i64]`.

A host `ℍ` gains a function per group, on the floats' bits (`Host.fbin`, `fun1`, `frel`,
`convert`, `trunc`, `truncSat`, `demote`, `promote`); `reinterpret` keeps the bits and is fixed in
`Host.call`. `host_call_sound` covers the new operations at every host, from the construction of
`Host.call` alone: nothing about float arithmetic is proved, as nothing about integer arithmetic
is (§8).

### NaN: sign and payload unspecified

*Amended in 0.70 (decision 66, #528). Through 0.69 every engine made each NaN these operations
answer the canonical one; this rule replaces that one.*

Every float result is fixed but one: **the sign and payload of a NaN that `add`, `sub`, `mul`,
`div`, `min`, `max`, `sqrt`, `ceil`, `floor`, `trunc`, `nearest`, `demote` or `promote` answers
are unspecified.** The result is a NaN exactly where IEEE 754 answers one; which NaN is the
engine's choice, as in Rust (RFC 3514) and in Wasm. `abs`, `neg`, `copysign` and `reinterpret` act
on the bits and keep a NaN's sign and payload, so a NaN given by its bits (`of_bits_f64`) is that
NaN everywhere. The choice is observed only by `reinterpret` and by `copysign`'s sign operand,
which a NaN may reach through `abs`, `neg` and `copysign` (and `total_cmp_*`, `ord_*` through
`reinterpret`); the comparisons, `trunc`, `trunc_sat` and the printer, which prints every NaN as
`NaN`, do not observe it.

The engines do not canonicalise. x86 generates a negative NaN, ARM a positive one, and both
propagate an operand's payload; the compiled code is the hardware's float instruction alone.

**What the semantics is.** `Host.Conforms ℍ` (`Support/Dynamics/Host.lean`): `ℍ` is `wasmHost` at
every operation, except that at each of the thirteen operations above its answer and
`wasmHost`'s are equal or both NaNs (`PrimF.NaNEq`), and at `copysign`, `abs` and `neg` equal. A
resolution `r` of those NaNs (a NaN at each width) gives the host `wasmHostAt r`, and
`wasmHostAt_conforms` proves every such host conforms. `wasmHost`, the Lean host the interpreters
and goldens use, resolves every such NaN to the canonical one (`0x7FC00000`,
`0x7FF8000000000000`): one allowed choice (`wasmHost_conforms`), kept because it makes the
reference output independent of the machine Lean runs on.

**What the proofs cover.** Every theorem over the machine (the Fundamental Property, adequacy,
`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD` and §13's safety) is stated for every
host `ℍ`, so it holds at every conforming host, with no statement changed. Exactly:

- An engine whose NaN choice is a function of the operation and its operands' bits (the hardware
  of x86 and ARM, wasmtime on either) is the machine at one conforming host, and every theorem
  holds of its runs as of the reference's.
- **Not proved:** that a program which does not observe a NaN's bits prints the same at every
  conforming host. It is tested: the closure-IR interpreter runs at `wasmHostAt .negative` (the
  canonical NaN with its sign set), the flat-IR interpreter at `wasmHostAt .payload` (payload
  `1`), and Wasm at its hardware's choice, and each must print every corpus golden, which the
  source interpreter writes at `wasmHost` (*Engines*, below). A program whose output depends on
  the choice fails there. That noninterference theorem is *Open*.
- **Not covered:** an engine whose choice is not a function of the operation and operands, as
  when an optimiser folds one occurrence of `0.0 / 0.0` and the hardware computes another. No one
  host is that run, so no theorem here is about it (*Open*).

**Engines.** The source interpreter and the falsifier apply `wasmHost`; the closure-IR and
flat-IR interpreters `wasmHostAt .negative` and `wasmHostAt .payload`; the Wasm stage runs
wasmtime's instructions, which do not canonicalise (Wasm allows any NaN there, as this section
does). Goldens print floats through the printer and bits through `reinterpret`; no corpus program
prints the bits, sign or `totalOrder` position of an arithmetic NaN (`float-compare.bc` takes its
NaN by its bits; `float-ordered.bc` sorts `0.0 / 0.0` and its negation, which print `NaN` at both
ends whichever sign the first has).

`wasmHost`'s float operations are Lean's `Float32`/`Float` (IEEE 754, round to nearest even),
with each NaN result resolved and `min`, `max`, `nearest` and the conversions written to their
definitions above (`Support/Dynamics/Floats.lean`).

### Lowering

A float is one word holding its bits, an `f32`'s zero-extended, as an `i32`'s (Backend README,
*Representation*): no new local type, and `reinterpret` is the word itself. A float operation
reinterprets each operand as `f32`/`f64` as it is pushed and its result back to an integer
(`Backend/Wasm/Lower.lean`, `floatIn`, `floatOut`), so the module uses Wasm's `f32`/`f64`
instructions. `trunc` is lowered as its range test (two float comparisons against the bounds of
Wasm's range, false at a NaN) and `trunc_sat` inside it, so the compiled code never traps. Printed,
a float value is `f32[n]`/`f64[n]`, its bits, as an integer prints its bits (`Backend/Value.lean`).

### Surface

The operators `+ - * /` and `== != < <= > >=` at a float type are the float operation and IEEE
754's comparison, by §8's per-width dispatch (`SurfOp.host`): the width is the one expected of
an arithmetic result, or an operand's other than a literal's, and `f64` when both operands are
literals and one is a float literal. `/` at an integer is §39's, which raises where the
division has no answer. There is no unary minus: `neg_f64(x)` (`0.0 - x` is `+0.0` at
`x = 0.0`).

### Equality and order

`==`, `<` and the rest are IEEE 754's comparisons, returning `bool`: a NaN is unordered (every
comparison with it is false but `!=`, so `x != x` exactly at a NaN), and `-0.0 == 0.0`. They are
neither an equivalence nor a total order, so, as in Rust (`PartialEq`/`PartialOrd`, no `Eq`,
`Hash`, `Ord`), **a float has no equality, hash or order provider**: under one provider per type
(#489, #508) it has none, it is not a map key, and it is not sortable by default. The comparison
operators are host operations at the float widths, separate from any provider, so a provider's
cases need no float case.

Where an order is needed (`lib/float.bc`):

- `total_cmp_f64`, `total_cmp_f32`: IEEE 754's `totalOrder`, −NaN < −inf < … < −0.0 < 0.0 < … <
  inf < NaN, NaNs by their payloads; a comparison for `sort`.
- the `OrderedFloat` pattern: `ord_f64` maps a float to the `i64` whose signed order is
  `totalOrder` (the bits, with the magnitude flipped when the sign is set), a bijection with
  inverse `of_ord_f64`. A map keyed by `ord_f64(x)` or a sort of the keys uses the integer's
  equality, hash and order, which are the float's under `totalOrder`: `-0.0` and `0.0` are two
  keys, and a NaN equals itself. Once a generic `data` newtype lands (#508), `data OrdF64(i64)`
  is this with its own name.

### Library

`lib/float.bc` (`include float`):

- the operations by name at each width (`sqrt_f64`, `abs_f64`, `neg_f64`, `floor_f64`,
  `ceil_f64`, `trunc_f64`, `round_f64` (Wasm's `nearest`, ties to even), `min_f64`, `max_f64`,
  `copysign_f64`, `is_nan_f64`, and the same at `f32`);
- conversions: `f64_of_i32`, `f64_of_i64`, `f32_of_i32`, `f32_of_i64`; `i32_of_f64`, `i64_of_f64`
  (partial, `I ⊕ 1`) and `i32_of_f64_sat`, `i64_of_f64_sat`, and at `f32`; `f64_of_f32`,
  `f32_of_f64`; `bits_f64`, `of_bits_f64`, `bits_f32`, `of_bits_f32`;
- `total_cmp_*`, `ord_*`, `of_ord_*`, above;
- printing and parsing: `push_f64`, `push_f32` (onto a string), `print_f64`, `print_f32` (to
  standard output), `parse_f64`, `parse_f32` (raising `FloatParseError`, `1 + u8`: the text ends
  where a digit is needed, or the byte that cannot stand where it is), and the same on bit
  patterns (`push_f64_bits`, `parse_f64_bits`, …).

**Printing** is the shortest decimal that reads back as the same float, and of those the nearest
(the property of Steele and White's, Burger and Dybvig's, Grisu's and Ryū's output). It is
Burger and Dybvig's free-format algorithm on exact big integers (`Big`, a buffer of 32-bit limbs
in `i64`s, as long as its number): the value and its rounding interval scaled by a power of ten,
a digit per step until the rest lies in the interval, which is closed when the significand is
even, and the nearer of the last digit and its successor, the even one at a tie. It is spelled
as Rust's `{:?}`: `NaN` (every NaN), `inf`, `-inf`, `0.0`, `-0.0`; with `e` the decimal exponent
of `d.ddd × 10^e`, a decimal with at least one fractional digit when `-4 ≤ e < 16` (`1.0`,
`0.0001`, `1000000000000000.0`), else `d.ddde<e>` (`1e16`, `1.5e-7`, `5e-324`,
`3.4028235e38`).

**Parsing** reads `[+-]? (digits [. digits*] | . digits) ([eE] [+-]? digits)?`, or `inf`,
`infinity` or `nan` in any case, as the float nearest the decimal, ties to even, overflowing to
an infinity and underflowing through the subnormals to zero. It keeps the first 800 significant
digits and whether any later digit is nonzero (a point halfway between two floats has at most 767
significant digits), divides exactly, one bit at a time, and rounds once; an `f32` is rounded from
the decimal directly, never through `f64`. Every loop is counted, so both are total.

Both allocate (the string, the big integers), where Rust's printer allocates nothing: correctness
first.

### Programs

Each runs at every stage with one output (source, closure IR, flat IR, Wasm), and passes the
falsifier.

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/float-arith.bc` | arithmetic, `sqrt`, overflow, `0 / 0`, subnormals, `-0.0`, the rounding functions (`nearest` ties to even), `f32` arithmetic; shortest printing | `0.30000000000000004`, …, `1e-45`; `19` | `312 0 0` |
| `corpus/float-compare.bc` | IEEE 754 comparisons at NaN, `-0.0`, the infinities; `total_cmp_f64`; `min`/`max` of the zeros; a NaN given by its bits | six lines of comparisons, `9221120237041090560`; `6` | `0 0 0` |
| `corpus/float-convert.bc` | `trunc` partial and `trunc_sat` at `i32`, unsigned `i32` and `i64` at every range boundary, `inf`, NaN; integer to float rounding; demote and promote | thirteen lines, then `9007199254740992.0 16777216.0 4294967300.0 0.1 0.10000000149011612`; `13` | `183 0 0` |
| `corpus/float-ordered.bc` | sorting by `total_cmp_f64`; the `OrderedFloat` key `ord_f64`, sorted and deduplicated as `i64`s | `NaN -inf -0.0 0.0 0.0 1.0 2.0 3.5 NaN`, the eight distinct keys; `8` | `81 0 0` |
| `corpus/float-roundtrip.bc` | 38 floats printed and read back, 23 decimals read (halfway cases, long inputs, overflow, underflow, malformed text), at both widths, against Python's references | every check `=`; `61` | `3721 0 0` |
| `corpus/leetcode/heaps/0295-find-median-from-data-stream-f64.bc` | LeetCode 295 with the median an `f64` (the integer program, `…-stream.bc`, unchanged) | `1.5 2.0`, …; `24` | `281 0 0` |

Each program prints through one call of the printer per width: the backend compiles every call
of a function as a copy of its body, so each call of `print_f64` is a copy of the printer and
its big-integer library (#509).

### Baseline

The Fundamental Property and adequacy hold unchanged: `CDerives.lit` and `CDerives.hostOp` are the
rules they were, at more literals and operations, and `host_call_sound` covers the new operations
at every host. No new rule, index or former. Every existing corpus and kernel program keeps its
output, goldens, `corpus/kernel-counts.expected` and counts. The lexer reads `n.i`, an operation
of a row, as a float literal's text, and the parser reads it back (`nDotI?`), so every row is read
as before.

### Not provided

- A unary minus, and float literals written negative: `neg_f64`.
- An equality, hash or order provider at a float type: the classical default, as in Rust (above).
- Formatting options (a fixed number of digits, padding): only the shortest round-trip form.
- Floats as `withborS` leaves (`plainV`, as the integers, §8 *Open*).

### Open

- Rounding modes other than nearest-even, and floating-point exceptions: Wasm has neither.
- **NaN noninterference**: a program in which no NaN that an arithmetic operation answered
  (directly or through `abs`, `neg`, `copysign`) reaches `reinterpret` or `copysign`'s sign
  operand prints the same at every conforming host. Tested (*NaN*, *Engines*), not proved; it
  needs a relation between two runs at two hosts.
- **A machine at a host relation**: an engine whose NaN choice varies between two applications of
  one operation to the same operands (an optimiser's constant folding, LLVM's NaN semantics) is
  not the machine at one host. Covering it needs the host step to be a relation, `ℍ.call op v r`,
  with the theorems restated over it (#529's native backend is such an engine).
- SIMD (`v128`) and fused multiply-add, which Wasm's scalar core lacks.
- Faster, allocation-free shortest printing (Ryū or Schubfach tables) in place of the exact
  big-integer one, and parsing by Eisel–Lemire with this one as its fallback.
- Each call of the printer is compiled as a copy of it (#509); the programs call it once.

---

## 38. Entry 37 — instances of an effect: rows with types, names, abstraction safety

### Motivation

The kernel tells two handlers of one effect apart: a row is keyed by handler site and operation
(§19 *Names*), and `Row.uniqB` forbids only one site's operation twice. §18's surface did not.
Rows were inferred on the untyped program, before the types that tell `Fail[i32]` from
`Fail[ParseError]` are known (#516), so a row held one instance per effect, a second one was
dropped, and an operation went to the innermost handler of its *effect*. Programs worked around
it: `Stdout` and `Stderr` are two effects (§34), `parse_i32` maps its arithmetic's errors into its
own (`lib/text.bc`), and §18 *Not provided* listed a second instance in a row and two sites in a
counted loop's body. This entry makes the surface keep what the kernel has (#519, #155, #516):
instances, resolution by instance, names, and the rule that keeps a generic body's meaning.

### Instances and rows

An **instance** is an effect at its type arguments: `Fail[i32]` and `Fail[ParseError]` are two.
Two type argument lists are one instance's when they are equal as types (abbreviations expanded,
`Env.sameArgs`). A function's **row** is a list of **entries**, one per instance it performs, each
with its name when the row names it: `fn sync(k: i32) -> i32 with src: Kube, dst: Kube`.

**Rows are inferred with types.** The type arguments of an operation's instance are read off its
argument's type, by matching the operation's parameter types against it; those of a call of a
template are written, `f[T](…)`, or matched from its parameter's type against its argument's
(decision 45's matching). Both are read before the operations are resolved, by the typed
elaboration's own inference (`TCx.tyV`, `Elab.inferV`) and matching (`Frontend/Elab/Match.lean`)
over each declaration's body, at the declaration's own types: its type parameters are
placeholders (`Frontend/Elab/Instances.lean`). What inference cannot synthesize is not known: a
literal (whose width its context decides), an injection, a local of unknown type. `(e : T)`
ascribes it.

- **A written row** is a promise, as in §18: each instance the body performs is the entry named as
  it is, when it is named; else the entry of its type arguments; else the only entry of its
  effect. Two entries that could be it, neither the one unnamed, are ambiguous, and an error asks
  for an ascription or a name. A row that lists one instance twice names the two entries.
- **With no written row**, an instance whose type arguments are not known is the one entry of its
  effect (and name) whose are; with none they are not determined (§18's error); with two, it is
  ambiguous.

### Resolution

- **By instance.** `op(v)` goes to the innermost handler in scope of its instance. When its type
  arguments are not known, or no handler in scope has them, it goes to the innermost handler of
  its effect if every handler of the effect in scope is one instance (§18's rule, unchanged for a
  program with one instance in scope); otherwise it is an error that asks for an ascription or a
  name.
- **Names** (spellings provisional). `with n = h(…) { M }` names the handler `n`; `n.op(v)` performs
  `op` at the innermost handler named `n`. An entry of a row named `src` is served, at a call, by
  the innermost handler named `src` of its instance, and an unnamed entry by the innermost handler
  of its instance, named or not. So an unnamed `with` handles the unnamed instances of its effect,
  and a named one those and the ones of its name: an operation named for an outer handler passes
  the inner ones.
- **A copy's entries are unordered.** A function is elaborated once per assignment of its entries
  to what serves them (§18): in its copy, the entries of its row are its handlers, with no nesting
  between them. Of two entries that could serve an operation, the one unnamed is chosen if it is
  the only one, and otherwise it is ambiguous. A `with` inside the body is innermost, as anywhere.
- **The instance a `with` handles** is at its written type arguments; else at those of the one
  instance of its effect its body performs (unnamed, or named as the handler); a body that performs
  two asks for them. The handler's own row (`with E₂[…]`) is served by the innermost handlers of
  its instances around the `with`, and its clauses see them as its row's entries, at the
  handler's own types.

### Abstraction safety

A generic body does not change meaning when its type arguments coincide with another instance it
performs (Zhang and Myers, *Abstraction-safe effect handlers via tunneling*, POPL 2019). In
`f[E]` with the row `Fail[E], Fail[ParseError]`, instantiating `E := ParseError` must not merge
the two or reroute a `raise`; and in `g[E]` that handles its own `Fail[E]` around a call that
raises `Fail[ParseError]`, the handler must not catch that raise at `E := ParseError`.

**The rule.** The entries of a written or inferred row are distinct slots; an operation resolves
to a slot at the template's types; instantiation never merges slots.

**Why it holds.** Resolution runs on the template: the effects pass elaborates a function's copy
with its type parameters as placeholders, and the table of type arguments is read at them
(`Instances.table`). Decision 45 makes each instance from that copy by substituting types: the
static names of its sites and operations are fixed, so instantiation reaches the types of a
site (`HInfo.subst`, `Frontend/Elab/Subst.lean`) and never which site an operation names. A
handler type parameter that a site leaves open is named apart from the template's
(`withCtl`), so the substitution cannot capture it. Two slots that coincide at an instance are two
entries served by one site: the copy's row lists the site once (`Env.rowOf`), and both entries'
operations go to it, as the caller's handler of that instance.

**Prior art.** Zhang and Myers make handlers abstraction-safe by tunneling: an effect not named in
a function's signature passes the handlers inside it, which is this rule's effect for a slot.
Helium (Biernacki, Piróg, Polesiuk and Sieczkowski, *Binders by day, labels by night*, POPL 2020)
resolves lexically, with named instances and a name required only where two instances are in
scope. Effekt (Brachthäuser, Schuster and Ostermann, *Effects as capabilities*, OOPSLA 2020)
passes capabilities lexically, the implicit form of §18's capability per handler.

`corpus/effects-abstraction.bc` runs both programs above at `E := ParseError`.

### Several sites

- **In a counted loop's body** (§16): the step handles the abortive operations of every site the
  body performs, each site's handler around the previous one at the row of the ones around it, each
  operation leaving the loop by its exit; after the loop each is performed again at its site
  (`forData`, `Frontend/Sugar.lean`).
- **A resuming handler with a state** (§19 *Handler state*): its clauses answer a function of the
  state, which runs where the `with` is, and which resumes or cancels the continuation there. The
  continuation is at the row of the `with` (`[handle]`), so the function's row is the handler's
  own row and every other site in scope, not the handler's row alone (#514).

### Elaboration

| where | what |
|---|---|
| `Frontend/Elab/Instances.lean` | the table of type arguments, per declaration and call |
| `Frontend/Elab/Match.lean` | the typed elaboration's matching, moved out of `Frontend/Sugar.lean` |
| `Frontend/Elab/Effects.lean` | entries (`Env.addInst`, `Env.withoutInst`, `Env.handledArgs`), resolution (`Cx.serve`, `Cx.capFor`, `Cx.capAt`), a copy's slots (`slotsOf`), written rows (`Env.slotOf`, `Env.checkWritten`, `Env.settle`) |
| `Frontend/Elab/Subst.lean` | a handler site's types at a template's instance (`HInfo.subst`) |
| `Frontend/Sugar.lean` | several sites in a counted loop's body |
| `Frontend/Parser.lean` | `with n = h(…)`, `n.op(…)`, `src: E` in a written row |

The reports (§18) print an entry's name, `row L:C: sync: src: Kube, dst: Kube`, the handler a
call goes to, `on the state of `cluster` named `src``, and a copy's slots, `for cluster as
`src`, cluster as `dst``.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/effects-instances.bc` | `Fail[Bad]` and `Fail[ParseError]` in one row with no `map_err`; both raised in one counted loop's body; the two handlers nested both ways | `((inl (inl i32[42]), …), (inl (inl i32[10]), (inr (inl i32[108]), inl (inr (inr (inl u8[97]))))))` | `0 0 0` |
| `corpus/effects-abstraction.bc` | the rule at a coinciding instance: a generic body's own handler of `Fail[E]` does not catch `Fail[ParseError]` at `E := ParseError`; two entries that coincide, served by one site | `((inr (inl ()), inl (inr (inr (inl u8[33])))), (inr (inl ()), inr (inr (inl u8[33]))))` | `0 0 0` |
| `corpus/effects-named.bc` | target 3 of #18: two clusters (`sync` with `src` and `dst`, the names swapped), two maps of two handlers, two nested caches of one handler | `((i32[37], i32[90]), (i32[7], (i32[30], (i32[4], i32[1]))))` | `10 0 0` |
| `corpus/effects-fail-list.bc` | `handleFailList` (Schuster et al., ICFP 2020, §4.3): a handler installed around a computation parameter, under another instance's handler | `((i32[3], i32[0]), (inl i32[0], inr i32[7]))` | `0 0 0` |
| `corpus/effects-cancel-two-sites.bc` | #514: a stateful clause that cancels `k` and raises, under two handlers of `Fail` | `(inl (inl i32[30]), inl (inr i32[0]))` | `0 4 0` |
| `corpus/effects-row-inferred.bc` | a row inferred from a raised value's type, with no written row | `(inl i32[3], inr i32[4294967292])` | `0 0 0` |

Rejects: `corpus/reject/effect-instance-ambiguous.bc` (an operation two instances in scope could
serve, its argument a literal), `effect-row-twice.bc` (an instance listed twice, unnamed),
`effect-name-unserved.bc` (a named entry with no handler of its name), and
`effect-with-two-instances.bc` (a handler whose type arguments the body leaves open, over two
instances). `corpus/reject/effect-error-type.bc` now raises a literal: its `raise(n)` at `n : i32`
determines `Fail[i32]`, and is `corpus/effects-row-inferred.bc`.

### Baseline

No change to `CDerives`, the relation, the machine or the checker's rules: two instances are two
sites, as §19 has them, and the elaboration emits the core terms it did. `fundamentalC`,
`adequacyC`, `fundamentalD` and `adequacyD` keep their statements. Every existing corpus program
elaborates to the same core (`bcc desugar`, compared on every corpus program), with the same
output, goldens, counts, `corpus/kernel-counts.expected` and reports.

### Not provided

- Renaming a handler to serve an entry of another name (`with src = a { … }` over a handler `a`
  in scope); a function whose entries are named `a` and `b` calls one whose are `src` and `dst`
  only through handlers named so.
- An operation's instance from a type inference does not synthesize: it is ascribed, or named.
- A computation parameter (§33) that provides two instances of one effect: its ports are by
  effect.
- A `poly` case (§36) that performs an effect: the case is chosen in the typed elaboration, after
  the operations are resolved. The table now has the argument types a case is chosen by, so the
  effects pass could choose it.
- Type parameters on an answering effect (§18): two instances of one answering effect are told
  apart by name only.

### Open

- Integer division that raises is §39: the effects pass gives `a / b` the instance
  `Fail[DivError]` at an integer width, decided by the walk that reads the instances.
- `Stdout` and `Stderr` as one output effect at two named instances (§34): `main`'s platform
  handlers installed named (`stdout`, `stderr`), the library's writers taking an unnamed entry
  (served by the innermost) or a named one, and the corpus's `eprint_byte` calls written
  `stderr.print_byte(…)`.
- A name in a `|>` stage (§33), and on a `for`'s site of an iteration effect (§15).

---

## 39. Entry 38 — integer `/` and `%`: a division with no answer raises `Fail[DivError]`

### Motivation

#513. An integer division with no answer (a zero divisor, `MIN / -1`) **raises** through the
effect system. **Decided by the user** (2026-10-17): "I just want div by zero to raise not panic.
That is kind of the whole point of an effect system." It never traps, panics or answers a made-up
value (`x / 0 = 0`). Until this entry integer division was reachable only as `host[div_s32]` and
the rest, answering `I32 + 1` (§8), and programs matched on that by hand; §37 made `/` float-only
for the time being. The error is an instance of `Fail`, `Fail[DivError]`: §38 lets a row hold it
beside a program's own `Fail[E]`, so no effect of its own is needed (decision 65).

Everything here is elaboration, library code and lowering over existing core terms: no `CDerives`
rule, relation clause, machine step, host operation, kernel type or checker rule.

### The operators

`/` and `%` at `i32`, `i64` and `u8`, and the library's `div_euclid` and `rem_euclid`:

| form | answer | can fail |
|---|---|---|
| `a / b` | the quotient truncated toward zero (C, Rust, Wasm) | `b = 0`; `MIN / -1` at `i32`, `i64` |
| `a % b` | the remainder, with the dividend's sign; `MIN % -1 = 0`, as Wasm's `rem_s` | `b = 0` |
| `div_euclid(a, b)`, `rem_euclid(a, b)` | `q`, `r` with `a = b·q + r`, `0 ≤ r < |b|` | as `/` and `%` |
| `checked_div(a, b)`, `checked_rem(a, b)` | `inl q`, or `inr e`, `e : DivError` | never: the error is the answer |

At `u8` the division is the unsigned `i32` one on the widened operands (as §8's byte operators
are), and cannot overflow. The operators are `SurfOp.div` and `SurfOp.rem`, `%` at `*`'s
precedence; `(%)` is a `poly` family as `(/)` is (§36, `op_rem`). At a float width `/` is IEEE
754's (§37), with no row, and `%` is refused: a float has no remainder (Wasm has no `frem`).
`host[div_*]` and `host[rem_*]` are unchanged. `checked_div` and `checked_rem` are names of the
surface, `VSugar.checked`, unless the program declares a function of that name.

### The error: `Fail[DivError]`

`lib/arith.bc`, brought in by the elaboration when a division can fail (`include arith` names it,
for `div_euclid` and the type):

    type DivError = 1 + 1          -- inl (): the divisor is zero; inr (): MIN / -1 overflows
    def div_by_zero : 1 + 1 = inl ()
    def div_overflow : 1 + 1 = inr ()
    fn div_euclid[T](a: T, b: T) -> T       fn rem_euclid[T](a: T, b: T) -> T
    handler main_div_error[A]: Fail[DivError], A -> A + 1

The handlers are `Fail`'s own (`lib/fail.bc`): `to_result`, `default(d)`, `map_err(f)`. A
function that divides by a variable has `Fail[DivError]` in its inferred row, with nothing written.

- **Beside a program's own `Fail[E]`.** A function that raises its own error and divides has two
  entries, `Fail[E], Fail[DivError]` (§38); a `with` handles the instance its type arguments say
  (`default[DivError, i32](0)`), or the one instance its body performs, and passes the other.
  `map_err[DivError, E, A](f)` raises the division's error as the program's own.
- **The slot rule** (§38, *Abstraction safety*). A division's `raise` is resolved at the template's
  types like any operation: in `share[E]`, which handles its own `Fail[E]` around `1000 / t`, the
  division's error goes to the slot `Fail[DivError]` of `share`'s row, and at `E := DivError`
  still passes `share`'s handler (`corpus/div-abstraction.bc`). Two entries that coincide at an
  instance are served by one site.
- **A written row** lists `Fail[DivError]` as it lists any instance the body performs; a written
  row without it is an error that says so (`corpus/reject/div-row-unlisted.bc`).

### Elaboration: deciding a division's row

Whether `a / b` can fail depends on its width (a float's cannot) and on its divisor at that width
(`4294967295` is `-1` at `i32`). §38's effects pass reads instances where the types are, by the
typed elaboration's inference over each body before effects are resolved
(`Frontend/Elab/Instances.lean`), and decides a division there:

- **The operands' width.** `Instances.argTy` types an operator as the typed elaboration does
  (`surfOp`): its operands' width, a literal taking the other operand's; a comparison's is
  `1 + 1`; a checked division's is the width and `DivError`. A counted loop's variable is an
  `i32` (§16).
- **The decision** (`divCanFail`). At an integer width, a division can fail unless its divisor is a
  literal at which it has an answer (nonzero, and not `-1` for a signed `/`); at a float width, or
  with a float literal operand, it cannot. A written literal `k` with `0 < k < 256` cannot fail at
  any integer width. One that can fail is recorded at its own span with the instance it raises,
  `[DivError]`.
- **A width not known there** — an operand inference does not type (a block's parameter whose type
  a generic callee's instantiation gives, a local bound from a `match` with literal arms), a type
  parameter (whose instances may be integers), or a program's own type with a case of the
  operator's family — is **taken to be able to fail**: the division raises when it fails, as an
  integer division would, and at a float or a family's case its error arm is never taken. `bcc
  check` reports each (`lowering L:C: a division whose operands' width is not known where effects
  are resolved…`), and ascribing an operand, `(x : i32)` or `(x : f64)`, makes it exact. No
  existing corpus program has a float division of this kind.
- **The rewrite** (`Frontend/Elab/Divisions.lean`). Before rows are inferred, each recorded division
  is written as a program would by hand,

      a / b   ⟶   run (case checked_div(a, b) { inl q -> return q | inr e -> return raise((e : DivError)) })

  with the `raise` at the division's span, where the table holds its instance. So it is an ordinary
  operation of `Fail[DivError]` for everything §18 and §38 do: rows, slots, copies, counted loops,
  recursive groups, unwinding borrows, drop glue. The rewrite is one pass over the declarations at
  the decisions of the walk §38 already makes: there is no second elaboration.
- **The typed elaboration** (`Frontend/Sugar.lean`, `surfOp`) gives each division the host
  operation taken apart at its width: the checked form `divChecked` (`inl q`, or `inr e` with `e`
  chosen by `eqz` of the divisor for a signed `/`), or, at a divisor at which it cannot fail,
  `divUnchecked`, whose `inr` arm, never taken, answers `0` to be typed. A division that reaches
  it at an integer width with a divisor that can fail and was not written to raise is an error
  (`… its effect was not given where effects are resolved …`): the walk and the typed elaboration
  read the width the same way, so this is a check, not a case a program meets.
- **A `case` on a checked division** is fused with the operation's own (`fuseChecked`): the
  quotient's arm and the error's arm are the host operation's, and the division is tested once.

### Zero cost

- **A literal divisor** (nonzero, not `-1` for a signed `/`) performs nothing: no row, no copy,
  and the bare instruction. The flat IR knows the locals set to a constant where they are made
  (`LState.consts`, each local set once): a division by such a constant has no test (`divTest`),
  and a `case` on a constant tag selects its arm. `corpus/div-literal.bc` (counts `0 0 0`)
  compiles `m % 10` and `m / 10` to `i32.rem_s` and `i32.div_s` with no branch, and
  `corpus/sugar/div-literal.bc` pins the elaborated code against `div-literal.core.bc`.
- **A variable divisor costs one test**: Wasm's trap condition (`b = 0`, and `a = MIN ∧ b = -1`
  for `div_s`), a branch to the error arm, the instruction in the other. A `case` on a division's
  answer is lowered as the division's own test (`Backend/Flat/Lower.lean`, `lowerTm`'s fused
  `letv`/`case`), so no tag is built and tested again. An error leaving a function is §19's: the
  copy answers a sum, as any abortive operation does. The six rewritten corpus programs keep their
  counts.

### `main`

A `Fail[DivError]` that `main` performs and handles nowhere is served by `main_div_error`, as the
platform serves the system interface (§34). Its clause writes `error: division by zero` or
`error: integer overflow in division` on standard error (`Stderr`, served by the platform on its
cell) and answers `inr ()`. `Frontend/Elab/Effects.lean`, `divMain`:

- `main : F A` becomes `main : F (A + 1)`, and the handler is around the rest of `main`'s body
  from its first statement that performs `Fail[DivError]` (`splitDiv`; a call's argument that
  performs none, `f(read_input())`, is bound before it). What comes before runs outside it:
  reading the input, which loops over a capability `main` holds and so cannot be in a control
  handler's body (below), cannot fail.
- **Innermost.** A program's own handler of `Fail[DivError]` is a `with` inside `main`'s body, so
  it is inside `main_div_error` and innermost: it handles its body's errors, which never reach
  `main_div_error` (`corpus/div-innermost.bc`). Only an instance `main` leaves unhandled is
  served; a program's own `Fail[E]` unhandled at `main` is §18's error, as before.
- The unwind runs the finalisers of what `main` built (§19), and the run ends with `live 0`.
- **The exit status.** `main` is served when its typed term has a `handle` node whose site is
  `main_div_error`'s for `Fail` (`Check.Checked.exitsOnDivError`, §19 *Handler sites*); its value `inl v` is reported as `v`, and `inr ()` as no value, the live
  count, and exit status `1` (`Backend/Value.lean`, `reportExit`). Every stage does the same: the source stage's model run
  (`ioOutputN`), the closure IR (`Clos.Prog.exits`), the flat IR (`Stmt.status`, `entryFn`) and
  Wasm (`$exit`, WASI `proc_exit`, the entry's last act). `bcc interp` and `bcc run` exit with it;
  `bcc-counts` checks that the flat IR and Wasm end with the same status.
- **The libraries on demand.** A program with a division that may fail that does not include
  `lib/arith.bc` is given it only when one can (`Elab.Effects.elaborate`'s `divLib`), ahead of
  the program; and `lib/wasi.bc`, for `main_div_error`'s standard error, only when `main` is
  served (`platform`), just before `main`, its externs and clauses ahead of the program's own
  declarations (a program with the platform's externs and no capability does not run, #515).
- **Harness.** `<name>.status` holds a corpus program's exit status (`0` when absent), compared
  at every stage by `scripts/compile-corpus.sh` and in every mode by `scripts/falsify.sh`, and
  written by `--write-goldens` with `<name>.out` and `<name>.err`.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/div-recover.bc` | `default` and `to_result` recover a zero divisor; a buffer built in a counted loop dropped by the unwind | `((i32[4], i32[4294967295]), …)` | `5 0 0` |
| `corpus/div-unhandled.bc` | no handler: `main` is served by `main_div_error`; the buffer unwinds, the error on standard error, status 1 (`.err`, `.status`) | `before`, `live 0`; `error: division by zero`; 1 | `1 0 0` |
| `corpus/div-innermost.bc` | the program's own `default` and `to_result` inside `main_div_error`'s region are innermost; status 0 | `(i32[5], (i32[4294967295], inr (inl ())))` | `0 0 0` |
| `corpus/div-own-fail.bc` | constraint 1: `Fail[i32]` and `Fail[DivError]` in one inferred row, handled apart and merged by `map_err` | `((inl i32[5], …)` | `0 0 0` |
| `corpus/div-abstraction.bc` | the slot rule at `E := DivError`, and two entries that coincide served by one site | `((inl (inl i32[250]), …)` | `0 0 0` |
| `corpus/div-overflow.bc` | `MIN / -1` overflows at `i32` and `i64`, `MIN % -1 = 0`; bytes; `checked_div`, `checked_rem`; a literal `-1` divisor | `((inr (inr ()), i32[0]), …)` | `0 0 0` |
| `corpus/div-euclid.bc` | truncating against Euclidean results on negative operands, and `div_euclid(MIN, -1)` | see the file | `0 0 0` |
| `corpus/div-infer.bc` | rows inferred: a parameter divisor, a counted `for`, a generic at `i32` and `i64`, a float division (no row), a literal divisor (no row), a block to a generic HOF, a resuming handler's clause by `checked_div` and a cancel | see the file | `0 4 0` (the resumptions of a handler with a parameter, §21) |
| `corpus/div-recursive.bc` | a division in a recursive group (§20), beside `Exhausted` | `(i32[12], inr (inl ()))` | `0 0 0` |
| `corpus/div-literal.bc` | division by a literal: no row, the bare instruction | `(i32[15], i32[49500])` | `0 0 0` |
| `corpus/int-slash.bc` | `7 / 2`, moved from `corpus/reject/` | `i32[3]` | `0 0 0` |

`corpus/reports/div-*.txt` pin the rows, the copies and `main`'s report; `corpus/sugar/div-literal.bc`
the elaborated code; `corpus/reject/div-row-unlisted.bc` a written row that leaves the division's
instance out. Pending, each refused as a `raise` there is: a variable divisor in an adapter's
stored function (#161, `corpus/pending/div-in-adapter.bc`) and in a clause of an answering handler
(§18 *Not provided*, `div-answering-clause.bc`); `k(x / d)` in a resuming clause, where `k` is
live across the abort (`checked_div` and a cancel serve, as `div-infer`'s `scaled`).

**Corpus rewrites.** The hand-written divisions became `/` and `%` where each program's output and
counts stay as they were: `aoc/2021-06` (`modulo(day, 9)`, a literal divisor), `map-views`
(`rem(x, 10)`, `rem(i, 3)`), `aoc/2021-15`, `leetcode/graphs/0200`, `0417` and
`leetcode/trees/0212` (`quot`, `modulo` by the grid's width; `main` is now served by
`main_div_error`; the divisors are never zero on the inputs). `0212` was kept in its form by #518
for two abortive effects in a counted `for`'s body, which §38 provides. The others keep their
form, each for a limit that applies to any abortive operation (#517), checked again here:

- `aoc/2022-12`, `aoc/2023-03`, `aoc/2024-11`, `aoc/2022-21`: the division is inside `borrow imm s`
  of the input string, a borrow of a buffer that an abort would cross (§18 *Not provided*);
- `leetcode/matrix/0054`, `0073`, `0079`: the division is inside `cases`, a loop over the input
  with no bound, and a handler around a div computation is not provided (§20); the refusal is
  reported as a type mismatch against the loop's type, as it is for a `raise` there (#522);
- `float-roundtrip`: `div_u64` of a float's bits, which `/` (signed) would change;
- `int-arith`, `int-ops` and the core forms of `corpus/sugar/`: the host operations' own tests.

The library's `host[div_u*]` uses (`lib/io.bc`, `lib/text.bc`, `lib/float.bc`) are unsigned and
keep their form.

### Baseline

No change to `CDerives`, the relation, the machine, the host's operations, `PinLaw`, `Paper/`,
`Support/`, `Core/` or the checker's rules. `fundamentalC`, `adequacyC`, `fundamentalD` and
`adequacyD` keep their statements and cover every elaborated program. Every existing corpus
program elaborates to the same core and the same reports (`bcc desugar` and `bcc check`, compared
on every corpus program), with the same output, goldens, `corpus/kernel-counts.expected` and
`corpus/counts.expected` entries; the file only gains the new programs'. The flat IR's two
lowerings (a constant divisor, a constant tag; a `case` on a division) change the code of
programs that divide or match on a constant injection, not what they compute or count. A control
handler's `with` now has in its row the answering effects its clauses perform (`rowV`; they run
in the scope of the `with`). `corpus/reject/include-unknown.bc`'s message lists `arith`. The
system interface's declarations are not reported however a program brings them in, `lib/arith.bc`
included (§34).

### Not provided

- `main_div_error` around a loop of `main` (a `main` that returns a loop): `main` handles
  `Fail[DivError]` itself.
- `main_div_error` around a statement of `main` that loops over a capability `main` holds
  (`read_input()` after the first division): a control handler's body is lent the capabilities,
  and a borrow cannot be held across a loop's observations (§14, §34). `main` handles the error
  around the division instead, or reads first.
- `%` at a float type; unsigned `/` at `i32` and `i64` (there are no unsigned types:
  `host[div_u32]`).
- Arithmetic overflow of `+`, `-`, `*`: they wrap, as Wasm's (§8); `add_checked` and
  `mul_checked` raise their own `Fail[1]`.

### Open

- **The width where effects are resolved.** The walk types operands by inference with no type
  expected of them, so a division whose width only its context gives (a block's parameter typed by
  a generic callee's instantiation, a literal's width from the type expected of it) is taken to be
  able to fail. No corpus program has a float division of this kind; one would have a row it does
  not need until an operand is ascribed. Reading the type the typed elaboration expects there would
  make it exact.
- Where `main_div_error` cannot reach (#517): a division inside a borrow of a buffer, a loop with
  no bound, or a statement after a loop over a capability `main` holds; the programs above that
  keep their form.
- A message naming where the division was; an exit status other than `1`.
- The platform's handler for `Exhausted` at `main` (#228), by the same mechanism (`divMain`,
  the site of its `handle` node, `reportExit`).

## 40. Entry 39 — the native target: LLVM IR from the flat IR

### Motivation

#529, part of #21: the language targets native code through `clang`, and Wasm stays the target
the proofs are run against. Both are implementations of SPEC's operations (§8, §37), neither of
the other: no Wasm quirk is carried into native code. The flat IR (`Backend/Flat/Syntax.lean`)
was built for this: 64-bit words, numbered locals, explicit allocation and free, direct calls of
several results, `switch`, explicit tail calls.

Everything here is backend: no change to the language, the kernel, the checker or any program.

### The target

- `bcc compile --target native <file> -o <out.ll>` prints the program's LLVM IR for the host's
  target; `bcc run --native <file> [arg…]` builds it with `clang -O2`, beside the native runtime,
  and runs it. `bcc kernel run --native <name>` does the same for a kernel program and
  `bcc-counts --native <file>` compares the native build's counts with the flat IR's.
- The C compiler is `$BC_CC` when set; else on macOS `xcrun clang` (the Xcode toolchain's, with
  its SDK); else the first `clang` on `PATH` outside a Lean toolchain, whose own `clang`
  (first on `PATH` under `lake exe`) has no C headers. `bcc cc` prints it.
- A flat-IR function is an LLVM function of the C convention; a tail call is `musttail`, which
  guarantees a jump between functions of one prototype, so the functions joined by tail calls
  share one: the most parameters of any of them, the missing ones `poison` (a tail call passes
  the caller's results on, so the results agree). `tailcc`, which lets prototypes differ, is
  miscompiled by Apple clang 21 on AArch64 (`Backend/README.md`, Native). A function returns one word as an `i64`, up to the
  target's registers for results (8 on AArch64, 4 on x86-64) as a struct by value, and more
  through a pointer the caller passes and a tail call passes on (LLVM refuses its own `sret`
  demotion under `musttail`).
- Words are real pointers. The program's data is a global; the flat IR names its addresses
  (`Flat.Exp.data`, from the closure IR's `Op.dataAddr`), which Wasm places at `16384` and
  native code at the global. Frame slots (§35) are an `alloca` of the function's frame.
- Every host operation computes SPEC's answer with no undefined behaviour or poison: shifts mask
  the amount (§8), `clz`/`ctz` of zero is the width, a division and `trunc` with no answer branch
  to a trap that no run reaches (the flat IR tests first, §39), `MIN % -1` is `0`, `trunc_sat`
  saturates (`llvm.fpto[su]i.sat`), `min`/`max` propagate NaN (`llvm.minimum`/`maximum`),
  `nearest` rounds ties to even; no instruction has `nsw`, `nuw` or fast-math flags. The table
  per operation is `Backend/README.md`, Native.
- The runtime (`Backend/Native/Runtime.lean`, C, trusted) is the allocator with the Wasm
  runtime's specification and algorithm, so `live` and the counts agree, and the POSIX platform
  of §11 and §34: `read`/`write` on the descriptors, unbuffered; the arguments from `argv`;
  `CLOCK_MONOTONIC` and `nanosleep`; the exit status of §39. The entry runs on a thread of a
  512 MiB stack.

### Tests

`scripts/compile-native.sh`, a step of `make gate` (passing with a notice when there is no C
compiler, as the book build is skipped without `mdbook`): every corpus program built natively matches its golden standard
output, standard error, exit status and `live`, which the flat IR is checked against, and
`bcc-counts --native` agrees with the flat IR; every kernel program prints what it prints at the
flat IR; every host operation, on a table of operands read at run time, answers what the Lean host
(`flatHost`, the flat-IR interpreter's) answers (`bcc hostops`), a NaN that arithmetic answers
compared as a NaN only; and loops of tail calls run in a stack of 64 KiB (`bcc tailcalls` at
10⁸ turns, the kernel program `loop-tail`, `corpus/deep-list.bc`). A program is also built and run under
`lake env`'s `PATH`, where the Lean toolchain's `clang` comes first.

### Baseline

No change to `CDerives`, the relation, the machine, the host's operations, `Paper/`, `Support/`,
`Core/`, the frontend or the checker. The closure IR's literal address is `Op.dataAddr` where it
was an `i32` literal, and the flat IR's `Exp.data`: every corpus program's WAT is unchanged, byte
for byte, and every output, golden and count is unchanged.

### Not provided

- Performance tuning: native output is unbuffered, as Wasm's is, and no optimization is aimed at
  native code (#530).
- Aliasing attributes from the borrow invariants (`noalias`, `readonly`, #531).
- Detection of stack overflow, debug information, linking with C (#532).
- A target other than the host's: the IR has no triple, and `clang` builds it for the host.

### Open

- **NaN payloads and the proofs (§37 *Open*).** The native target does not canonicalise: an
  arithmetic NaN is the hardware's (AArch64: the default NaN or a propagated payload), except
  where `clang` folds an operation on constants, whose NaN is LLVM's choice and need not be the
  hardware's. A run's choice is then not a function of the operation and its operands, so native
  code is the engine §37 *Open* names: it is not the machine at one conforming host, and no
  theorem of §37's *What the proofs cover* is about its runs until the host step is a relation.
  What holds is tested: every corpus golden at native, and every host operation against the Lean
  host on operands read at run time (so unfolded), an arithmetic NaN compared as a NaN only.
- **Stack depth.** The native stack is sized (512 MiB) rather than bounded: `bounded`'s budget
  (§20) is calibrated against Wasm's 64 MiB, and a native frame is not the same size (#532).

---

## 41. Entry 40 — `let mut`: names resolved to their binders, compositional writes, one boundary rule

### Motivation

#613, after #611's spike (PR #612). Every silent wrong answer of `let mut` has one of two causes:
state that crosses into another frame (a block, a `modify` callback) is not passed in and back
out (#586), and the threading reads variables back **by name**, so a `let` that shadows a
variable takes its place where an arm joins or a loop's turn ends (#504 and its broader form,
#493, #590). The user's requirement: "it's done in a principled way. Because if you just try to
get one program to compile, the first permutation will break." So the elaboration of `let mut`
is three general rules, one per surface construct, in place of hand-written cases:

1. **R1, resolution:** every name resolves to a unique binder before any threading, so threading
   never compares names;
2. **R2, writes:** what a construct writes is computed from its parts;
3. **R3, the boundary:** one rule passes a construct's writes in and out of every construct that
   runs code in another frame; a writer that escapes is refused by a named rule.

Each is one function of the elaboration: R1 the parser's resolution (`bindName`, `lookName`), R2
its write set (`frame`), R3 one hand-on (`handOn`) and one capability rule for blocks
(`Elab.Effects`, `mutCap`).

**Prior art.** The rules follow the translation of Ullrich and de Moura, *'do' Unchained:
Embracing Local Imperativity in a Purely Functional Language* (ICFP 2022; read for this entry):
`let mut` is a local state effect over its scope (their Fig. 5, rules S1–S6), a join point
rebinds the variable (S2, and S9 at a loop's entrance), the rewriting system is assumed hygienic
(§2: "an identifier introduced by a rewriting rule is renamed automatically to avoid any conflict
with user-specified names"), and reassignment is legal only in the `do` block that declares the
variable (§2), the analogue of R3's escape refusal. Two differences: they refuse a binder that
shadows a `mut` variable (S2, S3's side condition `x ≠ y`, "shadowing of mutable variables is
disallowed in general"), where R1 makes it a variable of its own; and their state crosses only
`do`-block joins and `for`, where ours also crosses blocks, borrow and `modify` callbacks, loop
turns observed one at a time, generators and handlers (R3). Koka's `var` (the Koka book, §3.2.4
*Local Mutable Variables*; read) is a local state handler; a closure that assigns it has the
`local<h>` effect in its type, and one that escapes the variable's scope is a type error: the
precedent for R3's escape refusal, and for a write being visible in a closure's type. Effekt's
mutable variables (the Effekt tour, *Variables* and *Regions*; read, not checked against its
implementation) live in a region, a closure over one has the capture set `at {x}` in its type, and
it may be used only where the region is in scope.

### R1: resolution

In a surface body (a `fn`, `main -> T`, a handler's clause, a `poly` case), the parser resolves
each name as it reads it (`Frontend/Parser.lean`, `bindName`, `lookName`):

- **A binder of a name already in scope is a new variable.** It gets a fresh name, `x1`, `x2`,
  …: the first that no name of the source and no earlier renamed binder has. So no binder shadows
  another, and two variables never share a name. This holds for every binder: `let`, `let mut`,
  `x <- M`, `fun`, a closure's or a borrow block's pattern, a `with`'s capability, a `match` or
  `case` arm, a `for`'s variable, `withbor2r`'s view.
- **An occurrence resolves to the innermost binder of its name in scope,** or to a declaration
  when none is.
- **A binder spelt as a generated name is a new variable too.** The elaboration binds and
  recognises names of its own (`io_…`, `fx_…`, `hy{n}…`); a source binder with such a name gets a
  fresh name outside them (`Parser.generatedName`), so generated code never takes it for its own
  (`corpus/generated-names.bc`: a `let io_bt` stopped a borrow block handing back its writes).
- **Except:** a capability (`stdin`, `stdout`, `stderr`, `clock`, `args`) is a place the
  platform names, passed and handed back by name (§11): a binder of its name rebinds it. Core text
  (`def`, `main : C`) is not resolved: it has no assignment, and a binding of a name in scope is
  how it passes a variable on (`corpus/sugar/for.bc`). Generated templates are not resolved.
- **Declarations.** A program's declaration of a name an included module also declares shadows
  the module's: the module's is renamed, in its own name and wherever the module's declarations
  name it, so the module's code keeps meaning its own (`Decl.renameDecls`, #590).
- **Messages** name a renamed binder as the source writes it (`Error.renderIn`, `unrename`): a
  fresh name is no name of the source.

### R2: writes

A construct **writes** a `let mut` variable when it is, or contains on its own frame:

| form | writes |
|---|---|
| `x = e` | `x`, where `x` resolves to a `let mut` variable; otherwise refused: "`x` is assigned, but it is not declared `let mut`" |
| `x <- M`, `x : A <- M`, `linear x <- M` | `x`, the value of `M`, where `x` resolves to a `let mut` variable ('do' Unchained's A4, `x ← s`); otherwise R1's new variable |
| `let (x, q) = f(…, x, …)` | the place `x` moved and rebound (typed elaboration §5.1): `x` is the variable it was, and a write when it is `let mut` |
| any other binder of a name in scope | nothing: R1's new variable |

| a lend `&mut x`, `&x`; a borrow block's or `modify`'s place `x` | `x`, where `x` resolves to a `let mut` variable: the construct rebinds its place |

**A construct's writes are its parts' writes** (`Parser.frame`): every construct whose parts
write reads each part in a frame of its own, and what the part writes of the enclosing `let mut`
variables, in the order they were declared, the construct writes too. The rule table below gives
each construct's parts. Writes are of resolved variables (R1), so a shadowing `let` is never taken
for the variable it shadows.

### R3: the boundary

A construct whose part runs in another frame, before the code after it (an arm, a binding's head,
a callback, a block, a loop's turn), passes that part's writes `W` in and back out:

- **In.** A part that runs where it is written sees the variables in scope: a callback, an arm or
  `run M` reads them as they are. A part that runs elsewhere, a block called by its callee, takes
  them as parameters: the block is `!U(W ⊗ A ⊸ F_r (W ⊗ B))` at the callee's copy, which takes `W`
  after its own parameters, passes them at each call of the block parameter, binds them again
  after it, and hands them back first. This is §32's rule for a block's capabilities: a variable a
  block writes is one of its capabilities (`Effects.mutCap`), its type a parameter of the copy.
- **Out.** The part hands back `W` at each terminal, beside its value or alone (`Parser.handOn`),
  and the construct's binding takes the tuple apart, rebinding `W` (`joinBind`, `letVal`). A
  join's terminal that is a value hands it on as it is, `return (V, W)` (`return W` for `()`), and
  a loop's turn that ends in `()` goes on with no binding of it (`Sugar.thenGo`); only a frame whose
  later elaboration reads its terminal's binding (`io_bt`: a borrow block, `with`, `modify`,
  `run`) binds it.
- **A `let mut` value is no place.** `modify &mut x { v -> S }` of a `let mut` value `x` (not a
  cell `ref A`) runs `S` on `x`'s value in place, `run (let (v, u) = (x, ()); S)`, its new content
  rebinding `x` as the lend does; a cell is `modify`'d through `withswap`.
- **Refused,** each by a message that names the rule: a closure that writes and is not given at a
  block parameter of a call, stored or returned (`Effects.escapingWriter`); a `run` that writes
  inside an expression (`checkRun`); a control handler's body that writes (it may be abandoned,
  §18 *Not provided*); a `for`'s `else` value that writes. Koka's precedent is the escape
  refusal: its `var` in a closure that escapes is a type error.

### The rule table

One rule per surface construct. "W" is what its parts write (R2). An unlisted construct writes
what its parts write and has no boundary of its own.

| construct | writes | boundary (R3) |
|---|---|---|
| `let mut x = e; N` | `W(e) ∪ W(N)` | declares `x`, a variable of its own (R1) |
| `x = e` | `{x} ∪ W(e)` | — |
| `x <- M` on a `let mut` | `{x} ∪ W(M)` | — |
| `let (x, q) = f(…, x, …)` | `{x}` | — |
| `let p = e; N`, `x <- M; N`, `S; N` | `W(e) ∪ W(N)` | — |
| `&mut x`, `&x` | `{x}` | the lend rebinds `x` (typed elaboration §5.1) |
| `if`, `match`, `case` (a statement) | `W(arm₁) ∪ W(arm₂)` | each arm hands on `W` (`handArms`); the statement rebinds it |
| `let p = if/match …`, `x <- M` (a head) | `W(M)` | each terminal hands on `(value, W)`; the binding takes it apart (`bindForm`) |
| `for x in V { M }`, `while`, `loop`, `for` over a generator | `W(M)` | a turn: the loop's state is `W` and the variables it reads (§14, §15, §16); each turn hands it on |
| `borrow k P { b -> S }` | `{P} ∪ W(S)` | the callback hands back `(result, W)` beside the places it lends; the binding rebinds `P` and `W` |
| `modify P { v -> S }` | `{P} ∪ W(S)` | the callback hands back `(c, (r, W))`, the new content `c` and the result `r` (`()` when there is none; `Sugar.modifyBody`); of a `let mut` value, the body runs in place |
| `with h(e) { S }`, answering | `W(S)` | as a borrow block of the state's cell (§18) |
| `with h(…) { S }`, control | — | refused when `W(S)` is not empty |
| `run M` | `W(M)` | `M` hands back `(value, W)` where it is bound; inside an expression, refused |
| a closure: `{ p -> S }`, `!{ … }`, `{ S }`, `thunk`, `thunkv` and their `!` forms | `W(S)` | marked `writes(W) V` (`VSugar.writes`); at a block parameter of a call, the copy passes `W` in and out at each call; elsewhere refused |
| a `for`'s `else { d }` | — | refused when `W(d)` is not empty |
| a handler's clause | its `mut` parameters only | the state is threaded by §18 |
| a declaration (`fn`, `main`, `def`, a `poly` case) | its own `let mut`s | no `let mut` reaches another declaration |

`writes(x, …) V` is printed by `bcc print` for a closure that writes; in a surface body it is not
written (the parser finds it), and in core text it is read as printed.

### Programs

| program | what it shows | answer |
|---|---|---|
| `corpus/mut-shadow-arms.bc` | a `let` shadowing a `let mut` in an `if` arm, a `let` head, a `match` arm and a `for` body (#504's broader form) | `(i32[2], (i32[3], (i32[4], i32[6])))` (was `(50, (60, (70, 1020300)))`) |
| `corpus/reject/mut-shadow-assign.bc`, `mut-shadow-assign-loop.bc` | #504: an assignment after a shadowing `let` | refused: "`n` is assigned, but it is not declared `let mut`" (was `11`, `13`) |
| `corpus/loop-shadow-persistent.bc` | a `let` in a loop's body shadowing a variable that is not `let mut` | `(i32[1], i32[3])` (was `(4, 6)`) |
| `corpus/mut-bind-arm.bc` | `x <- M` on a `let mut` in an arm (R2) | `(i32[5], i32[3])` (the arm's write was lost: `(1, 3)`) |
| `corpus/loop-shadow-linear.bc`, `loop-shadow-owner.bc` | #493's two programs, from `corpus/pending/` | `i32[6]`; `.` and `i32[6]` |
| `corpus/lend-shadow.bc` | a borrow block's `let mut acc` beside `main`'s `acc`, lent per observation | `i32[105]`; in core text still refused (`corpus/reject/lend-shadow.bc`) |
| `corpus/name-clash.bc` | #590 (1): a program's `fn take` beside `include buf`'s | `i32[2]` (was refused) |
| `corpus/mut-name-capture.bc` | #590 (2): a callee's `let mut tbl` beside its caller's | prints `1`, `i32[0]` (was refused) |
| `corpus/mut-block.bc` | #586: a block that writes, at a block parameter called once, twice, and in a loop | `(i32[52], (i32[4036], i32[323]))` (was `(12, …)`) |
| `corpus/mut-block-nested.bc` | a block inside a block, both writing | `(i32[13], i32[3])` |
| `corpus/mut-run.bc` | #586: `run` that writes, bound | `(i32[52], i32[5102])` (was `12`) |
| `corpus/fail/mut-run-nested.bc` | #586: `g(run if … { x = 5; … })`, a `run` that writes inside an argument | refused, R3 |
| `corpus/reject/mut-stored-thunk.bc` | #586: a block that writes, stored and forced later | refused, R3 (was `12`, the write lost) |
| `corpus/mut-modify.bc` | `modify` whose body writes, on a scoped cell and on a `mut` borrow | `((i32[6], i32[7]), i32[120])` (was `((6, 0), 110)`) |
| `corpus/mut-lend-arm.bc` | `&mut x` in an arm (R2) | `i32[12]` (was `2`, the lend's write lost) |
| `corpus/for-in-if-lend.bc` | #502, from `corpus/pending/` | `i32[3]` |
| `corpus/reject/mut-control-with.bc` | a control handler's body that writes | refused (§18 *Not provided*) |
| `corpus/lend-copy.bc` | copies of a borrow block's borrow over a loop: `let b2 = b`, `let mut v = v` (T04's form), a copy after a statement | `(i32[30], (i32[321], i32[6]))` (was refused) |
| `corpus/binder-copies.bc` | a copy of a block parameter, of a clause's continuation, and a copy of a copy | `(i32[4294967291], (i32[103], i32[22]))` (was refused) |
| `corpus/div-residual-copy.bc` | a div function's residual handed back by a copy, `let j = i`, and by `let i = i` | `i32[4]` on `abc` (was refused; `let i = i` ran before R1) |
| `corpus/loop-handler-binder.bc` | #493's handler-clause binder, from `corpus/pending/` | `i32[42]` (was refused) |
| `corpus/generated-names.bc` | a source binder named `io_bt` | `i32[62]` (was `61`) |

`scripts/mut-combos.py` checks the rules on generated nestings (*Acceptance* below).
`corpus/sugar/mut-heads.bc` and `mut-modify.bc` pin the elaboration beside the core written by
hand (#611's targets).

### Acceptance

`scripts/mut-combos.py` (a gate step) generates nestings of the constructs, each assigning the two
outer `let mut`s `a` and `b` by `=`, `<-` and a rebinding call, with shadowing `let`s and binders
named `a` and `b` at every binding position (a `let` head, a `match` arm, a `for`'s variable, a
block's, `modify`'s and a borrow block's parameter). Three rows of 400 programs, depth 3:

| row | constructs |
|---|---|
| `joins` | `if`, `let` heads, `match`, counted `for`, a resuming operation |
| `frames` | the above, blocks at a block parameter (of a callee that calls it twice, one that calls it in a counted loop, and a generic one), `modify`, borrow blocks, an answering handler's body, a control handler's body (reading only), `run` |
| `loops` | the above without the resuming operation, with `while` and a `for` over a generator on the spine |

Each program's answer is compared with the script's own evaluation of it (lexical scope, an
assignment updating the variable it names) and, where the constructs allow it, with the program
run with the variables as `State` instances (#611); the gate fails on any difference and on any
refusal. The generator writes only programs the rest of the language accepts: no resuming
operation inside a borrow's callback (T1), a block reads its parameter and the variables it
writes (a persistent closure captures only `!` values), a div loop only on the spine and with no
handler around it (§14, §21), one borrow of the cell at a time.

### Baseline

No change to `CDerives`, `Core/`, `Paper/`, `Support/`, the relation, the machine or the checker.
Every corpus program elaborates to a core whose run output, goldens, `corpus/counts.expected`,
`corpus/kernel-counts.expected`, `kinds.expected`, `cells.expected` and `handled.expected` are as
they were, except the programs above. A program with a shadowing binder elaborates to the same
core with the binder renamed (`bcc desugar`). Changed:

- `bcc check`'s reports name a program's declaration that shadows a module's as the program's
  (`corpus/leetcode/lists/0206`, `text-wordfreq`: their own `reverse`; probes `bg/regex`,
  `ds/btree`, `tests/T14*`), and the module's renamed one (`cmp_i32'lib`) where it is listed.
- `corpus/reject/lend-shadow.bc` is core text (`main : F i32`), where names are not resolved.
- `corpus/pending/config-parse.bc` is refused at the block given to `fold_lines` (`f` is passed in
  the fold's state, which §30 refuses), before the `raise` it was refused at. The earlier message
  came from the step's pattern binder of the state's block, also named `f`, taken for the block
  parameter by its name: with `lib/` renamed, the build before R1 gives today's message
  (*Binder identity*).
- `docs/expressiveness-probes/tests/T04.bc` is in its original form: its `let mut v = v` inside a
  borrow block over a loop is a copy of the borrow (*Binder identity*).
- `corpus/reject/lend-escape.bc`'s witness is a pair holding the borrow, `let q = (b, 3)`: its
  `let b2 = b` is a copy of the borrow, which the loop may use.
- Each declaration's `let mut`s are its own: before, `main` and a `def` saw the names of the
  function before them, and a borrow block in `main` handed back a variable of that name
  (`corpus/leetcode/strings/0647`: `let (sum, sum) = …`; same output).
- A loop's decision that its body performs an operation that resumes (§16, *Effectful bodies*)
  reads the operations of a `!thunkv` block too, which the copy it is given to performs.
- The typed elaboration types a binding's computation, and a borrow block's body, with its lends
  elaborated (`TCx.tyCL`, `TCx.tyVL`): a lend's result is its call's, as `Comp.elab` makes it.

### Binder identity

R1 makes every binder of a surface body a name of its own; what the elaboration recognises by a
binder, it recognises by that binder **followed through its copies**, never by a name (#617). A
**copy** is `x <- return V` where `V` is a variable, ascribed or cloned (`Val.copyOf?`): `let y =
x`, `let mut v = v`, `let y = (x : T)`. One rule, at every analysis that gives a binder a meaning
of its own:

| what | identified by | a copy of it |
|---|---|---|
| a borrow block's borrow over a loop (§14, `LoopLend`) | the block's parameter | a copy, or a destructuring of it or of a part (`Binding.of?`), anywhere on the block's spine, is one of the block's aliases from there on, bound again at the start of each block the rewrite makes; a copy passed to a div function is the place lent (`lendCall`) |
| a block parameter of a §30 copy, a computation parameter's port (§33) | the copy's `cbs`, `cbRows`, `ports` | is the parameter (`Cx.copy`, `rowC`, `forOverParam`) |
| a clause's continuation (§19), a layer's `call` (§20) | `ResumeK.k`, `LCall.name` | is it (`Cx.copy`; `unboxesC` for BOXED-κ) |
| a div function's residual (§14, *The residual by name*) | the names the terminal hands back | a copy made after the last loop is the binder it copies (`termParts`) |

Two more rules keep generated code and the user's apart, so that no analysis that compares names
can take one for the other:

- **A control handler's code has names of its own.** Its clauses run in the scope of a `with`,
  or as closures built there, so every binder of a control handler (its parameters, its clauses'
  parameters, the binders of its clauses' bodies and its return clause) gets a fresh name,
  `hy{n}c{h}_{x}` (`Decl.hyg`). A `for` in the body of a `with default(0) { … }` chose the
  variables it threads by name and took `default`'s clause binder `e` for the function's own `e`
  (#493's `loop-handler-binder`, now `corpus/loop-handler-binder.bc`, `i32[42]`). Messages name
  these binders as written (`Hygiene.written`, in `unrename`).
- **A capability variable is one per effect and slot** (`capVar`, `capLife`): `Log` and `LOG`,
  or `Log_a` and the slot `a` of `Log`, shared one variable.

A block's `let mut` capabilities key its copy by position (`m0`, `m1`, `blockKeys`), not by the
caller's names: callers whose blocks write variables of other names share the copy
(`ap__b0m0`).

**The renaming check** (`scripts/alpha-check.py`, a gate step) renames every program of the corpus
α-equivalently, with `bcc alpha`: each binder of a surface body gets a name of its own (`{x}q{k}`,
from the parser's record of what each name resolved to, `resolutionOf`), so no binder shadows
another and no two variables share a name. `bcc check` must print the same up to the renaming and
`bcc erase` the same erasure, and the same with every module of `lib/` renamed (`BCC_LIB`). On the
corpus it finds 0 differences. Run on the build before R1 (`--bcc`, renaming with this one's
`--alpha`), it finds 19: each program of #504, #493 and #590, `T04`, `config-parse` and others
whose meaning depended on two names coinciding.

**Justified: what is still identified by a name.**

- A **capability** (`stdin`, `stdout`, …) is a place the platform names (§11); its binder rebinds
  it (R1's exception), and a copy of one is refused (§34).
- **Core text** (`def`, `main : C`) and **generated templates** are not resolved: a binding of a
  name in scope is how they pass a variable on.
- A **handler's name** (`with n = h(…)`, `n.op`, a row's `src: E`) names a site, not a variable
  (§38): the innermost of a name is meant.
- A **declaration** (a function, an operation, a recursive group's member) is found by its name;
  Hygiene keeps every local from sharing one. A copy of a function, `let g = f`, is a value, and of
  an effectful or recursive function refused (§18, §20).
- **`let (x, q) = f(…, x, …)`** rebinds the place written as the argument (R2); `f(y)` with `y` a
  copy of `x` binds a new `x`.
- A **`let mut` variable** threaded by a loop, an arm or a block is identified by its resolved
  binder (R2): unique, so its name is its binder.

### Open

- **A control handler's body that writes**, and a `run` that writes inside an expression, are
  refused. The first needs the handler's clauses to hand the variables back when the body is
  abandoned; the second, the expression's calls lifted in order around it.
- **The target pairs** that are not met (`docs/research/let-mut-state/README.md`): what separates
  each is the counted loop (§16), the state machine of a div body (§14), §32's calling convention,
  a function's parameters and effects' elaboration (§18, §19), none of it this entry's.
- **Lifetimes are not resolved.** A borrow block's `'a` inside another's `'a` is the same name in
  a type, and a type that mentions the outer one reads as the inner one (a refusal, "expected `imm
  'a i32`, but this has type `imm 'a i32`"). R1 for lifetime binders, and in the types and
  instantiations that name them, is not built.
- **A copy of the residual between two loops** of a div function is not followed: the states
  before the copy hold the copied binder, those after it the copy (`termParts` follows copies
  after the last loop only); it is refused where a state names the moved binder.
- **A block that writes, passed through a closure** in its callee (`{ x -> f(x) }` given to
  another block parameter), is refused with a message about `!thunk` promotion: the copy's row
  for a block parameter (`cbRows`) does not carry its `let mut` capabilities.

---

## 42. Entry 41 — data declarations: records, variants, recursion under `box`, match compilation

### Motivation

#593 (`docs/data-declarations.md` §10, unit U1; the decision menu of §11 and its additions §11.1,
decided 2026-10-20). The corpus writes its data as structural types: records are nested pairs,
variants nested `inl`/`inr`, and recursive types `mu X. …` (B3, `docs/expressiveness.md` §3). A
`data` declaration names a type and its parts. It is a name plus an isomorphism to a structural
type of `⊗`, `⊕` and `μ` (#141, decision 1); every rule below is sugar into existing core terms,
and the kernel sees nothing new: no type former, rule, constant or derived form is added, so
`fundamentalC` and `adequacyC` cover every program a declaration elaborates to (decision 26's
argument, as §36 states it for `poly`).

This entry is the data face of `docs/data-declarations.md` §3.1, for transparent declarations.
Faces and dot (U2), abstraction (U3), codata (U4, U5), derive (U6, U7), the `fold` block and data
unfolds (§11.1 A2, A3) are later units.

### Declarations

    data N[P, …]<'l, …> = C₁ | C₂(A, …) | C₃(f: A, …) | …      -- a variant
    data N[P, …]<'l, …> = { f₁: A₁, …, fₙ: Aₙ }                  -- a record

A record is one constructor, named `N`, whose fields are named. A constructor's fields are
positional (`C(A, B)`) or named (`C(f: A, g: B)`). Type and lifetime parameters are as `type`'s
(§7, §22): substituted at each use. `data` is a declaration only where a declaration may begin and
an upper-case name follows it; elsewhere it is a name.

The declaration elaborates to a `type` declaration of the same name and parameters
(`Frontend/Elab/Data.lean`, `typeDecls`), in place:

- a constructor with no fields is `1`, with one field the field's type, with several the
  right-nested `⊗` of their types in declaration order (§5: no trailing `1`);
- the constructors are the right-nested `⊕` of their payloads in declaration order; one
  constructor is its payload alone (a newtype `data Id = Id(i32)` is `i32`);
- a field of type `box A` is a cell, `ref A` (typed elaboration §5.3's `box A`; `box @ A` with a
  lifetime is the lifetime box of §23, unchanged);
- a recursive declaration is `μX. S` with `X` at its recursive occurrences (below).

The name, its constructors and its fields live in the elaborator's table (`Data.Table`), which the
parser holds, read before the module is parsed: a declaration is in scope in the whole module that
declares it and in every program that includes that module, and the prelude's in every program.
Its `type` declaration is placed where the group's first member is, so a type declared later is
named only after it.

### Recursion: blocks and a written `box`

Decided (#489, §6.11, item 13 of §11): every heap allocation of a recursive declaration is
written.

- **A block** is a constructor of a recursive declaration with a field in which the root of its
  group (below; a declaration recursive alone is its own root) occurs other than under `box`. Each field of a block is a cell, `ref A`, and the block is
  allocated whole: `box C(e, …)`. `data Tree = Leaf | Node(left: Tree, val: i32, right: Tree)` is
  `μX. 1 ⊕ (ref X ⊗ (ref i32 ⊗ ref X))`, the corpus's `Tree` of blocks, with
  `shape Tree_Node = node (leaf Tree) (node (leaf i32) (leaf Tree))`.
- **A field written `box A`** is a cell of its own; a constructor whose recursion is only under
  written boxes is not a block (`data L = { v: i32, next: Option[box L] }` is
  `μX. i32 ⊗ (ref X ⊕ 1)`).
- **Refused, asking for `box`**: a block's field whose type holds a member of the group inside
  another type (`tail: Option[List]`, a cell `ref (X ⊕ 1)` outside §6's `FShape`), at the
  declaration; and a block constructor written without `box`, at the construction (E3).
- **Regular recursion**: inside its group a parameterised member occurs at its own parameters.
  A nested datatype (`Tree[(T, T)]`, D2) is refused: not provided.

**Mutual recursion: the single-root rule** (#141, decision 5). The declarations that mention each
other form a group (a strongly connected component of the declarations' references, by name).
A group of several members elaborates to one `μ` when one member, the root, lies on every cycle:
the root is `μX. S_R`, with every other member's structure substituted for its name and `X` for
the root's; every other member is its own structure, the root and the other members named, each
`type` declared after the members it names. The first member in declaration order that is on every cycle is the root; a group
with none is refused: "the declarations … are mutually recursive with no member on every cycle:
not provided (the single-root rule)". Only the root rolls and unrolls.

### The rule table

One rule per construct; every rule is sugar into existing core terms, and the kernel checks what
it gives. "Parser" rules need only the table; "typed" rules need the types of their operands and
run in the typed elaboration (`Frontend/Sugar.lean`, with the rule in `Frontend/Elab/Data.lean`).

| # | construct | elaborates to | where |
|---|---|---|---|
| D1 | `data N … = …` | `type N[P, …]<'l, …> = T`, and for a monomorphic declaration a `shape N_C` per block | parser (table), sugar (in place) |
| D2 | `box A`, a field's type | `ref ⟦A⟧` | parser |
| D3 | a recursive declaration, a group | `μX. S`, the single-root rule; a block's fields cells | parser |
| E1 | `C`, `C(e₁, …, eₖ)` | `inj_i (payload)`, `roll`ed when `N` is a `μ` (its root), ascribed `: N` when `N` has no parameters; the payload `()`, `e₁`, or `(e₁, (…, eₖ))` | parser |
| E2 | `box C(e₁, …)` | for a block, `inj_i (alloc_s[N_C] (payload))` (a generic declaration's block is `(alloc(e₁), (…, alloc(eₖ)))`, the leafwise form `alloc_s` is, §5); for any other constructor, `alloc(⟦C(e₁, …)⟧)` | parser |
| E3 | `C(…)` of a block, without `box` | refused: "`C` builds a block, one cell per field: allocate it with `box C(…)`" (typed elaboration §5.3's reassembly from cells is not provided, *Not provided*) | parser |
| E4 | `N { f: e, … }`, `box N { … }` | E1/E2 with the fields in declaration order; each field once, all of them; when the written order differs, the values are bound in the written order first | parser |
| E5 | `e.f` | a field of a one-constructor declaration, by the receiver's type (*Fields*) | typed |
| E6 | `x.f = e;` | `modify &mut x { r -> … }` (`x` a `let mut`), `modify x { r -> … }` otherwise: `r`'s fields bound, `e` with `x.g` read as `r`'s field `g`, the record rebuilt with `f`'s new value; the old one is dropped (§12) | parser, typed |
| M1 | `match e { p₁ -> M₁ \| … }` | a decision tree (*Match compilation*) | parser |
| M2 | `match (e₁, …, eₙ) { (p₁, …, pₙ) -> M \| … }` | M1 over the columns `e₁ … eₙ`, each bound once, no pair built | parser |
| M3 | `let p = e; N` with a constructor pattern | M1 with one arm | parser |
| M4 | the arms of M1–M3 | reports: refused when not exhaustive or when an arm is never reached | parser |

The constructors of `N` with `n` constructors inject as the summands of their ⊕: `inj₁ v = inl v`,
`inj_i v = inr (inj_{i-1} v)`, the last `inr^{n-1} v`. A match's `case` is the same spine.

`match` with exactly the two arms `inl p | inr q` of patterns without constructors is the form of
draft 0, unchanged; every other `match` is M1.

### Patterns

    p ::= x | _ | () | (p, …) | C | C(p, …) | box C(p, …) | N { f: p, … } | N { f, … }
        | n | u8[n] | 'c' | true | false | inl p | inr p

`N { f, … }` is `N { f: f, … }`; a field left out of a record pattern is `_`. An integer, a byte
and a character literal match by `==`; `true` and `false` are `bool`'s two constructors (`1 + 1`,
§5.4 of typed elaboration: `inl ()` is false); `inl` and `inr` are a sum's.

**What a constructor pattern binds** (typed elaboration §5.3, `docs/data-declarations.md` §6.11):

- `C(p, …)` of a constructor that is not a block binds the payload's components, as `let`
  destructures them: values on an owned scrutinee, views on a view (§5, `Imm̲` fieldwise);
- `C(x, …)` of a block binds the cells, `ref A` on an owned scrutinee, and on a view the cells'
  views, `imm 'x A`;
- `box C(p, …)` of a block frees the block (`free` of each cell, the leafwise `free_s`) and
  matches the values; a nested pattern under a block's cell needs it.

### Match compilation (§11.1 A4)

The compiler is Maranget's (*Compiling Pattern Matching to Good Decision Trees*, ML Workshop
2008; *Warnings for pattern matching*, JFP 17(3), 2007): `Frontend/Elab/Data.lean`, `compile`,
`useful`. A clause matrix `P → A` has a row per arm and a column per occurrence (a variable of
the generated code), and

- **a row of wildcards first**: its arm, with each variable pattern bound to its occurrence;
- **otherwise** the leftmost column whose first row is not a wildcard is tested:
  - a constructor column of `N` (or `bool`, or a sum): `case (unroll o)` (`case o` when `N` is not a
    `μ`) along `N`'s ⊕ spine, one arm per constructor, each with the matrix specialised to it and
    the payload's components bound to fresh occurrences; a constructor no row names takes the
    default matrix (the rows with a wildcard there);
  - a tuple column: `let (o₁, o₂) = o`, and the matrix specialised;
  - a literal column: `if o == l { … } else { … }` per literal, in the order of first
    appearance, the default matrix last.

An arm reached on several paths is elaborated once per path. **Exhaustiveness**: the vector of
wildcards must not be useful after the last row (`useful P (_, …)`); otherwise the match is
refused: "this `match` is not exhaustive: `<p>` is not matched", `<p>` a witness built by
`useful`. **Redundancy**: an arm `pᵢ` not useful after the rows before it is refused: "this arm is
never reached: the arms before it match everything it matches". A literal column is never
complete; a column of wildcards only is matched by the default matrix. The compiler needs the
constructors of each column, which the constructor names give: no type.

### Fields

`e.f` names the field `f` of a one-constructor declaration with a field so named
(`Data.fieldCands`: each such declaration in scope, with its fields' names, the field's index and
whether it is a `μ`). The receiver's type chooses (`Sugar.resolveField`): a declaration fits when
its fields fit the record type's components and the record type matches the declaration's named
type with its parameters placeholders (`Elab/Match.lean`'s first-order matching, as a generic
call's); the declarations that fit must agree on the field's place, or the access is refused as
ambiguous, "ascribe the record". A block's fields are cells, read by matching the block. A field's
name may be a word the core reserves (`val`, `free`, `input`): after a `.` and before a `:` it is a
field's. The read is a typed rule
(`Sugar.fieldRead`), by the receiver's type:

| receiver | `e.f` | |
|---|---|---|
| owned, persistent (§10) | `run (let (x₀, (…, x_{k-1})) = e; return x_j)`, unrolled first when the declaration is a `μ` | `e` stays usable |
| `imm 'a N`, `N` persistent | the record copied out, `*e` (§36's load at the identity), and projected | the borrow is used |
| `imm 'a N`, otherwise | `withload` around the projection of its view, the field's view the result: the field persistent | the borrow is used |
| `mut 'a N`, at a binding `let y = x.f;` | `withswap` whose body takes the record apart and answers it rebuilt and the field: the field persistent | `x` rebound by the lend |
| owned, not persistent, at a binding `let y = x.f;` | the value taken apart and put back in place, as `modify` runs on a `let mut` value (§41): `run (let (r, u) = (&x, ()); …)` answering the record rebuilt and the field, the field persistent | `x` rebound by the lend |
| owned, not persistent, any other expression | the projection, which consumes it | |

At a binding `let y = x.f;` the parser gives the read the place `&x` (it is a write of a `let mut`
`x`, §41's R2); a persistent receiver drops it. Elsewhere a `mut` borrow, or a variable that is
not persistent, is refused: "`.f` reads a field of a `mut` borrow (or: of a value that is not
persistent): bind it, `let y = x.f;`, which lends the place for the read". `x.f = e` (E6) is
`modify`'s lend (§41's rule table: it writes `x`); its body takes the record `r` apart into `r_g`
for each field `g`, `x.g` in `e` is `r_g`, and the record is rebuilt with `e` at `f`. When the
declarations with a field `f` agree on its place, the parser takes the record apart, so that the
passes before the typed one (effects, §18) see `r_g` bound; otherwise the typed rule does, after
the receiver's type chooses (`VSugar.update`, printed `(r).{f = e}`). No rule decides an alias, a lend's extent or an escape: each lend is lexical, the
statement's, and the kernel checks it.

### Folds: unordered positions (§11.1 A1)

A fold (§6) promises no order between its recursive positions. Allocation order is not output,
and a fold's algebra is `F_∅`, so no result observes the order. The counts the gate records
(`corpus/counts.expected`) are those of the sequential order. This keeps parallel folds open.

### The library

`lib/prelude.bc` declares `data Option[T] = Some(T) | None`, which is `T + 1` with `Some` the
`inl` (the convention of §17's fillers and of `map_get`), and `data Vec[T] = Vec(buf T)`, a
newtype, so `Vec[T]` is `buf T` and the buffer library's functions apply to it. The prelude's
declarations are in every program's table; a program whose types name `Option` or `Vec` gets the
`type` declaration.

### No automatic boxing (§11.1 A7)

Not built in this entry. A declared type's recursion is boxed as written (blocks and `box`), and
the backend's one box a node (§35) finds nothing to add to it. For a recursive type written in
core, removing the rule makes its layout infinite, so every such program must write its boxes:
41 compiled programs of the corpus and the benchmarks, through `lib/list.bc`, `lib/async.bc`,
`lib/io.bc` and `lib/adapters.bc` (`docs/expressiveness-probes/zero-cost/data/a7-programs.txt`).
Written with the kernel's forms today, their counts rise or they are refused:

- a child cell each, `μX. 1 ⊕ (ref X ⊗ (A ⊗ ref X))`, is two objects a node and one an empty child
  where the rule boxes the sum's payload, one object a node (`rec-tree`: 254 where it is 127);
- the payload in one cell, `μX. 1 ⊕ ref (X ⊗ (A ⊗ X))`, keeps the count, but `ref` of a type that
  is not `X` is outside §6's `FShape`, so the type has no fold and no destructor (§12), and a
  program that drops one implicitly is refused;
- a block, `box Node(…)`, is allocated cell by cell (*Open*): three objects a node.

So A7 waits for a block to be lowered as one object (N1, layouts from types): the block form is in
`FShape`, has its destructor, and is then one object a node, the rule's count.

### Programs

| program | what it shows | answer |
|---|---|---|
| `corpus/data-box-tree.bc` | a tree declared with `data`, built with `box Node(…)`, summed by a recursive match whose `box` pattern frees each node | `i32[6]`, `live 0` |
| `corpus/data-particles.bc` | T09: particles as records in an array, their fields updated and read through each slot's `mut` borrow, read through the `imm` borrows of a `for` | `10 92 55`, `i32[11]` |
| `corpus/data-turnstile.bc` | T07: a state machine whose step is a match over two columns, a variant and a byte | `Locked 3 2 1` |
| `corpus/data-config.bc` | T11: a record with a string field updated field by field in a loop's match arms, then read; a variant with views of the input; `let Cfg { title } = cfg;` (M3) | `demo`, `((i32[80], (i32[50], inr ())), (i32[4000], i32[1]))` |
| `corpus/data-group.bc` | the single-root rule: `Expr` and `Bind`, rooted at `Expr` | `i32[17]` |
| `corpus/data-option.bc` | the prelude's `Option` and `Vec`; the generic `List[T]` and `Pair[A, B]` | `i32[30]` |
| `corpus/fail/data-no-box.bc` | a block built without `box` | refused, asking for `box` |
| `corpus/fail/data-not-exhaustive.bc`, `data-not-exhaustive-nested.bc` | matches missing a constructor, one over two columns with a nested pattern | refused, with the witness |
| `corpus/fail/data-redundant.bc` | an arm after a wildcard | refused |
| `corpus/reject/data-field-box.bc` | a recursive field under another type | refused, asking for `box` |
| `corpus/reject/data-no-root.bc` | mutual recursion with no member on every cycle | refused |
| `corpus/pending/data-fold-block.bc` | the tree summed through a borrow by a fold block | pending on §11.1 A2 |

Each rule is pinned beside its elaboration written by hand (`scripts/check-sugar.sh`):
`corpus/sugar/data-forms.bc` and `data-update.bc` beside core forms, and `data-box-tree`,
`data-particles`, `data-turnstile` and `data-config` beside a surface program with no declaration
(`corpus/sugar/<name>.lowered.bc`, `-- lowers: corpus/<name>.bc`), which must erase to the same
term.

T10 has no declaration: its form as written is tuple assignment and `let (mut a, mut b)`,
`let mut` sugar outside this entry (#626, #632).

### Baseline

No change to `CDerives`, `Core/`, `Paper/`, `Support/`, the relation, the machine or the checker.
Every corpus program that was accepted elaborates as it did: its goldens, exit status,
`corpus/counts.expected`, `kernel-counts.expected` and `cells.expected` are unchanged; new
programs get rows.

### Not provided

- **Nominal identity.** The elaborator types a declared type by its structure (a `type`
  abbreviation): two transparent declarations of one structure are interchangeable, and a field
  is chosen by the receiver's structure (*Fields*). Nominal identity in the elaborator's types, which decision 1
  asks for, comes with faces (U2), where resolution by the receiver's type needs it; until then a
  newtype (`data Id = Id(i32)`) is its field's type to the checker.
- **A match on an `imm` borrow.** Load it first, `borrow imm *b { v -> match v { … } }`. A
  recursion over a borrowed recursive value is §6's fold (the `fold` block is A2): a load's view
  is at a lifetime shorter than the borrow's, and a group's members recurse at their own
  lifetimes (§20).
- **A generic block's construction** needs its fields' types from the arguments (`alloc(e)`): an
  injection without its type is to be ascribed.
- Field paths through several records (`d.spec.replicas = …`), update syntax `N { f: e, ..r }`,
  and variant payloads updated in place (#19).
- **A block reassembled from its cells** without `box` (typed elaboration §5.3's `Node(c₁, c₂,
  c₃)`, for `fold_reuse`): every block written without `box` is refused, asking for it. It comes
  with the `fold` block (A2), which binds the emptied cells.
- **A field read through a `mut` borrow inside an expression**, and an implicit copy of an `imm`
  borrow so that it can be read twice (#58): a read through a borrow is a binding of its own, and
  it uses an `imm` borrow.

### Open

- **One box a node** (§35) is still the backend's rule for recursive types written in core
  (*No automatic boxing*).
- **A block is allocated cell by cell** by the backend (§5 *Open*, block provenance): `box Node(l,
  v, r)` is three objects where Rust's `Box<Node>` is one (a tree of depth 7: 381 where `rec-tree`
  is 127). The excess is the lowering's: N1.
- **A record read out of an array or through a borrow is copied whole**, and an update through a
  `mut` borrow is a `withswap` of the whole record: loads and stores where Rust touches one field
  (the ports of `docs/expressiveness-probes/zero-cost/data/`, L-1: N2). The allocations are the
  probes'.

---

## 43. Entry 42 — `let mut` as a frame's slots, behind a flag (#632, a prototype)

### Motivation

#632 step 2. `experiments/Frames` proves the frame rules (`FDerives`, 13 derived rules over
`CDerives`): each rule's elaboration is a `CDerives` derivation (`FDerives.elab`) and hands back
the slots it is given on every run (`accounting`). This entry tries them on the surface, behind
`BCC_FRAMES=1` (`BCC_FRAMES_LIB=thread` keeps the library modules' `let mut`s on §41), so that
what they resolve and what they cost can be measured beside §41's threading and #626's place
model (`docs/research/frames-with-exits.md` §13). Nothing changes without the flag.

### The rules at the surface

`Frontend/Elab/Frames.lean`, with hooks in `Frontend/Parser.lean`:

| construct | under the flag |
|---|---|
| `let mut x = e; N` | the rule `new`: the cell `alloc(e)` is the slot `x`; at `N`'s normal end the cell is freed and its last content read where `N`'s value reads `x`; at any other exit the cell is a linear value in scope, destroyed by §12 |
| a read of `x` | the rule `use`: a load `*x`, made before the construct that evaluates the read (Core code sees no slot); in a borrow block's, a `with`'s or a writing `run`'s body, where it is |
| `x = e`, `x <- M`, `let (x, q) = f(…, x, …)` | the rule `use` with `withswap`: `modify &mut x { o -> … }`; a value that does not read `x` is evaluated first |
| `&mut x`, `&x` at a call | the rule `use`: the content swapped out, lent by the value's own rules, swapped back |
| `borrow k x { … }` | the content swapped out and borrowed by the value's own rules (an array as a family; any other value through a cell allocated for it) |
| `if`, `match`, `case` (a statement or a head), `x <- M` | the rules `case` and `bind`: the arms hand back the slots they mention, and the binding takes them apart |
| a borrow block's, a `with`'s, a `run`'s body that uses slots | the rule `lend`: the body hands back the slots it uses beside its result |
| the loops | §14's and §16's loops, the cells they use in their state (`Π ⊗ S₀`) |
| a closure that writes a slot | refused: a frame-typed block (`callBlock`), generic in its slots at its callee (D4), is not built |

For a slot, §41's R2 write sets, R3's hand-on, `mutCap` and `escapingWriter` do not run: a slot
is no `let mut` variable to them.

### Baseline

No change to `CDerives`, the relation, the machine or the checker. Without the flag the parser
and the elaboration are as they were: every corpus program's erasure, run output, goldens and
counts are unchanged.

### Open

The measured refusals and costs (`docs/research/frames-with-exits.md` §13): a linear content moved
out of a slot (no holes), a view read twice, effects inside a use (a swap's callback is pure),
blocks generic in their slots (D4), and the cells' allocations (#626's L1/L2).

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
`Frontend/Elab/LoopLend.lean` and `Core/Totality.lean`; each div body is one state machine.
Its effect `Div` is in the kernel (`Core/DivDefs.lean` to `Core/DivRuntime.lean`, the rules
`iterate`, `divFuel`, `reify` and `effHandleT` of `CDerives`), and the backend replaces `iterate`
by its fixed point (`Backend/Clos/Convert.lean`); the frontend does not elaborate to it yet. Entry 14 (§15) is implemented in `lib/yield.bc`, `lib/adapters.bc`,
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

Entry 30 (§31) is implemented in `Frontend/Elab/Effects.lean` (`RGroup.tps`, `RGroup.lives`,
`defineGroup`, `groupCopy`, `deepCopy`, `liftCalls`, `Env.clashes`), `Frontend/Sugar.lean`
(`genericCall`, `matchC`, `pureArrow`, `argOf`, `makeInst`, `elabDecl`) and `lib/list.bc`, with no
change to `CDerives`, `Core/`, `Paper/`, `Support/` or `Backend/`.

Entry 31 (§32) is implemented in `Frontend/Elab/Effects.lean` (`Blk`, `Cap.blk`, `Cap.canon`,
`withBlkCaps`, `Blk.inCopy`, `blockArgs`, `blockCall`, `blockParamCall`, `HInfo.lives`),
`Frontend/Sugar.lean`
(`hndCtlC` at a handler's lifetimes; a closure argument typed at its parameter's type),
`Frontend/Elab/RenameLife.lean` (`substLives`), `Frontend/Syntax.lean`, `Frontend/Parser.lean`
and `Frontend/Print.lean` (`CHandler.lps`), and `lib/async.bc`, with no change to `CDerives`,
`Core/`, `Paper/`, `Support/`, the checker or `Backend/`.

Entry 32 (§33) is implemented in `Frontend/Syntax.lean` (`VTy.rowed`, `VTy.rowEffs`,
`VSugar.pipe`), `Frontend/Lexer.lean` and `Frontend/Parser.lean` (`|>` in `opOf` and `opsLoop`,
a provided row in `rtyAtom`),
`Frontend/Print.lean`, `Frontend/Elab/Effects.lean` (`Env.comps`, `compParamsOf`, `Blk.prov`,
`etaArgs`, `blockArgs`, `blockCall`, `blockParamCall`, `copyOf`'s ports, `Cx.portIn`, `withCtl`,
`resolvePipes`, `pipeStage`) and `Frontend/Sugar.lean` (an annotated binding at the row), with no
change to `CDerives`, `Core/`, `Paper/`, `Support/`, the checker or `Backend/`.

Entry 33 (§34) is implemented in `lib/sys.bc`, `lib/wasi.bc`, `lib/io.bc` and `lib/textio.bc`;
`Frontend/Syntax.lean`, `Frontend/Parser.lean` and `Frontend/Print.lean` (`HostKind`,
`OpDecl.lives`, `Decl.handler`'s lent state); `Frontend/Elab/Effects.lean` (`HSig.lent`,
`HSig.cell`, `clauseDef`, `opCall` on a cell, `platformEffects`, `platformMain`, `Env.gives`,
`Cx.givenC`, a borrow block that lends its tasks' capabilities, `withCtl`'s given capabilities,
`hide`); `Frontend/Sugar.lean` (the I/O library included first, `capNames`, `mainLife`);
`Frontend/Check/Externs.lean` (the clock's and the arguments' externs and harness);
`Core/Opaque.lean` and `Core/Stdio.lean` (`Opaque.clock`, `Opaque.args`, their models and
proofs); `Backend/` (`IOOp.clockNow`, `IOOp.clockSleep`, the arguments' stream at every stage,
the WASI runtime's clock and arguments, `bcc trusted` at the externs `main` reaches, and #485's
and #486's fixes in `Backend/Clos/Capture.lean` and `Backend/Driver.lean`), with no change to
`CDerives`, the relation, the machine, `Paper/` or `Support/`.

Entry 35 (§36) is implemented in `Frontend/Syntax.lean`, `Frontend/Lexer.lean`,
`Frontend/Parser.lean` and `Frontend/Print.lean` (`Decl.poly`), `Frontend/Sugar.lean` (`polyDecls`,
`PolyTab`, `polyCheck`, `polySelect`, `polyInst`, `dropPhantoms`, the family's call in
`genericCall`, an operator's case in `surfV`, `borrow imm *g`, a record lent fieldwise, `lendCall`
at several lifetime parameters), and `lib/key.bc` and `lib/map.bc`, with no change to `CDerives`,
`Core/`, `Paper/`, `Support/`, the checker or `Backend/`.

Entry 34 (§35) is implemented in `Backend/` alone: `Backend/Clos/Convert.lean` (`markScoped`,
`staticWord`), `Backend/Clos/Syntax.lean` (`Op.scopedAlloc`, `Op.scopedFree`, `Op.staticCell`,
`Prog.suspendedScopes`), `Backend/Clos/Capture.lean` (`crossedScopes`), `Backend/Clos/Types.lean`
(`sumBoxes`), `Backend/Flat/` (`frameScopes`, `Exp.slot`, `Stmt.unslot`, `Fn.frame`, the
interpreter's frames) and `Backend/Wasm/` (`$sp`, the stack, `lowerFn`), with the library's
comments in `lib/buf.bc`, `lib/text.bc` and `lib/rec.bc`; no change to `CDerives`, `Core/`,
`Paper/`, `Support/`, the checker or the elaboration.

Entry 35 (§36) is implemented: `Width.f32`/`f64`, `IntLit.f32`/`f64` and the float `HostOp`s in
`Support/Syntax/Integers.lean`; the host's float functions and `Host.call` in
`Support/Dynamics/Host.lean`, `wasmHost`'s in `Support/Dynamics/Floats.lean`; `hostArg`,
`hostRes` and `host_call_sound` in `Core/Integers.lean` (and the host's answers closed and
raise-free, `Core/Closed.lean`, `Core/RaiseNames.lean`); the lexer, parser, printer, operator
dispatch and literal rounding in `Frontend/` (`Frontend/FloatLit.lean`); every stage of
`Backend/` (`Flat/Lower.lean`'s `hostVals`, `Wasm/Lower.lean` reinterprets); and
`lib/float.bc`. No change to `CDerives`, the relation, the machine's rules or the checker's rules.

Entry 37 (§38) is implemented in `Frontend/Elab/Instances.lean` (the table of type arguments),
`Frontend/Elab/Match.lean` (the matching, moved from `Frontend/Sugar.lean`),
`Frontend/Elab/Effects.lean` (`Inst.name`, `Site.slot`, `Cap.slot`, `Env.addInst`,
`Env.withoutInst`, `Env.handledArgs`, `Env.callRowAt`, `Cx.serve`, `Cx.capFor`, `Cx.capAt`,
`slotsOf`, `Env.slotOf`, `Env.checkWritten`, `Env.settle`, a stateful handler's row in `withCtl`),
`Frontend/Elab/Subst.lean` (`HInfo.subst`), `Frontend/Sugar.lean` (several sites in `forData`),
and `Frontend/Syntax.lean`, `Frontend/Parser.lean` and `Frontend/Print.lean` (`VSugar.handle`'s
name, `VSugar.named`, `Mark.row`'s names), with no change to `CDerives`, `Core/`, `Paper/`,
`Support/`, the checker or `Backend/`.

Entry 38 (§39) is implemented in `lib/arith.bc` (`DivError`, `div_euclid`, `rem_euclid`,
`main_div_error`); `Frontend/Syntax.lean`, `Frontend/Lexer.lean` and `Frontend/Parser.lean`
(`SurfOp.rem`, `%`, `(%)`, `VSugar.checked`); `Frontend/Elab/Instances.lean` (`argTy` at
operators, `divCanFail`, `safeDivisor`, `Found`); `Frontend/Elab/Divisions.lean` (the rewrite);
`Frontend/Elab/Effects.lean` (`divMain`, `splitDiv`, `divLib`, `platform`, a `with`'s row with its
clauses' answering effects, a written row's check); `Frontend/Sugar.lean` (`surfOp`, `divCase`,
`divUnchecked`, `divChecked`, `fuseChecked`, the libraries brought in); and `Backend/`
(`Output.status` and `reportExit` at every stage, `Clos.Prog.exits`, `Flat.Stmt.status`, the
runtime's `$exit`, `divTest`, the constant locals and the fused `case` of the flat IR), with the
harness's `<name>.status`; no change to `CDerives`, `Core/`, `Paper/`, `Support/` or the checker's
rules.

§8 and §37 as restated in 0.70 are implemented in `Support/Dynamics/Floats.lean` (`NaNs`, every
float operation at a resolution, `NaNEq` and its lemmas), `Support/Dynamics/Host.lean`
(`Prim`, `wasmHostAt`, `Host.Conforms`, `wasmHostAt_conforms`, `wasmHost_conforms`),
`Backend/Clos/Interp.lean` (`closHost`), `Backend/Flat/Interp.lean` (`flatHost`) and
`Backend/Flat/Lower.lean` (`hostVals` without the NaN test); no change to `CDerives`, the relation,
the machine, `Core/`, `Paper/` or the checker.

§3's typed term is implemented in `Frontend/Check/TExpr.lean` (`TExpr`, `TInfo`, `TExpr.erase`,
`TExpr.isLam`, `TExpr.children`) and `Frontend/Check/TDerives.lean` (`TDerivesAt`, `TDerivesP`,
`TDerivesAt.erase`, `TDerivesP.erase`, `TDerivesAt.toP`, `jdg_eq`), both generated by
`scripts/gen-pin.py` from `Core/Tied.lean` and `Core/PinDerives.lean`; `Frontend/Check/TTied.lean`
(`TTied`, one builder per rule, `TTied.tied`); `Frontend/Check/TFacts.lean`; the checker's builders
(`Frontend/Check/Rules.lean`, `Consts.lean`, `Steps.lean`, `Pin.lean`, `Checker.lean`), which build
each node beside its derivation; `Checked.t` and `Checked.e := t.erase`, with `checkProgram_typed`,
`checkProgram_typedAt` and every theorem of `Frontend/Check/Program.lean` at `c.t.erase`; and
§10's check on the typed terms (`Frontend/Check/Copies.lean`, the core form `Val.clone`). No
change to `CDerives`, `Core/`, the relation, the machine, a rule of the checker, or any program's
erasure, output, goldens or counts.

§3's split masks and §5's cell classes are implemented in `Frontend/Check/Masks.lean` (`Masks`,
`SplitMasks`, `SplitMasks.both_iff`, `SplitMasks.both_persistent`, `SplitMasks.ins`), the generated
typed rules (`scripts/gen-pin.py`: the `u.Rel` premise at a split, `TExpr.masks?`,
`TDerivesAt.split_masks`, `TDerivesP.split_masks`, `TDerivesP.copies`), `Frontend/Check/Fam.lean`
(`split_lemma`, `Fam.split`, `Fam.mapB`), the builders at a split (`Rules.lean`, `TTied.lean`,
`Weaken.lean`'s `splitP_route`), §10's check on the masks (`Frontend/Check/Copies.lean`),
`Frontend/Check/Cells.lean` (`VTy.eraseLife`, `TExpr.cells`, `cellClasses`, `cellsOkB_sound`),
`Checked.cells` and `Checked.cells_closed`, `Backend/Cells.lean` (`bcc-counts --cells`) and
`scripts/check-cells.sh`. No change to `CDerives`, `Core/`, the relation, the machine, or any
program's erasure, output, goldens or counts.

§3's marked derived nodes, typed `[let-poly]`, `[handle]` at tail clauses and `reify`, the lint,
the lifetime weakening and the key table are implemented in `scripts/gen-pin.py` (`DERIVED`,
`lint_texpr`, the `TLife` cases) and its templates (`scripts/pin/TExpr.tmpl.lean`:
`divLitB`, `safeDivB`, `walkB`, `selfCallB`, `lendCellB`, `Expr.pairL`, `Expr.toVal`,
`Expr.letBody`; `TDerives.tmpl.lean`; `TLife.tmpl.lean`: `LeΔ`, `ExtΔ`, `TExpr.domFree`,
`TExpr.reAb`, `weakenΔ`), `Frontend/Check/Derived.lean`, `Frontend/Check/Rules.lean`
(`rMarked`), `Frontend/Check/Checker.lean` (`DefEntry.lift?`), the elaborator's marks
(`Frontend/Sugar.lean`: `divUnchecked`, `forData`, `lendBorrow` and the borrow block of a cell;
`Frontend/Elab/Effects.lean`: `memberCall`) and keys (`DefKey`, `recordKey`, `Origin.defKey`,
`Elaborated.keys`). No change to `CDerives`, `Core/`, the relation, the machine, or any program's
erasure, run output, goldens or counts; `bcc check` reports a `def` with type parameters as
`checked once per instance`.

§3's derived nodes and `use` nodes are implemented in the templates of `scripts/gen-pin.py`
(`scripts/pin/TExpr.tmpl.lean`, `TDerives.tmpl.lean`: the nodes, `litFnE`, their rules and
projections), `Frontend/Check/TShift.lean` (`TExpr.shift`, `AbsF`, `TExpr.absF`,
`TExpr.absF_shift`), `Frontend/Check/Weaken.lean` (`TDerivesP.weaken`, `TDerivesAt.weaken`,
`TDerivesAt.use_projects`, `TDerivesP.use_projects`), `Frontend/Check/TTied.lean` (`TTied.use`,
`TTied.weaken`, `TTied.litFn`), `Frontend/Check/Rules.lean` (`rUse`, `rUseAt`, `rLitFn`), the
checker's cache of checked bodies (`DefEntry`, `CheckM`, `useDef`, `Frontend/Check/Checker.lean`)
and the core form `Val.mark` (`Frontend/Syntax.lean`, printed as the value it marks). No change to
`CDerives`, `Core/`, the relation, the machine, or any program's erasure, output, goldens or
counts.

Entry 39 (§40) is implemented in `Backend/Native/Lower.lean` (the LLVM IR), `Backend/Native/Runtime.lean`
(the runtime), `Backend/Native/Tests.lean` (`bcc hostops`, `bcc tailcalls`), `Backend/Driver.lean`
(`compileLL`, `buildNative`), `Frontend/Main.lean` and `Backend/Counts.lean` (the commands),
`Op.dataAddr` and `Exp.data` in the closure IR and the flat IR, and `scripts/compile-native.sh`;
no change to `CDerives`, `Core/`, `Paper/`, `Support/`, the frontend or the checker.

Entry 40 (§41) is implemented in `Frontend/Parser.lean` (R1: `bindName`, `lookName`,
`bindOrAssign`, `rebindOf?`, `renamesOf`, `Error.renderIn`; R2: `frame`, `notePlaceWrite`; R3:
`handOn`, `joinBind`, `handArms`, `bindForm`, `writesOf`, `checkRun`, `Val.handsBack`),
`Frontend/Elab/Hygiene.lean` (`Decl.renameDecls`), `Frontend/Elab/Effects.lean` (`mutCap`,
`escapingWriter`), `Frontend/Sugar.lean` (a program's declarations shadow a module's;
`modifyBody`, `TCx.tyCL`) and `scripts/mut-combos.py`; no change to `CDerives`, `Core/`, `Paper/`,
`Support/` or the checker. Its binder identity is `Val.copyOf?` (`Frontend/Syntax.lean`),
`Frontend/Elab/LoopLend.lean` (`Binding.of?`, `spineAliases`, `Env.walk`), `Frontend/Elab/Effects.lean`
(`Cx.copy`, `rowC`, `unboxesC`, `forOverParam`, `capKey`, `blockKeys`), `Frontend/Sugar.lean`
(`termParts`), `Frontend/Elab/Hygiene.lean` (a control handler's code), `Frontend/Parser.lean`
(`generatedName`, `pushBinder`, `resolutionOf`, `unrename`), `Frontend/Main.lean` (`bcc alpha`)
and `scripts/alpha-check.py`.

---

## Changelog

- **0.91** (2026-10-20) — §43 (#632 step 2): `let mut` as a frame's slots, behind `BCC_FRAMES=1`
  (a prototype, `Frontend/Elab/Frames.lean`). No change without the flag; no change to
  `CDerives`, the relation, the machine or the checker.
- **0.90** (2026-10-20) — §42 (#593, unit U1 of `docs/data-declarations.md`): `data`
  declarations, records and variants, monomorphic and generic, transparent; recursion under a
  written `box` (blocks); the single-root rule; constructors, record literals, fields and field
  update through `modify`; `match` compiled to decision trees with exhaustiveness and
  redundancy reports; `Option` and `Vec` in the prelude; a fold's positions are unordered (A1).
  No change to `CDerives`, the relation, the machine or the checker.
- **0.89** (2026-10-20) — §19, *The clause's names in the continuation* (#610): condition 2 of the
  direct call of a tail-resumptive clause is over the names the clause's own code performs or
  raises (`Expr.own`, `handlerNames`), not over its row; over its row where it may run code it
  does not hold. `Fo`, the first-order invariant, closed under substitution and every step from
  any memory; `tail_work_names`: a tail-resumptive clause's work performs and raises only its
  names. `UnhandledNames`, `Checked.unhandledNames`; a bound per node stated
  (`Checked.FramesPerNode`). `bcc handled` prints each clause's names; `corpus/handled.expected`:
  `answers-two-types` 2.0 and `tree-map` 4.0 and 5.0 agree, every direct call of the corpus.
  No change to `CDerives`, the relation, the machine, a checker rule's acceptance, or any
  program's erasure, run output, goldens or counts.
- **0.88** (2026-10-20) — #618: each construct's rule emits the target's shape. §16: a step with
  no exit is `count_fold`'s, and a count from a literal in `[0, 2³¹)` is counted from it, the
  counter the element (`walkB` takes `count_fold`; `walk_fold_index_lt`, `countFold_runs`). §14:
  a point no move calls is its arm of the step, a move from the code before the first point is
  the machine at that state (no `io_mk`), and a value terminal finishes as `inl V`. §18: a call's
  binding is structured, so that a value that is one call's answer is the call, in tail position
  or bound to the binding's own name; a lone parameter is its function's binder. The backend's
  search for the fields that close a cycle enters it at a sum, so a list's box is at its
  recursive position whatever the node order. Six `let mut` target pairs are met and join
  `corpus/sugar/`, five targets corrected; clauses whose resume is in tail position are
  classified `tail` (`corpus/kinds.expected`); 13 programs' counts fall; no result changes.
- **0.87** (2026-10-20) — §41 (#617): binder identity. What the elaboration recognises by a binder
  (a borrow block's borrow over a loop, a block parameter, a port, a continuation, a layer's
  `call`, a div function's residual) it follows through copies (`Val.copyOf?`); a control
  handler's code has fresh names (#493's last program lands); a source binder spelt as a generated
  name is renamed; capability variables are one per effect and slot; a block's `let mut`
  capabilities key its copy by position. The renaming check (`bcc alpha`,
  `scripts/alpha-check.py`) is a gate step. T04 back to its original form; `lend-escape`'s witness
  changes; five new corpus programs. No kernel, `CDerives` or checker change.

- **0.86** (2026-10-19) — §41 (#613): a join's terminal value is handed on as it is, a loop turn's
  `()` is not bound, and `modify` of a `let mut` value runs its body in place rather than through a
  scoped cell. The elaborated core of the corpus changes shape (no result changes; three
  programs' loads and stores fall); `corpus/sugar/`'s core forms lose the bindings, and #611's
  `mut-heads` and `mut-modify` pairs join them, `mut-modify`'s target corrected to the in-place
  form.

- **0.85** (2026-10-19) — §41 (#613): R3, the boundary rule, and the rule table. A part that
  runs in another frame hands back what it writes (`handOn`): an arm, a binding's head, a borrow
  block, `modify` (whose body's writes were dropped), an answering handler's body and `run`
  (whose writes were dropped). A block that writes, given at a block parameter, takes the
  variables first and hands them back first at each call of the callee's copy, as §32's
  capabilities do (#586; the write was dropped). A closure that writes and is stored or
  returned, a `run` that writes inside an expression, a control handler's body that writes and a
  `for`'s `else` value that writes are refused by name. A lend or a borrow of a `let mut` place
  writes it (its write in an arm was dropped). Each declaration's `let mut`s are its own. The
  parser's joins are instances of one hand-on (`headOf`, `armOf`, `armIf`, `blockBody`,
  `joinArms`, `joinHead` and `bindHead` deleted). No kernel, `CDerives` or checker change.

- **0.84** (2026-10-19) — §41 (new, #613): `let mut`'s names resolved to their binders (R1) and
  its writes (R2). In a surface body a binder of a name in scope is a new variable with a fresh
  name, so threading never takes a shadowing `let` for the variable it shadows (#504 and its
  broader form, #493); `x <- M` on a `let mut` assigns it; `let (x, q) = f(…, x, …)` rebinds the
  place `x`; a program's declaration shadows an included module's (#590). Messages name binders
  as written. No kernel, `CDerives` or checker change; the programs whose answers change are
  listed in §41.

- **0.83** (2026-10-19) — §19, *The clause's names in the continuation* (#575): condition 2 of the
  direct call of a tail-resumptive clause is a checked fact. Each `handle` node records the frames
  its handled computation holds (`inside`), pinned by its typed rule; the program's flow record
  (`Checked.flows`) holds what may flow in a run of `main`. Run invariant: every handler frame a
  run reaches is of a handle node of the program (`Checked.frame_of_node`). Theorem: a row none
  of whose names the flow record may catch is unhandled in every continuation between a handler
  and an operation it catches (`Checked.unhandledIn`). `bcc handled`; `corpus/handled.expected`
  (`scripts/check-handled.sh`, a gate step). No change to `CDerives`, the relation, the machine, a
  checker rule's acceptance, or any program's erasure, run output, goldens or counts.
- **0.82** (2026-10-19) — §18, *Control effects*, and §19, *Clause kinds* (#574): the
  elaboration writes a handler site's clauses inline in its `handle` node,
  `handle_with[n]((V_r : T_r), (V_c : T_c)) M`, in place of binding them to variables first, so
  each handler's erasure is `hnd (n, (qs, (V_r, V_c))) e` where it was
  `(λhr. (λhc. hnd (n, (qs, (hr, hc))) e) V_c) V_r`. `handle_with` takes values; the checker
  types the pair as `[handle]`'s value form over persistent slots (`rEffHandle`, `valFormB`). The
  clause kinds read the node's own pair, through a `def`'s `use` node: `Env.vals` and the chase
  through it are gone; `classify_sound` keeps its statement, and `classifyHandler_sound` gives
  each kind's premise at the node's clause. The core programs that bound their clauses write them
  inline. §19, *Handler sites*: the record travels with the site's sugar to its node, with its types
  in the frame of the node's code (a generic stored generator's at the call's type arguments), the
  checker elaborates it to core types and checks its operations against the node's `E`
  (`siteOf_ops`); a counted loop's handler of a site's abortive operations has no record. No change
  to `CDerives`, the relation, the machine, a checker rule, or any program's run output, goldens or
  counts.
- **0.81** (2026-10-19) — The joins at `match`/`if` (0.16; typed elaboration §5.2) at the head of
  a binding (#581): in `let p = M; N`, `x <- M; N`, `x : A <- M; N` and `linear x <- M; N`, each
  terminal of `M` hands on the enclosing `let mut` variables `M` assigns beside its value, and
  they are rebound before `N`; a core `case` joins as a `match` does. Before, an assignment in an
  arm of a head was lost after the binding. No kernel, rule or checker change; no existing
  program's output, golden or count changes.

- **0.80** (2026-10-19) — §3 (#570): four marked derived nodes, `divLit` (§39), `walk` (§16),
  `selfCall` (§20) and `lendCell` (§35), each over its scheme's typed term, the first two with
  their facts about the run; no node holds an untyped term (`[let-poly]`, tail-clause `[handle]`
  and `reify` read them off their children), checked by `gen-pin.py --check`; a `def`'s body
  checked at one lifetime context is placed at a larger one by `weakenΔ` when it has no borrow and
  its type no binder; a `use` node records the elaborator's key of its `def`. `bcc check` reports
  a `def` with type parameters as `checked once per instance` (was `checked at each use`). No
  change to `CDerives`, `Core/`, the relation, the machine, or any program's erasure, run output,
  goldens or counts.
- **0.79** (2026-10-19) — §3, *What the checker returns* (#570): a node at a split carries both
  parts' use masks, and its typed rule relates them to the parts' contexts (`SplitMasks`), so the
  copy set of a split is its masks' (`TDerivesP.copies`), which §10's check reads; a binding's
  node records the names it binds. §5, *Cell classes* (new): the checker carries each allocation
  type's class, the types a cell of it may hold over its lifetime, closed under the typed term's
  swaps; `scripts/check-cells.sh` compares them with the layout types' cell widths. No change to
  `CDerives`, `Core/`, the relation, the machine, or any program's erasure, output, goldens or
  counts.
- **0.78** (2026-10-19) — §18, *Laws*: `TailResumes` has the right unit `(λx. R₀) X`, `R₀`
  answering `x`, and the `β`-step of a `let` of a closed value; `tail_resumes` reaches the resume
  under right-unit frames (`RetFrames`), which hand its answer on (`tail_resumes_answer`). §19,
  *Clause kinds* (#571): `TailResumesAt` and `TailLeaf` have the right unit, and `OnPaths` and
  `TailResumesAt` the alias `let k' = κ`; the classifier reads both (`tailLeafB`, `isVarB`), and
  `classify_sound` keeps its statement; a clause is read through `use` nodes at any depth. Reclassified: a named handler's `k(v)` in tail position
  (`once` → `tail`; `resume-or-cancel` where a path cancels, as `deadline`), and the BOXED-κ `log`
  of `lib/async.bc` (`stored` → `tail`). New: *The clause's names in the continuation*
  (`UnhandledIn`; the rows do not decide it, `unhandled_not_decided`). New: *Handler sites*: the
  elaboration's record of each site on its `handle` node (`HSite`), checked against the node;
  `bcc sites`. §39: the exit status is read from the site of `main_div_error`'s `handle` node, and
  `Checked.exits` is gone. No change to `CDerives`, the relation, the machine, a checker rule, or
  any program's erasure, compiled code, run output, goldens or counts; `bcc check`'s report of a
  handler site changes where its kinds do.
- **0.77** (2026-10-19) — §3, *Derived nodes* and *A `def` at its uses* (#560): a `def` is checked
  once per key and placed at each use by a `use` node, its derivation there by weakening with the
  live slots its absorption takes (`TDerivesAt.weaken`, `TDerivesP.weaken`); fixed schemes typed
  by a `Core/` lemma are derived nodes, replacing `scheme`; the elaborator marks a string
  literal's table (`Val.mark`), and the checker builds its derived node (§17). §11: a `def` that
  names an extern is checked once per key. No change to `CDerives`, `Core/`, the relation, the
  machine, or any program's erasure, `bcc check` output, goldens or counts.
- **0.76** (2026-10-18) — §19, *Clause kinds* (#561): at `[handle]` the checker classifies each
  operation's clause (abortive, tail-resumptive, tail-resumptive with state, resume or cancel,
  resume once, stored) from the typed term of the clauses' binding, and records the kinds with
  the qualifiers on the `handle` node; each kind gives its law's premise at the clause's erasure
  (`classify_sound`, `Core/ClauseKinds.lean`). §18, *Laws*: `TailResumes` runs through the body
  of `let x = e` too. §18, *Reports*: a handler site's operations are rendered from the checked
  kinds; the report channel among the elaboration's origins is typed (`Origin`), not tagged text.
  §3: the kinds are a field of the node the derivation does not constrain. The gate compares the
  kinds with the backend's lowering (`scripts/check-kinds.sh`, `corpus/kinds.expected`). §14:
  `effHandleT`'s clauses are an instance of the `tail` kind (`tailClause_premise`). No change
  to `CDerives`, the relation, the machine, a checker rule, or any program's erasure, output,
  goldens or counts.
- **0.75** (2026-10-18) — §14, *The effect `Div` in the kernel* (new, #563): `Div`, the reserved
  name `divEff` with `tick : 1 ↠^lin Next`, and the constants `iterate` (one machine step),
  `div_fuel` and `reify_res`, each a rule of `CDerives`. The relation at a row that holds `Div` is
  `cwp`, the greatest fixed point over segments with `Closing` (`effWp`). `ewp_frame_plain`,
  `ewp_frame_then` and `ewp_handle` are stated once at `opTable T ∨ Π`. `[handle]` around a
  computation that ticks is `effHandleT`, at clauses that resume `κ` in tail position (decision
  68); `effHandleV` and `effHandleVB` ask their rows not to hold `Div`. Finalisers are total
  (decision 69): `[then]`'s finaliser row does not hold `Div`, and the theorem is open.
  `fundamentalC`, `adequacyC` and `total_every_run` keep their statements; `divFuel_every_run`,
  `runtime_every_run`, and the kernel program `div-residual` (`3`, `live 0` at every stage). §19,
  *Divergence*: the greatest fixed point at a row that holds `Div` replaces "there is no second
  fixed point". The typed term (§3) has a generated node per new rule, `iterate`, `divFuel`, `reify`
  and `effHandleT`, each with its `TTied` builder. The backend replaces `iterate` by its fixed
  point (`expandIter`). The frontend
  writes no `Div`; every corpus output, golden and count is unchanged.
- **0.74** (2026-10-18) — §3, *What the checker returns: the typed term* (#559): the checker
  returns a typed term with one node per rule application and a generated typed derivation that
  projects to `CDerivesAt`/`CDerivesP`; the checked term is its erasure. §10: `clone(x)` is a core
  form, recorded on its node, and the check of implicit copies reads the typed terms; the typed
  IR inferred on core after the sugar, and `bcc tir`, are removed. §39: `main`'s exit status is on
  the checked `main` (`Checked.exits`). No change to `CDerives`, the relation, the machine, a
  checker rule, or any program's erasure, output, goldens or counts.
- **0.73** (2026-10-18) — §39, *The exit status* (#558): the elaboration's record that `main` is
  served `Fail[DivError]` is a field of the elaborated program (`Elaborated.exits`), not an
  origin string, and the checker's `Report` carries the elaborated program it checked
  (`Report.el`). The backend reads `main`'s program and `exits` from it and does not elaborate
  the program a second time. No change to `CDerives`, the relation, the checker's rules, a kernel
  program, or any program's output, goldens or counts.
- **0.72** (2026-10-18) — §19, *Lowering* (#544): a clause is tail-resumptive when every path
  through it ends in one resume of `κ` in tail position, each arm of a `case` with its own, not
  only when its last call is the resume. §18, *Laws*: the resume commutes out of the arms
  (`tail_resumes`, `Core/Handlers.lean`). `corpus/for-yield-branch.bc`.
- **0.71** (2026-10-17) — §40 (new, #529): the native target. `bcc compile --target native`
  prints LLVM IR from the flat IR, `bcc run --native` builds it with `clang` beside a C runtime
  (the allocator with the Wasm runtime's semantics, the POSIX platform of §11 and §34) and runs
  it. Tail calls are `musttail` between functions of one prototype per tail-call class; several results a struct by value, through a
  pointer when wider than the target's result registers; words are real pointers and the data a
  global (`Op.dataAddr`, `Exp.data`). No host operation is undefined or poison where SPEC gives
  an answer. `scripts/compile-native.sh` joins the gate: the corpus, the kernel programs and
  every host operation native against the flat IR, counts agreeing, tail-call loops in 64 KiB of
  stack. No change to `CDerives`, the relation, a kernel program, or any program's output, WAT
  or counts.

- **0.70** (2026-10-17) — §8 and §37 restated (#528, decision 66): the integer and float
  operations are the language's own, defined on bit-vectors as `wasmHost` computes them; Wasm and
  native code implement them. A shift or rotation masks its amount (the behaviour already; the
  wording is new). The sign and payload of a NaN an arithmetic float operation answers are
  unspecified (Rust RFC 3514), amending 0.67's canonicalisation: `Host.Conforms` is the set of
  allowed hosts, `wasmHostAt r` conforms at every resolution `r` and `wasmHost` (canonical) is
  one; every theorem holds at each, unchanged; noninterference and engines whose choice is not a
  function of the operands are §37 *Open*. The compiled code no longer tests each float result
  for a NaN; the closure-IR and flat-IR interpreters run at two other resolutions, so a program
  whose output depends on the choice fails the harness. `corpus/float-compare.bc` takes its NaN by
  its bits (its output unchanged). The flat IR's documentation is target-neutral: its operations
  are SPEC's, and the data's address (`16384` in Wasm) is the target's. No change to `CDerives`,
  the relation, the machine, a kernel program, or any program's output, goldens or counts.

- **0.69** (2026-10-17) — §39 (new, #513): integer `/` and `%` at `i32`, `i64` and `u8`, and
  `div_euclid`, `rem_euclid`, `checked_div`, `checked_rem`. A division with no answer (a zero
  divisor, `MIN / -1`) raises `Fail[DivError]` (`lib/arith.bc`), an instance of `Fail` beside a
  program's own (§38), handled by `to_result`, `default` and `map_err`. The effects pass decides a
  division's row at its operands' width, in the walk that reads the instances, and writes one that
  can fail as the checked division and a `raise` before rows are inferred (a width it cannot read
  is taken to be able to fail). A nonzero literal divisor (not `-1` for `/`) performs nothing and
  is the bare instruction; a variable divisor costs one test. A `Fail[DivError]` that reaches
  `main` is served by `main_div_error`: the unwind runs the finalisers, the error is written on
  standard error, and the program exits with status 1 at every stage (`<name>.status` in the
  harness). `int-slash` moves from `corpus/reject/` to the corpus; new programs `div-recover`,
  `div-unhandled`, `div-innermost`, `div-own-fail`, `div-abstraction`, `div-overflow`,
  `div-euclid`, `div-infer`, `div-recursive`, `div-literal`, `sugar/div-literal`, and the reject
  `div-row-unlisted`; six programs rewritten with `/` and `%` at their outputs and counts. §8
  *Open*, §37 *Surface* and §38 *Open* updated. No change to `CDerives`, the relation, the
  machine, a kernel program, or any existing program's output, core or counts.

- **0.68** (2026-10-17) — §38 (new, #519, #155, #516): instances of an effect. An instance is an
  effect at its type arguments; a row holds an entry per instance, with names
  (`with src: Kube, dst: Kube`); an operation's type arguments are read off its argument's type,
  a template call's off its arguments', at the declaration's own types, by the typed elaboration's
  inference before effects are resolved. An operation goes to the innermost handler of its
  instance; `with n = h(…)` names a handler and `n.op(v)` performs at it, a named entry is served
  by the handler of its name; an operation two instances in scope could serve is an error that
  asks for an ascription or a name. Abstraction safety: a row's entries are slots resolved at the
  template's types, never merged by instantiation (a handler site's types are now instantiated
  with a template, `HInfo.subst`). Several sites in one counted loop's body; a stateful handler's
  function of its state at the row of its `with` (#514). §18 *Not provided* loses a second
  instance in a row and two sites in a counted loop's body; §18 *Open*, §19 *Names* and §34 point
  to §38. New corpus programs `effects-instances`, `effects-abstraction`, `effects-named`,
  `effects-fail-list`, `effects-cancel-two-sites`, `effects-row-inferred`, and four rejects;
  `corpus/reject/effect-error-type.bc` raises a literal, its old form now inferred. No change to
  `CDerives`, the relation, the checker's rules, a kernel program, or any existing program's core,
  output, counts or reports.

- **0.67** (2026-10-17) — §37 (new, #499): floats. `f32` and `f64` are two more widths of
  `VTy.int`, with literals given by their bits and Wasm's float instructions as host operations
  (arithmetic, `min`/`max`/`copysign`, `abs`/`neg`/`sqrt`/`ceil`/`floor`/`trunc`/`nearest`, the
  IEEE comparisons, the conversions); float-to-integer `trunc` answers a sum where Wasm traps,
  `trunc_sat` is total. Every engine makes an arithmetic NaN result the canonical NaN (Wasm's
  deterministic profile), so all agree bit for bit. The surface reads decimal float literals,
  correctly rounded, and dispatches `+ - * /` and the comparisons at the float widths; `/` is
  only at floats. A float has no equality, hash or order provider: `total_cmp_*` and the
  `OrderedFloat` key `ord_*` give IEEE `totalOrder`. `lib/float.bc`: the operations by name,
  conversions, shortest round-trip printing (Burger–Dybvig, exact) and correctly rounded parsing.
  §8 *Open* updated. New corpus programs `float-arith`, `float-compare`, `float-convert`,
  `float-ordered`, `float-roundtrip`, `leetcode/heaps/0295-find-median-from-data-stream-f64`.
  No change to `CDerives`, the relation, the checker's rules, a kernel program, or any existing
  program's output or counts.
- **0.66** (2026-10-17) — §36 (new, #508, from #489): `poly` families, a family of functions with
  one case per type, chosen as the most specific case whose head the type argument matches; a
  second case at a type, or two overlapping cases neither more specific, is an error at the
  declaration. Operators are families: their cases at the integer widths are the host's
  instructions, as before, and a program's case at another type makes the operator work there.
  `lib/key.bc`: `equal`, `hash` and `order` over views, at the integers, `1`, pairs, sums, arrays,
  views and buffers. `lib/map.bc`: the hash map and set, a plain value (a trial), `map_get` a view
  through the map lent fieldwise. Elaboration: `borrow imm *g { … }`, a record of arrays lent
  fieldwise, a lend to a function with several lifetime parameters, a type read off a place lent
  at a parameter of its own type. New programs `poly-operators`, `poly-providers`, `map-views`;
  eight pending programs accepted (`aoc/2024-01`, `2024-11`, `2022-21`, and LeetCode 1, 49, 128,
  217, 347); four rejects. No change to `CDerives`, the relation, the machine, the checker, the
  backend, a kernel program, or any existing program's output or counts.
- **0.65** (2026-10-16) — §35 (new, #500): the backend's implicit allocations. A cell the
  elaboration scopes to one borrow (a lend of a value, `modify` of a value, a handler's state
  given as a value) is a slot of its code's frame when no suspension crosses its scope, on a Wasm
  shadow stack (`$sp`); the capability cells are words of the program's data; a recursive type
  boxes a sum's payload in place of its payload's recursive fields when that boxes fewer (a tree
  is one object a node, an empty child none); the arguments' memory counts in `$allocs`. The
  allocations that remain are said in the library's comments and §35. New corpus program
  `async-lend-slots`; `bcc-counts --sites` reports the scoped cells. Counts fall (`rec-tree` 254 →
  127, `tree-map` 58 → 29, `rec-deep` 60040 → 30040, every I/O program's capability cells), but
  `io-args`'s (7 → 6, its reservation counted). §11's and §34's *Lowering* updated. No change to
  `CDerives`, the relation, the machine, the elaboration, a kernel program, or any program's
  output.
- **0.64** (2026-10-16) — Library only (#198, #201, #203, the LeetCode corpus in
  `corpus/leetcode/`): §17's `lib/buf.bc` gains `heap_peek`, the least element of a heap read
  without taking it out. Ordinary library code over existing constants. No kernel, checker,
  elaboration or backend change; every existing program keeps its output and counts.
- **0.63** (2026-10-16) — Library only (#490, the Advent of Code ports in `corpus/aoc/`): §17's
  `lib/buf.bc` gains `array_set` and a binary min-heap over a buffer (`heap_push`, `heap_pop`),
  and `lib/text.bc` the integers of a view folded into a state (`fold_i32s`, `fold_i64s`); §34's
  `lib/io.bc` gains `dec64_each` and `print_dec64`. Each is ordinary library code over existing
  constants, every loop counted. No kernel, checker, elaboration or backend change; every
  existing program keeps its output and counts.
- **0.62** (2026-10-16) — §34 (new, #156): the standard streams, the clock and the arguments as
  answering effects (`lib/sys.bc`), the clock's time `i64` nanoseconds, monotonic, saturating at
  `2^63 − 1` (the user's decision), whose outermost handler is the WASI preview 1 platform
  (`lib/wasi.bc`), its handlers' state lent to their clauses (`handler h(&mut s: S)`), each clause
  a direct call of an extern; `main` alone is given them ambiently, holding the cells and lending
  one to each operation, and every other function by its row; answering operations with lifetime
  parameters; a task of `spawn_in` given the capabilities its body uses, lent for the borrow block
  around its spawn (PROPOSED); the laws of each effect. New opaque kinds `clock` and `args` with
  their externs' models and proofs (`clockNow_meets`, `clockSleep_meets`, `readArg_meets`, and the
  harness's). `lib/io.bc` and `lib/textio.bc` rebuilt on the platform's handlers, with
  `print_dec`, `eprint_dec`, `print_lit`, `print_str`, `print_string`, `eprint_lit`, `eprint_str`,
  `read_input`, `next_arg`, `ns_of_ms`. `bcc trusted` lists the externs `main` reaches; `corpus/trusted/` pins
  six. Program arguments: `bcc interp … -- arg…`, `bcc run <file> arg…`, `<name>.args`. Backend
  fixes: a code that suspends at operations of different answer types (#485), and a resume code's
  cancel arm injecting one binder at two types (#486). New corpus programs `io-effects`,
  `io-upper-effects`, `io-args`, `io-task`, `reconcile-clock`, `io-laws`, `answers-two-types`,
  `loop-row-answer`; `needs-stdout` moved from `pending/`; reject `io-unlisted`; pending
  `io-two-tasks`; reports `io-effects`, `io-task`, `needs-stdout`. **`reconcile-chain` changes its
  output on purpose**: without its simplifications around #485 and #486 it has a service with a
  state and a clock whose `sleep` answers, and answers the service's count too, at `28 3 0` (from
  `25 0 0`). `corpus/reject/include-unknown.bc` and `corpus/pending/effects-generic-store.bc`'s
  messages, and `corpus/pending/async-progress.bc`'s position, re-recorded. §11, §18 and §33
  updated. No change to `CDerives`, the relation, the machine, `PinLaw`, a kernel program, or
  another program's output or count.

- **0.61** (2026-10-16) — §33 (new, #161 part A): computation parameters, a parameter whose type
  has a provided row, `!(A => B with E…)` (PROPOSED spelling), whose provided control effects the
  callee serves at its ports (decision 57) and whose other effects tunnel to where the argument is
  written; a function named at a parameter of function type is the block that calls it, so
  `f(g)` and `f({ x -> g(x) })` are one argument; `|>` (decision 50): a handler stage is `with`,
  a computation parameter first takes the piped value suspended, any other function takes it
  first. The laws `m |> h ≡ with h { m }`, associativity, pass-through and lexical blocks, with
  what each rests on (associativity across function stages is *Open*). An annotated binding whose
  head performs operations of the row is elaborated at the row (a `with` in a counted loop at a
  resuming row). New corpus programs `comp-param`, `pipe-handlers`, `gen-pipeline-pipe`,
  `reconcile-chain`; `effects-sum-gen` moved from `pending/`; reject `block-raise-lexical`; pending
  `comp-param-two-sites`, `comp-param-capability` (#487), `comp-param-for`, which record what is
  not provided yet (the port rule is provisional until relabelling); reports `comp-param`,
  `effects-sum-gen`. **`retry-block` changes its output on purpose**: its `retry` takes a
  computation parameter and retries, `((inl i32[200], i32[30]), (inr i32[503], i32[10]))` where
  it answered `((inr i32[503], i32[0]), (inr i32[503], i32[0]))`; its counts are unchanged. Stored
  callbacks with a row (part B) stay *Open*, with the options written in §33 *Open*. §11, §14,
  §15, §18, §24, §30 and §32 updated. No change to `CDerives`, the relation, the machine,
  `PinLaw`, the checker, the backend, a kernel program, or another program's output, count or
  report.

- **0.60** (2026-10-16) — §32 (new): `Async`'s `log`, `spawn_logged`, `lpush` and `run_logged`
  (A5); A6 on the library; blocks that use capabilities (an answering handler's state, a `for`'s
  threaded variables), passed with the block at each call; a handler's lifetime parameters, at
  the meet of the lifetimes in scope, and `spawn_in`, `queue_in`, `push_in`, `run_in` (tasks over
  an outer borrow). A function with a row passed as a value stays refused, deferred to #161
  (§32 *Open*). New corpus programs `async-logged`, `async-cancel`, `async-scoped`,
  `block-yield-inner`, `block-capability-inner`, `list-capability`, `async-workers-scoped`; moved
  into the corpus: `yield-callback` (from `pending/`), `block-capability` (from `reject/`); reject
  `spawn-in-unscoped`. `experiments/AsyncCap/bc/a5-effects.bc` and
  `a6-cancel.bc` removed (in the corpus). The reports of `async-scheduler` and `async-map` name
  `log`. §28 *Open*, §30 *Not provided* and *Open* updated. No change to `CDerives`, the relation,
  the machine, `PinLaw`, the checker, the backend, a kernel program, or an existing program's
  output or count.

- **0.59** (2026-10-15) — Elaboration hygiene (#481): a control handler's parameters are bound
  at each `with` under fresh names, and a local named as a declaration of the program or of a
  library the elaboration brings in is renamed in its scope (`Frontend/Elab/Hygiene.lean`), so a
  handler's parameter no longer captures the body's or the continuation's variable of its name,
  and a handler clause, an effect's resolution or generated code no longer resolves a
  declaration's name to a user's local. New corpus programs `hygiene-*` (thirteen). No change to
  `CDerives`, the relation, the machine, a kernel program, or an existing program's output or
  count.

- **0.58** (2026-10-15) — §31 (new): generic recursive groups (type and lifetime parameters,
  layers, the heap driver), blocks with a row given to generic functions, and three inference
  fixes (a nested template call typed at its parameter; a pair as the last argument, #135; a core
  `def[A]` calling a template, #136). `lib/list.bc`; `lib/async.bc` includes it. New corpus
  programs `list-generic`, `list-blocks`, `rec-generic-mutual`, `rec-generic-layer`,
  `rec-generic-deep`, `rec-lifetimes`, `generic-pair-arg`, `generic-in-def`,
  `text-lend-lifetime`; rejects `rec-generic-params`, `rec-name-clash`, `double-use-in-callee`.
  `async-map` (A4) uses the generic `map`, with its output and counts unchanged; `quicksort` loses
  its three ascriptions. §9, §17 *Open*: the stale inference lines removed; §20, §21, §30 *Not
  provided* and *Open* updated. No change to `CDerives`, the relation, the machine, a kernel
  program, or an existing program's output or count.

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
  *Baseline*: the checker's copies, a `def`'s body at each use, are that premise term, and a
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
