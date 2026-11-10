# Borrow core — specification

Version: the highest entry in `docs/changelog/`, printed by `scripts/changelog.sh --version`.

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
an immutably borrowed function can only be released, because it may capture linear
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
| `FnMut` | `[@c] U(Clo^c T₁ T₂)`, the closure of §22, called through a `Mut` borrow by `withswap` |
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
the lifetime `∀` (elimination at every `C`), the `!` rules of §2 (promotion over a flat
context, §10), `[]I` at every value type,
`⊑Imm`/`⊑Mut`, one constant per borrow axiom of `[TR]` p. 3 at arbitrary value-type payloads,
three call-by-value derived forms (`lolliE`, `allEV`, `ofRet`), and conversion up to the names of
lifetime binders (`[α]`, *Lifetime binders and `[α]`* below). No new machine rules.

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
consume of a type (`consume`, `consume_wf`; a recursive type's is a fixed point), a block's allocation
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
nodes already. A consume is the rule nodes `unitE` over `lolliE` of the variable and the consume's
derived node (`consume`), and a finaliser the `[then]` node's third child, built of consumes.

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
can, as a leaf consumes a persistent slot and `⟨⟩` takes any. Which slots it can take is the body's
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
  the type elaborated at the use is another `VTy` than the one checked. `[α]` (below) relates the
  two types; placing the body without checking it again would also need its derivation's binders
  renamed, which is not built.

In #509's reproduction (`print_f64` twice) that is 179 keys and 249 checks, of which 36 are bodies
with a borrow and 34 bodies whose type has a binder.

**Lifetime binders and `[α]` (#808).** A term's lifetime context numbers its variables from `0`: a
function's lifetime parameters, `Fun`, a borrow's lifetime, `'main` (`Δ.freshVar`), and the
elaborator names a type's binder `forall 'x < @b. C` or `all 'x < @b. A` the same way. So one
written type elaborated in two lifetime contexts can be two `VTy`s that differ only in their
binders' names, as `File<'c>` (§22) is in `main` and in `file_read<'a, 'c>`. The kernel accepts a
term at every type equal to its own up to those names, by one rule of `CDerives`:

    Δ; Γ ⊢ e : j     j ≡α j'
    ────────────────────────  [α]
         Δ; Γ ⊢ e : j'

- **The relation.** `j ≡α j'` is `Jdg.alphaB j j' = true` (`Core/Fundamental.lean`): `VTy.alphaB`/
  `CTy.alphaB` at no binder pairs (`Core/Types.lean`). The binders are `CTy.all` alone (`VTy.all`
  is `U (∀'x ⊏ @b. F A)`); passing `∀'x ⊏ @b. C` and `∀'x' ⊏ @b'. C'` pairs `'x` with `'x'`, and
  a variable is read through the innermost pair that binds it on either side, or is free on both.
  An effect row's operations are compared at their argument, answer and cancel row like every other
  type (`OpSig.AlphaEq`, `RowAlpha`). It is an equivalence (`VTy.alphaB_refl`, `_symm`, `_trans'`,
  `Core/Alpha.lean`).
- **Rows and the effect context.** A row is tied to the effect context `Ξ` up to α (`RowAt`,
  `OpAt`, `Core/Tied.lean`): an operation's qualifier is `Ξ`'s and its argument and answer are
  α-equivalent to `Ξ`'s (`OpSig.AtEntry`), so an operation whose type is elaborated in two lifetime
  contexts has one signature. A handler's signature is a prefix of `Ξ`'s up to α
  (`sig_prefix_of_rowAt`); its tags are a prefix of `Ξ`'s qualifiers as before (`hndTags_of_rowAt`).
  The checker's `sigsOkB` compares an operation's signatures up to α.
- **Soundness.** At substitutions agreeing on the pairs (`AlphaAgree`), α-equivalent types are one
  type (`VTy.alphaB_sound`, `CTy.alphaB_sound` into `TyEq`/`CTyEq`), so the relation reads them
  alike (`cC_alpha`, from `cC_tyEq`). `[α]`'s compatibility lemma is `alpha_compatJ`; it is the
  rule's one cost under the growth rule.
- **The checker.** The checker compares two kernel types in one place. `tyEqV`/`tyEqC`
  (`Frontend/Check/TyEq.lean`) decide equality up to α, and `convVal`/`convComp`
  (`Frontend/Check/Conv.lean`) carry a checked term from the type it was derived at to the type it is
  wanted at. Equal types take no node, α-equivalent types take `[α]` (`rAlpha`), and a returner chain
  `F_Σ′ A′` wanted at `F_Σ A` takes `[sub]` to `Σ` read at `Σ′`'s names (`alignRow`), then `[α]`.
  These are the sites that compare:
  - checking against an expected type (`convV`, `convC`);
  - a bound head lifted to its binding's row (`liftRow`, `atRow`);
  - the argument of `M x` (`appIt`: `M` carried to the argument's type);
  - the binder of `fun (x : A) -> M` (checked at the annotation, then carried to the expected
    `A₀ -o C`);
  - `nu_in M` synthesized (the `ν` type found under the observations' arguments and `∀` binders,
    `M` carried to its unrolling);
  - `withbor2r`'s annotation against the lent cell's type (the lend is at the cell's type);
  - `shorten`'s operand against its family;
  - a handler's clause tuple against the type its reading rebuilds (`clausesReadAt`, `convVal`);
  - a `handle` site's record against the node's operations (`tyEqEnts`);
  - the program's operation signatures (`sigsOkB`, `sigsErr`);
  - derived copies (`withCopiesC`, `withCopiesVC`);
  - the backend's `handle` nodes of one static name, which a direct call needs at one outer row and
    one signature (`directFacts`, `Backend2/Driver.lean`: `tyEqC` at the rows, `tyEqEnts` at the
    operations). Copies of one site from generic instances at different lifetime contexts spell
    their binders differently (`corpus/alpha-handle-copies.bc`, erased).

  `alignRow` reads each operation the synthesized row finds, and each layer of its cancel row at
  every depth (`alignFin`), at the synthesized names. So a cancel row that grows and names its
  binders differently is `[sub]` then `[α]`. `rowLeB` decides `[sub]`'s `RowLe` with cancel rows
  growing (`finLeB`, `Frontend/Check/Decide.lean`). The written cancel rows are `F 1` (`elabRow`),
  so the case is exercised on the rows themselves (`alignRow_grow_renamed`).

  Some comparisons stay exact, each with its reason in `scripts/type-eq.allow`:
  - kernel premises stated exactly (`OpSig.Sig` in `[sub]`; `Row.ResumeO`'s binder-free `F 1` and
    `1`; `FamSide.hinst`);
  - cache and cell-class keys, where an unequal key is a miss and never a refusal; the backend's
    cell classes are keyed by `eraseLife`, which sends α-equal types to one type
    (`VTy.eraseLife_of_alphaB`);
  - the kernel's derived consume `consumeE A` (SPEC §12), whose one comparison is a key lookup
    among the keys of the one type it is built at, and the kernel programs built from it;
  - the IO harness's comparisons against the standard table. Those types are elaborated at the
    empty lifetime context, where binders are numbered by position, so an α-variant spelling
    elaborates to the table's term.

  The elaborator (`Frontend/Elab/`, `Frontend/Sugar.lean`) compares kernel types through the same
  `tyEqV`/`tyEqC`: generic inference (`matchV`, `matchC`, `phUnify`, `specTy`), instance keys
  (`Env.sameArgs`, `sameTy`), the readers of loop, iterator, generator and `sized` types
  (`loopRowOf`, `iterOf`, `pullOf`, `sizedOf`), and the loop plans' tests of their value types.
  `corpus/alpha-generic-arg.bc` infers a generic argument from two α-variant types.

  `scripts/check-type-eq.sh` (a gate step) reads the elaborated declarations of every compiled
  module (`bcc`'s import closure outside `Core`, `Support` and `Paper`: `Frontend`, `Target`,
  `Pipeline`, `Reference`, `Backend`, `Backend2`) and refuses any other equality of `VTy`, `CTy`, `OpSig` or a row decided at run
  time, directly or through a kernel declaration that decides one (`scripts/TypeEq.lean`).

  Surface types name their binders, so α does arise there. The elaborator compares them up to the
  names of their binders (`VTy.alphaEq`, `Frontend/Elab/SurfAlpha.lean`: every lifetime binder and
  `mu`/`nu` binder renamed by its depth, spans dropped). It does so where two surface types are
  compared as types: the effects pass's matching of type arguments (`matchTy`), instance keys
  written as surface types (`Env.sameArgs`, `sameTy`), a recursive group's result types, and a
  datatype's own parameters. The caches of generic instances and of higher-order copies key on the
  same renaming (`makeInst`, `copyOf`). The other surface comparisons are of terms and
  declarations, or test whether a type mentions a name by substituting for it. None of them
  compares two types. The census does not cover surface types.

  The `[α]` node erases to its premise's term, and the backends read through it
  (`transparent?`).
- **Inversions.** `[α]` concludes with its premise's term, so it is a same-term step (`JS.alpha`,
  `VS.alpha`, `Core/Inversions.lean`), and what an inversion gives is up to `≡α`: views keep their
  head up to `≡α` (`VView.hnf`, `Hnf.alpha`), a rigid type is read at its α-equivalents
  (`JR.rigid`), an `&` at α-equivalent `&`s (`JR.amp_amp`, through `CTy.alphaB_unroll` at two
  positive bodies), a λ-value's binder at an α-equivalent of the type it is read at
  (`lam_bang`, `lam_arr`, `der_clause_body`), and a row at the rows `[sub]`'s order and `[α]` reach
  (`RowReach`, `JR.rowLe`), whose operations keep their key, qualifier, mark and answer's `0`-ness
  and reach their cancel rows (`OpReach`, `FinReach`).
- **The inversions' cost** (CLAUDE.md, *Do not invert `CDerives` casually*). `[α]` is a same-term
  rule, so every inversion takes it as a step and gives its facts up to α. The change against the
  rule-free baseline: `Core/Inversions.lean` +483/−203, `Core/Rejections.lean` +194/−141,
  `Core/EffCancelTyped.lean` +186/−109, `Core/AwaitCancel.lean` +4/−4, and `Core/Tied.lean`
  +67/−31 for the tie up to α; `Core/Alpha.lean` (921 lines) holds the α lemmas the inversions and
  the checker use. Persistence is kept (`VTy.alphaB_persistent`), so
  each refusal (`refuses_R_clauses`, `not_der_at05`, `not_der_at06`, `not_der_at08`,
  `not_der_at13`, `not_der_progT`, `not_der_e7c`) holds as before.

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
acts fieldwise. Projecting one field of a borrowed record consumes the other fields' views, which
must be `Releasable`; `Releasable` has no `μ` case, so projection past an unboxed `μ`-typed field
is not available (destructuring is).

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
they agree on every program but eight, where a class is wider (an `i32` cell, three words where
the layout types give one, because a cell holding `1` is refilled with a list elsewhere, as
`fold_reuse`'s emptied cells are).

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

For `T` in the wider class `P` (closed leaf, a variable in scope, `⊗`, `⊕`, `Ref S`, `Array S`
and `μ` over members, not headed by a variable; §61), the owned fold with one algebra per key
(each `μ` and each array of recursive data), passed at run time:

    foldOwnG  : Algs ⊸ !U(μX.T ⊸ F R₀)

It terminates by the size of the owned resource, then of the value, then of the key's body.

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

**Positivity** (`CTy.NuOk`). `C` is a `&` of two observation trees (`CTy.NuShape`), and an
observation tree is an `F A`, a `&` of two observation trees, an observation that takes an
argument, `A ⊸ D` with `X` not in `A` and `D` an observation tree (§22), or an observation
quantified over a lifetime, `∀'x ⊏ @b. D` with `D` an observation tree (§22). In each result
`A`, `U X` occurs only under `⊗`, `⊕` and `[@a]`: `A` is `U X`, `B ⊗ B'`, `B ⊕ B'` or `[@a] B` of
such types, or a type in which `X` does not occur (`VTy.Poly`). So `X` is never in an argument,
under a `Ref`, a borrow, a `!`, a `μ` or another `U`, and a `νX. C` always has at least two
observations. An argument's lifetimes are unrestricted: `Mut 'x A ⊸ D` under `∀'x` takes a borrow
lent for that one call. **Binder freshness:** no lifetime bound by a `∀` leaf is free in `C`, so
the unrolling `C[U(νX. C)/X]`, which puts `U(νX. C)` under those binders, captures none.

`X` is kept out of arguments because an argument is a negative position: one unfolding is
monotone in the candidate for `U X` (below) only while the argument does not read it.
Lifetimes are not type variables, so `X ∉ A` (`A.Cl 0`) places no restriction on them; what an
observation taking a borrow needs is the `∀` leaf (#808).

**Relation.** At a positive `C`, `𝒞⟦νX. C⟧` is the greatest fixed point of one unfolding of the
observation tree, with a candidate `R` for `U X`: `⋃{R | R ⊆ Φ_C(R)}`, written in `Prop` as
`∃ R` (`docs/scope-recursion.md` §3.1). `Φ_C` is monotone because `X` is outside every `Mut`
payload and every argument. It needs no approximation of `νX. C` and no step index. `cC` reads
the shape (`NuShape`) as its guard; freshness is syntactic, not invariant under renaming a
binder, and the rules carry it through `NuOk`.

**In and out.** `C[U(νX. C)/X]` is the unrolling:

    Γ ⊢ M : C[U(νX. C)/X]            Γ ⊢ M : νX. C
    ──────────────────────  nuIn     ──────────────────────  nuOut
    Γ ⊢ M : νX. C                    Γ ⊢ M : C[U(νX. C)/X]

on the same term, at a positive `C`. Observing a `νX. C` is `nuOut` followed by the projections
of the unrolling.

**Coiteration.** At every positive `C` and every state type `S` that mentions no lifetime
bound by a `∀` leaf of `C` (`CTy.BindsFresh`, since `C[S/X]` puts `S` under those binders):

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
buffer or a cell handed back). `close` is required: no rule discards a `U C`, so a linear state
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

### Consume

`U(νX. C & F R)` with `R` closed and in `Consumable` is consumable (§12): force, `nuOut`, the
second projection (`close`), then the consume of the residual `R`. Delay and stream have
`R = 1`; an iterator's residual is consumed by its own consume.

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

§37 adds the floats and §73 the unsigned widths `U32` and `U64`.

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
| `slice_get_mut` | `!(ArrayMut @a A ⊗ I32 ⇒ Mut @a A ⊕ 1)` — `idx`: the leaf at the index; the rest of the family is released, since a `mut` leaf holds no `own` cell (`noOwn_mut`) |
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

A `mut` family is consumable (§12), so a part a program does not use is consumed.

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
consumed inside the lend (its consume, §12), so `reverse(&mut a)` is `()`; a result that holds
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
    (μ, consume (f, (ℓ, n))) ↦ (μ, f (free (ℓ+0)); …; f (free (ℓ+n−1)); ())

`tab` places the cells, then runs the ordinary term that fills them; `drop` is a pure step to the
ordinary term that empties and frees them. The machine stays deterministic at each host up to the
choice of fresh locations, as `alloc` is. An index out of range takes the sum's error branch; no
step is stuck on a well-typed argument.

### Relation

    𝒱⟦[L]⟧δ(v) ≜ ∃ℓ c. ⌜v = (ℓ, i32 c) ∧ c < 2³¹⌝ ⋆ ⊛_{i < c} 𝒱⟦L⟧δ(ℓ + i)

At `Array A` this is `n` owned cells, each holding a value in `𝒱⟦A⟧`; at `ArrayImm @a A`, `n`
`imm` cells at `@a`. Nothing else changes in the typed world: a block allocation is `n` of
`TW.alloc`, a consume `n` of `TW.free`.

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
| `array_empty` | `Array A` — `(0, 0)`, the array of no cells, at every `A`: it needs no element (`arrEmpty_compatX`, the empty family `famEmpty_compatX`; §61) |
| `array_free` | `!(!(A ⇒ 1) ⊗ Array A ⇒ 1)` — `drop`: each element to the consumer, in index order, then the cells freed |
| `array_size` | `!(Array A ⇒ Array A ⊗ I32)` |
| `array_replace` | `!(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))` — the old element, or the new one back if out of range |
| `array_len` | `!(ArrayImm @a A ⇒ I32)` |
| `array_get` | `!(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)` — `idx`: a leaf view at the family's lifetime |
| `array_copy` | `!(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)` |
| `array_release` | `!(ArrayImm @a A ⇒ 1)` |

`array_replace` on `Mut @a (Array A)` is `withswap` with `array_replace` in its callback.

Implicit consumes (§12): `Array A` has one when `A` does, `array_free` with the consume of
`A` as the consumer; `ArrayImm @a A` is releasable, by `array_release`, and `ArrayMut @a A` by
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
- Whether `slice_borrow`'s side conditions on `A` and `B` can be consumed: they are used by the
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
persistent live slot to both sides, `Ctx.DeadP` may consume one, and `Ctx.SoloP` may consume one beside
the variable used. So persistent variables are copied and consumed implicitly, at dead-context rules
and at variable leaves alike, and `copy_bang`/`release_bang` are needed only to make that explicit.
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

### Promotion over a flat context

A value type is **flat** when it is persistent and holds no recursive data (`VTy.flat`): `I32`,
`I64`, `U8`, the floats (`.int _`, §8), `1`, `0`, `!A`, and `⊗`, `⊕` and `[@a]` over flat types.
`μ` is not flat. `flat A ⇒ persistent A` (`VTy.persistent_of_flat`). A context is flat when every live slot's type is:

    Flat(Γ)  ≜  ∀ s ∈ Γ. s.live ⇒ s.ty flat        (Ctx.FlatLive, Core/Persistent.lean)

`!Γ` (`Ctx.Banged`, every live slot at a type `!A`) implies it (`Ctx.Banged.flatLive`), since `!A`
is flat. The premise of Core's two promotion rules, which §3 takes from §2's `!I-λ` and `!I-Λ`, is
`Flat(Γ)`:

    Flat(Γ)    Δ; _ : 1 (dead), Γ ⊢ M : F A
    ───────────────────────────────────────  !thunk     (bangThunkF)
    Δ; Γ ⊢ λ_. M : !U (F A)

    Flat(Γ)    C ≠ F _    Δ; Γ ⊢ λN : C
    ───────────────────────────────────  !thunkv    (bangThunkV)
    Δ; Γ ⊢ λN : !U C

So a `!` closure may capture a live variable of any flat type: the scalars, `1 + 1`, `1`, `0`,
`!A`, and `⊗`, `⊕` and `[@a]` over flat types. `U C`, `Ref`, `Imm`, `Mut` and the opaque host types
(§11) are not persistent, and `μ` data (a list) is not flat, so a closure capturing one is not
promoted. It is an ordinary closure `U C`, moved with no copy at capture. Rust splits implicit
duplication (`Copy`, flat captures only) from explicit (`Clone`); the explicit half for closures is
*Open* (#928).

- **Soundness.** The compatibility lemmas (`bangThunkF_compatC`, `bangThunkV_compatC`, and the
  chain's `bangThunkF_compatN`, `bangThunkV_compatN`) need only that the context relation holds at
  `∅`. `gSepC_persistent` (the chain's `gN_persistent`) gives it from `Flat(Γ)` through
  `flat ⇒ persistent`, slot by slot, by `vCE_empty_of_persistent` (`vN_empty_of_persistent`).
- **Mirrors.** `CDerivesAt` (`Core/Tied.lean`) and the generated `CDerivesP`, `TDerivesAt` and
  `TDerivesP` (`scripts/gen-pin.py`) take the same premise. The checker's promotion test
  (`Frontend/Check/Rules.lean`) asks `VTy.flat` of each live slot. The inversion of a λ read at a
  `!` thunk (`LamCls`, `lam_bang`) gives a flat context, and AT06's rejection reads that the
  captured cell's type, a view of `Ref`, is not flat.
- **Where `!Γ` stays.** `[let]` and `[then]` at a row with an unrestricted operation (§19), and
  `Count`, `Inversions` (`banged_slot`), `Weaken` and `Embedding`, keep `!Γ`.
- **Backend.** A captured flat value is copied into a `!` closure's environment as a `!` value is,
  as a scalar or a flat tuple: Backend2 copies the environments of `!` closures, and
  `LTy.persistent` agrees with `VTy.persistent` (`ofV_persistent`).

Baselines: every existing derivation still holds, since `!Γ ⇒ Flat(Γ)` and the rules only widen;
program derivations in `Core/` pass `(…).flatLive` or a proof generic in the predicate. The
fundamental property (`fundamentalC`, the pinned and the chain versions) and adequacy are
unchanged in statement. Every rejection theorem (AT06 among them) holds, restated over the wider
inversion. Every corpus program and golden is unchanged. No `CDerives` index or rule is added, and
the judgment freeze is unchanged.

### Open

- A persistent closure (`!(A ⇒ B)`) that captures recursive data is copied deep too; its type
  does not say what it captures, so that copy is not checked (`bcc-counts` counts it).
- **Explicit duplication of a closure whose captures are clonable** (Rust's `Clone` for closures).
  A closure that is not `!` and captures `μ` data is moved, and cannot be duplicated: `clone`
  refuses a linear value. Duplicating it needs a kernel copy rule, likely on §68's
  `Code⟨N; E⟩ C`, which records the environment (#928).

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
consumed. Each opaque type `k` has a **model**, a predicate `k.Holds` on values, and

    𝒱⟦k⟧δ(v) ≜ ⌜k.Holds v⌝                                      (in both modes)
    Imm̲ 'b k ≜ Unk          Δ ⊢ k ⊐ @a (at every @a)          not persistent, no consume

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

### `Tok`: the token of a declared type

    A ::= … | Tok                                   (VTy.opq .tok)

`Tok` is an opaque kind that is not a host type (`Opaque.Host k` is `k ≠ tok`). Its value is a
location owning a unit cell, the pattern of §25's capture cell, and its relation, in both modes, is
`Ref 1`'s (`Opaque.rel`, `Core/Opaque.lean`):

    𝒱⟦Tok⟧δ(v) ≜ ∃ℓ v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ ⌜v′ = ()⌝        Imm̲ 'b Tok ≜ Unk

Two constants, at a dead context like the borrow axioms (`Core/Tok.lean`):

    mint ≜ λx. alloc x : 1 ⊸ Tok        (CDerives.tokMint)
    burn ≜ λc. free c  : Tok ⊸ 1        (CDerives.tokBurn)

`mint` allocates the cell by the ordinary `alloc` step and `burn` frees it, so their compatibility
lemmas are `[TR]` 6.141 and 6.142 (`tokMint_compatX`, `tokBurn_compatX`, by `wpTS_alloc` and
`wpTS_free`, the lemmas `ewp_alloc` and `ewp_free` take at an effect row). `burn` is the only
constant that takes a `Tok`. A program cannot write them: the lexer has no keyword for the
constants and the parser reads the type `tok` only in the source the elaboration writes and parses
back (its templates, a type printed as surface syntax, the `run_io` wrapper). The elaboration of
§42's declared types is the one place that names them (`Const.tokMint`, `Const.tokBurn`).

`Tok` is linear and not consumable (`tok_linear`: `Consumable` has no `opq` constructor), and it owns
its cell, so it is not `VTy.OwnFree` (`tok_not_ownFree`): an abort cannot abandon it (`[let]`'s
`hW`, `[raise]`'s `hd`), and neither can it abandon a type that holds it. A `Tok` the run did not
burn keeps its cell, so `adequacyC`'s empty final memory says every one was burned (§42).
A cell of `1` lowers to no words (`zeroCell`, §23).

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
capabilities are not consumable (§12), so `main` hands them back; `run_io` (below) then takes
them back by the harness. `A` is the program's result; `bcc interp` prints it, so it is persistent.

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
`main`'s body is put in the wrapper as its elaborated term, not as its printed form, so the
elaborator's marks (§3) reach the check, and the check carries the elaboration's keys of the
`def`s it copied: the wrapper is checked as it is (`checkElaborated`), not elaborated again, and the
keys it carries are the first elaboration's. `run_io` is checked like any `main`, so it has a
`CDerives` derivation at the context of the operation and harness externs; `bcc interp` runs it
with the model implementations. Its compiled form, `run_io : Bytes -o F A`, takes the outputs
back as the model's form does and weakens them in the term (they are persistent); both backends
compile it with the host implementations (*Lowering*).

The harness externs are `run_io`'s alone. A program that declares one of them, or `io_inp` or
`io_main_body` (the names the wrapper binds around `main`'s body), or that declares a capability
other than as an extern, is refused: it could otherwise make a capability of its own, or have a
name of its own captured by the wrapper.

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
  `io_every_run` takes, and `bcc interp` runs exactly `run_io[γ] inp` (`IORun.expr`). The
  compiled form is an `IORun` too, and the program a backend compiles is its `IORun.expr r []`
  with each extern's host for its model.
- **No capability, no effect** (`wpTSD_frame_own`). A cell owned by the frame of a computation
  holds the same value at the end of every value run of it. A computation's resource is what its
  context and captures hold, so a function given neither the `stdout` cell nor a borrow of it,
  nor an `Output` in a cell it owns, leaves the stream's content as it was: it writes nothing to
  standard output.

**Adequacy's scope.** The empty-memory conclusion is about the model's cells. File descriptors
and other host handles are not memory: adequacy says nothing about them (whether a stream was
flushed or closed). That the compiled lowering behaves as the model is tested, not proved.

**What is proved and what is trusted.** Proved: the checked `run_io`, at any implementation of
its externs that meets `ExternsMeet`, runs safely from every input to a value at the empty memory
(`externs_every_run`), and at the models does (`IORun.every_run`). Trusted at the I/O boundary:
that each host implementation meets its extern's contract, the one hypothesis `ExternsMeet`
names, unconditionally (at every call, record list and lifetime substitution). The harness's
makes and takes are host implementations like the operations and sit at the same boundary; a
backend adds no code of its own around `run_io` that makes, takes, copies or consumes a value. That
a backend compiles the checked term faithfully is the compiler's obligation (`docs/compiler.md`), outside this
boundary, and is tested, not proved.

### Assurance

Each extern records its assurance level, on the ladder of decision 27: (1) assumed,
(2) interpreter-checked, (3) property-tested, (4) typed low-level (typed unsafe code),
(5) boundary-checked, (6) semi-automatically verified, (7) proved. `bcc trusted <file>` lists
every extern `main` reaches (§34) with its level and its implementation; an unproved boundary is
the program's trusted base.

| extern | model | host implementation |
|---|---|---|
| `stdin`, `stdout`, `stderr` | proved (7): cells with the model content | the heap cells `run_io` makes by `mk_input` and `mk_output`, holding the fd; assumed (1), checked against the model on the corpus |
| `read_byte`, `write_byte` | proved (7) | WASI `fd_read`/`fd_write`; interpreter-checked (2): the flat-IR interpreter runs the lowering against scripted streams |
| `write_all`, `read_into` | proved (7) | WASI `fd_write` of the view, again after a short write; `fd_read` into the view until it is full or the input ends; interpreter-checked (2) |
| `mk_input`, `mk_output`, `take_input`, `take_output` | proved (7) | host functions: a make allocates a fresh heap cell holding the stream's descriptor (`mk_input`: `0`, its argument, a byte list, consumed whatever it holds, the stream being the platform's standard input; `mk_output`: its argument), as the model's `alloc` does at every call; a take frees the cell, answering the empty list (`take_output`: the descriptor and the empty list). Assumed (1), each claimed to meet its extern's contract at every call, with no condition on the run |

An extern the compiler has no implementation for is reported as assumed and not compiled.
`bcc trusted` lists, beside the externs `main` reaches, the harness externs `run_io` calls.

### Lowering

Both backends compile `IORun.expr r []` for the compiled form `r` (`Backend.CheckedProg.runIO`):
the checked `run_io` applied to its argument `IORun.arg []`, the empty byte list, with each extern
bound to its host implementation: the operations, and the harness's makes and takes as host
functions (`Backend/Clos/Convert.lean`, `mkValue`, `takeValue`; `Backend2/Convert.lean`,
`mkClosOf`, `takeClosOf`). The application is converted as the term holds it, the argument a
value of the term; an extern the term does not use is not made. The compiled `run_io` is built
with no arguments in the term: `mk_args` is passed the empty list, and its host's stream is the
host's arguments; `bcc interp` builds `run_io` with the run's arguments as that list. The
program's input is the stream `mk_input`'s host gives `stdin`, descriptor 0. The compiled form's
value is `main`'s result `a`, which the platform prints: the term takes the outputs back and
weakens them, their byte lists empty, since each byte went to its descriptor when it was written.
Each capability's cell is a heap cell, allocated by a harness make and freed by a harness
take inside the compiled term. `read_byte` is WASI `fd_read` of one byte from
the cell's descriptor (end of input, or an error, is `inr ()`); `write_all` is `fd_write` of the
view's bytes, called again after a short write; `read_into` is `fd_read` into the view, called
again until it is full or a read answers nothing; `write_byte` is `fd_write` of one
byte. Both are unbuffered, so a prompt appears before the next read. The plain LLVM/libc
counterpart is `read(2)`/`write(2)` on the same descriptors (or `getc`/`putc` on a `FILE *`): no
WASI-only feature is part of the semantics (decision 25).

### Programs that run until their input ends

`main` may return a loop over its capabilities:

    main : F (U (Loop (Caps ⊗ A) (Caps ⊗ B)))

The runtime drives `run_io`'s loop (below): it observes `next` until it finishes, `run_io`
having taken the capabilities back when `main`'s loop finished with `(caps, a)`, and prints `a`;
it never closes it. A `main` with no externs may return a
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
- **A lending call in tail position** (the last expression of a function, a `with` body, a block
  or an arm) that lends one place is `let r = f(…, &p, …); r`, the head's form: the place is
  rebound from what the call hands back and the call's answer returned. At a row whose
  operations the call performs, the typed pass reads it as that binding, so the borrow is the
  unwinding form at those operations (§18); elsewhere the last step of the lend sugar
  (`Comp.elab`) does, as for a head. A refusal of such a call names the function as written, not
  the copy the elaborator makes for its handlers (`get_or_fail`, not `get_or_fail__n1`). A tail
  call lending two places is refused, as in a head.
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
- Consumes for host resources, which perform I/O and can fail (§12 Open).
- `main` with borrowed capabilities (lifetime-parametric externs) is not provided.
- `Env`, `Exit`, `Fs` and the rest are designed only; `Args` and `Clock` are §34's.
- `|>` pipelines (#59) are §33's.

---

## 12. Entry 11 — implicit consumes

Types stay linear. Where a program lets an owned value go unused, the checker inserts a call
of the value's **consume**, and that call is the value's one use. The elaborated program is an
ordinary linear core term with an ordinary `CDerives` derivation, so every owned value is still
consumed exactly once, and leak freedom is `adequacyC` on the elaborated term. No typing rule,
judgment index or semantic definition changes. The consumes and their derivation are
`Core/Consume.lean`'s.

**Vocabulary.** A value type is unrestricted or linear; there is no third class. A linear value
is *consumed* exactly once: by a rule that uses it or, at a **consumable** type, by the type's
**consume**, the type-directed operation that uses the value up. A consume may free cells or may
not:
- at a borrow (`Imm`, `Mut`, `Unk`, `ArrayImm`) it **releases** the borrow: the loan ends and
  returns to its lender, and nothing is deallocated (the `release` constants, `CDerives.releaseImm`,
  `releaseMut`, `releaseUnk`, `releaseBang`, `arrRelease`; the types whose consume does nothing
  are `Releasable`);
- at `Ref A` and an array it **frees** the cells, with the primitives `[free]` and `array_free`;
  only these primitives are called free;
- at codata it runs the object's **close**.

An unrestricted slot is **weakened** (`Ctx.DeadP.weaken`), which is a rule of `CDerives`, not a
consume. A continuation is *resumed* or *cancelled*. Closing a host resource (a file) is not a
consume and not a kernel rule: it is the API of the resource's effect, written with linear types in
the library (decision 73).

Names follow one rule. The class is `Consumable` (decided by `consumableB`, and in a `μ` body's
mode by `consumableAtB`); `LinearConsumable A` is `Linear A ∧ Consumable A`. The consume of `T`
is the closed function `consumeE T` (`consumeAt` with the mode, typed by `consume_wf`). The
checker's insertion of it at slot `i` is `consumeSlotE T i e` (licensed by `consumeSlot_derives`)
and appears in the typed term as a `consume` node (`TExpr.consume`); Backend2 lowers the node to a
`consume` at a `ConsumeRule`, and the consume of a type to a consume function (`Prog.consumeFns`).

### Consumes

`consumeE T : T ⊸ F 1` is a closed term, defined by one structural recursion on `T`
(`Core/Consume.lean`; with `algsIn`, which lists a `μ`'s algebras, one mutual recursion, §61). `Consumable T` is the class of types it is defined at, and `consume_wf` types it
in `CDerives` at every lifetime context and every dead context, using existing rules only.
The kernel has two classes of value type: **unrestricted** (persistent, §10) and **linear**
(every other). A consume (`LinearConsumable A`: `A` linear with `Consumable A`) and a derived copy
are properties of a linear type, not further classes (`Core/Classes.lean`). By their consume,
value types fall in three groups.

1. **Releasable types**: the types whose consume does nothing (the unrestricted ones and
   the borrows): the persistent types (§10: `1`, `0`, `I32`, `I64`, `Unk`, `!A`, and
   `⊗`, `⊕`, `[@a]`, `μ` over them), the borrows `Imm @a A`, `Mut @a A`, and `⊗`, `⊕`, `[@a]`
   over these. The consume is `forget = λx. ()` (at a borrow, the `releaseImm`/`releaseMut`
   constant), componentwise at `⊗`, `⊕`, `[@a]`. Discarding one does
   nothing: it deallocates nothing and runs no code, and ending a loan early is safe. The
   unrestricted ones are already consumed by context splitting (§10), with no call. Every type of
   `Core/Records.lean`'s `Releasable` is here (`consumable_of_releasable`).
2. **Owned types that are consumable.** The consume is an action:
   | type | consume |
   |---|---|
   | `A ⊗ B`, `A ⊕ B`, `[@a] A` | componentwise |
   | `Ref A` | `free`, then the consume of `A` |
   | `μX. T`, `T` in `FShape` (§6) | `foldOwn`, whose algebra is the consume of `T[1/X]` |
   | `μX. T`, `T` in `P` (§6, §61), not in `FShape` | `foldOwnG`, whose algebra at each key is the consume of the key's body (an array key's element type) at results `1` |
   | `U(C & F 1)` | `close`: force, then the second projection |
   | `U(νX. C & F R)`, `R` closed and consumable (`D A`, `Stream A`, `Iter A R₀ R`, `Clo^c A B`) | `close` (§7), then the consume of `R` |
   These are linear. A value of one of these types that goes unused is consumed by its
   consume, which the checker inserts. Because the consume deallocates memory and, at codata,
   runs the object's `close` code, where it is inserted can be observed.
3. **Types that are not consumable**: `U C` other than the codata above (a thunk of `F A` or of
   `A ⊸ C` can be disposed of only by running it, which has effects and may need an argument), `μ`
   outside `P` (§61), a type variable, and anything built from one of these. These are linear
   that is not consumable.
   A variable of one of these types must be consumed, and an unused one is a type error that
   names the type.

### Insertion policy

A variable is **owed** to the body of its binder (`x <- M; N`, `let (x, y) = V; M`, a `case`
arm, `fun (x : A) -> M`) exactly when its type is linear and consumable (group 1 or 2, not
persistent): `Env.pushOwn` owes a slot exactly when `LinearConsumable A` holds (`Env.pushOwn_own`). The
body must consume an owed variable on every control path; on a path that
does not, the checker consumes it by its consume:

- **At the end of the path.** The consume calls go immediately before the path's terminal
  computation: `return V`, `force x`, an application, a projection, an instantiation,
  `nu_out`. They go after every effect of the path and before the result is
  produced. A value never used is therefore consumed at the end of its binder's scope, and a
  `case` arm or a `<M, N>` component that does not consume an owed variable consumes it, while one
  that does, does not.
- **In reverse binding order.** Several owed variables are consumed most recently bound first.
- **Tail positions.** The owed set passes to the body of `x <- M; N`, `let () = V; M` and
  `let (x, y) = V; M` (without what `V` or `M` consumed), to both arms of a `case`, both
  components of `<M, N>`, the bodies of `fun` and `Fun`, and through `nu_in` and
  ascriptions. An owed variable that the head `M` of `x <- M; N` mentions is owed to `M`, which
  must then consume it on every path of `M`, consuming it where it does not.
- **Handled bodies.** A handler site `handle[k] (H) M` (a `with`; every `for` body, a per-iteration
  handler; the budget's site of a recursion) is not terminal: an owed variable that the handled
  body `M` mentions is owed to `M`, as to the head of `x <- M; N`, and the others are consumed
  before the site, at its end of path. So a path of `M` that ends in an abortive operation (a
  `raise`, a budget's `exhausted`, a loop's exit) consumes before the abort what `M` is owed and
  that path has not used, and a `case` in `M` whose one arm aborts and whose other uses such a
  variable merges. The handler's pair uses only persistent slots (`[handle]`'s `Γ₁`), and an owed
  slot is never persistent, so the split of the site is unchanged; a variable `M` mentions is used
  by `M` on every path already, so the outlives premise of a boxed `κ` (§28) asks nothing new. The
  consumes are `consumeOne`'s nodes, and `[handle]` and `[sub]` are unchanged. The variables `M`
  does not mention stay consumed before the site, where they were. (#848, #492)
- **Captured variables.** A computation inside a value (`thunk M`, `thunkv N`, `run M`: a borrow
  block's callback, a closure, a handler's clause) is owed the owed variables of the computation
  the value is in that it mentions, as the head of `x <- M; N` is; the others stay with that
  computation. "Owed to the computation the value is in" is what its terminal computation was
  owed before its own consumes (`Env.clearOwn`), or, for a value of a `let`, `case` or `<-` head,
  what that form is owed (`Env.forVal`); both are held in `Env.cap` and handed to the inner
  computation by `Env.capture`. So a path of the callback that ends in an abortive operation (a
  `raise`, a recursion's budget `exhausted`) consumes before the abort the captured variables it
  has not used, and a `case` in the callback whose one arm aborts and whose other uses a captured
  variable merges. Sound against the kernel: `thunkF` and `thunkV` type the body in the thunk's
  own context, whose slots are exactly what it captures, and the body must use each linear one
  on every path, which an owed slot gets by `consumeOne`'s nodes; a variable the body mentions is
  used by the body already on the paths that mention it, so the thunk's context, and the split of
  the value it is in, are unchanged. A captured variable is consumed later than before, at the end
  of the callback's path instead of before the terminal computation of the enclosing path, which
  §12's *Not moved across effects* allows: it is never earlier than the path's terminal
  computation. A `!` thunk uses only persistent slots, and an owed slot is never persistent, so it
  captures nothing. `[thunkF]`, `[thunkV]`, `[ofRet]` and `CDerives` are unchanged. (#891)
- **Not moved across effects.** A consume is never placed earlier than the path's terminal
  computation. Codata `close` runs code, so moving it would reorder effects.
- `<>` and `absurd V` absorb any context (§11 of `docs/syntax-core.md`), so no consume is inserted
  before them. A value owes nothing itself: a computation inside it is owed only the variables it
  captures (*Captured variables*), and a thunk that captures a variable consumes it.

**A value that must not be consumed.** A value whose silent destruction is a bug, such as a
transaction that must be committed or aborted, needs a type in group 3, which the program must
consume on every path. A field marked `must_close` in a data declaration (§42, *Declared types
that is not consumable*) holds `Tok` (§11), so the declared type is linear and not consumable
(`decl_linear`), and so is every type that holds it (`not_consumable_tensor_right` and the closure
lemmas of `Core/Decl.lean`). The checker inserts a consume only as a `consume` node of the typed term,
which carries `Consumable` (`TDerivesP.consume_consumable`), so it inserts none at such a type. A borrow of
one, `Imm @a N` or `Mut @a N`, is linear and consumable (`decl_imm_consume`, `decl_mut_consume`): the
loan ends, the value is not consumed.

### The derived copy at `imm`

`Imm @a A` and `[Imm @a A]` are linear with a **derived copy** (`DerivedCopy`, `Core/Classes.lean`):
the constant `copy` (`CDerives.copy`, at `axCopyTy`) or `array_copy` (`CDerives.arrCopy`, under
`bangE`) makes two of one, and `copy_derives` types `copyE A i e`, the copy of `xᵢ` with `e` under
both copies. A use of such a variable beyond its first is its derived copy, which the checker
inserts as it inserts a consume. The split is unchanged (`overlapOK`, `Ctx.SplitP`): a slot
both parts use is admitted at a persistent type only, so `imm` stays linear, and a second use of a
`mut` borrow, an owned value, a declared value or a capability is refused there ("`x` is used
twice here, and its type `…` is linear").

- **Where.** At a node whose context the checker splits between two parts that run in sequence,
  each variable both parts mention free (`mentionsV`, `mentionsC`, which respect binders) whose
  slot is `DerivedCopy` (`derivedCopyB_iff`) is copied before the node:
  `p <- return (copy xᵢ); let (x₁, x₂) = p; node`, the first part checked where `x` names `x₁`,
  the second where it names `x₂`; the copies are owed as any binder's (above). The nodes and their
  parts: `(V, W)`; `V W` (`W`, then `V`); `x <- M; N` (`M`, `N`, at `[let]` and `[then]` too);
  `x <- M unwind (D); N` (`M`, then `N` and `D`); `let () = V; M` and `let (y, z) = V; M` (`V`,
  `M`); `case V {…}` (`V`, then both arms); `M y` (`M`, `y`). A value split holds no binding, so its
  copy is under `run` (`ofRet`). Several variables nest, in slot order. The rule is decided before
  the parts are checked, so each is checked once (`Frontend/Check/DerivedCopy.lean`).
- **Not here.** A merge (`case` arms, `<M, N>`, `[then]`'s continuation and finaliser) uses a
  variable once per side. A handler's clauses use only unrestricted slots (`[handle]`'s `Γ₁`),
  `!thunk` only flat slots (§10), and a relaxed lend's body only its view: an `imm` there is
  refused with those rules' messages. Inside a thunk, a clause's body, a loop's or a fold's generated function
  or a `def`, the rule applies at the splits there.
- **The kernel rule.** `copyIt` builds the term from `rVar`, the constant's node, `rLolliE`,
  `rRet`, `rTensorE` and `rBind`; its erasure has `copyE`'s shape with the kernel's `copyC A`
  (`copyIt_erase`). A `copy`
  node is typed only at `axCopyTy a A` and an `array_copy` node only at `arrCopyTy a A`
  (`TDerivesP.copy_at`, `TDerivesP.arrCopy_at`), each `DerivedCopy`, so no inserted copy is at
  another type whatever decides where it goes.
- **Mention is use.** A part mentions a variable only at `var` leaves, which its masks keep, and
  the checker consumes only slots a part owns, so a part uses a slot exactly when it mentions its
  variable: the rule is the split's own masks, read before the parts are checked, so it fires
  only where the split would refuse a `DerivedCopy` slot. `copyUsed` checks at every insertion that each
  copy is used or consumed by its part (one neither is an internal error).
- **Not covered.** A tuple of borrows is not `DerivedCopy` (a kernel change would widen it). The
  elaboration's own `array_copy` in its templates is unchanged (below). `clone(x)` stays the written
  copy of an unrestricted value.
- **Pinned.** The copy constant's node records the variable and that the checker inserted it
  (`TInfo.inserted`); `bcc copies <file>` prints each, and `corpus/copies/<name>.txt` pins them for
  `corpus/<name>.bc` (`scripts/check-corpus.sh`): what `main` reaches, a `def`'s body once per
  use.

### Every insertion site cites its rule

Every stage that inserts a consume, a copy or an abandonment names the kernel rule it emits.
`scripts/check-pins.sh` (a gate step) runs `scripts/PinSites.lean`, which checks that every rule
names declarations that exist and, where it is not proved, a `def … : Prop` stating what it needs;
that each backend site builds nodes at exactly the rules its entry lists, and no definition chooses
a rule apart from the node it builds; and that the elaboration emits the copy, release and burn
constants only at the sites it lists. The script's negative tests (a site the table omits, a rule
chosen in a definition of its own) must be refused (#746):

- **The checker** inserts a consume only as a `consume` node (`rConsume`, `finNode`), typed by
  `TDerivesP.consume`, which carries `Consumable`; erased, it is `consumeSlot_derives`. Every checked program
  projects to `CDerivesP` (`checkProgram_soundP`), so the checker needs no table of sites. It
  inserts a copy only as a `copy` or `array_copy` node (`copyIt`), typed only at `DerivedCopy`
  (`TDerivesP.copy_at`, `TDerivesP.arrCopy_at`); `bcc copies` lists them (above).
- **The elaboration** emits `tok_burn` only where it compiles a written `match` (`Data.compile`,
  through `Data.burnBind`), `array_copy` only in a template's view (`CDerives.arrCopy`), and no
  other copy or consume of its own: a field read, `*e` and a `for` over an owned array copy only at an
  unrestricted type (`Class.of`), and the checker inserts every consume. An operation is abortive by
  the kernel's `isAbortive` (`OpDecl.abortive`, `Sugar`'s clause types).
- **Backend2**'s `consume`, `copy` and `abandon` nodes carry their rule (`Backend2.ConsumeRule`,
  `CopyRule`, `Abandon`), and `Lint` checks each rule's premise on the variable's type at every
  node:
  - weakening (`dead`: a leaf's other slots, a `use`'s unread slots, a handler's values by
    `effHandleV`'s `DeadP`, a pure frame's arguments at an abort, the machine's own words) and a
    split's `dup`, at an unrestricted type;
  - the `release` constants at a borrow, `Unk` or `[Imm A]`;
  - a consume's leaves, `[Mut A]` among them (`Consumable.arrayMut`), only in a function the
    consume calls to consume one (`Prog.consumeFns`, checked per function);
  - the `copy` constants and the derived copy (`copy_derives`) at `DerivedCopy`;
  - `abandon` at `[let]`'s abort (`hW`) and at a superseded raise payload (`effRaise`'s `hd`), at a
    type with no owned cell; at `⊤`, anything.
  A live slot no part's mask holds is consumed at the rule `unused`, at a persistent type only: the
  weakening its part applies at its leaves (`Ctx.DeadP.weaken`). At `absurd`'s own split such a
  slot is absorbed, left unconsumed on the path that ends at `absurd` (§66), and `⊤` abandons its
  context; a slot another rule leaves in neither part at another type is refused by `Lint`, not
  consumed; that no checked program has one is `UNPROVED:` (`Check.SplitMasks.NeitherAbsorbed`, which `neitherAbsorbed_of` reduces to
  `Check.UnmentionedAbsorbed`). A must-resume `κ`'s cancel component is `⊤`, which has no
  elimination: `Lint` refuses an observation of it, and its cancel entry is unreachable (`kTy_lin`).
  `[nil-dead]` is at a context with no live slot. A stack machine's consume of a level's suspended
  computation is the rule `stackK`, a hand-over (§52, *The hand-over*): `Lint` reads its premise
  from the node (`Lint.handsOver`), and the rest is `UNPROVED:` (`Backend2.StackKHandOver`, F3).
- **The old backend** converts the erased term, so its `copy` and `consume` carry a licence
  (`Backend.Clos.Licence`) naming the rule each site relies on. None is read from the typed term:
  each is `UNPROVED:`, its statement `Clos.LicenceSound` at it (a checked program whose closure IR
  has a node at the licence runs there to `()` with no object left). The licences are not checked
  against the program.

### Soundness

The elaborated term, with consumes inserted, is what the checker returns, as the erasure of its typed
term (§3), with its `CDerives` derivation (`checkProgram_sound`). The consume is `unitE` over `lolliE` of the variable and
`consume_wf` (`consumeSlot_derives`). `fundamentalC` and `adequacyC` apply unchanged, so the baseline theorems
(§1) and every theorem of entries 1–10 are preserved; nothing in them is touched. Placement does
not affect soundness: any placement of a consume call is a `CDerives` derivation. The policy
fixes when the effect of a consume happens.


A stored generator over a row is not consumable; it is dropped at its row, by a close, at scope end
or just before a tail call (§15 *Stored generators over a row*).
### Open

- **Host resources are not consumed.** A host resource (§11), such as a file handle, is group 3.
  Closing it is the API of the resource's effect, written with linear types in the library,
  not a consume and not a kernel rule (decision 73). `consumeE` is total and pure apart from
  deallocation and `close`.
- **Externs** are not owed. `main` must consume every non-persistent extern.
- **Values** do not consume. The value `V` of `let`/`case` and the operands of value forms consume
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

**The residual.** A loop closed early must give up its state. What is consumable (§12) is
consumed, and what has none, such as a capability (§11), must be handed back. The residual of a
result `B` is `K ⊗ 1`, where `K` is the tuple of the components of `B` (its right-nested `⊗`)
whose type is not consumable, in their order in `B`; it is `1` when there are none, so `div B` is
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
by whichever observation runs, and consumed (§12) by the other where they have consumes. If
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
  consume.

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
other variable of the state is consumed (§12).

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
`↭` brackets every borrow cell inside one run (`experiments/LoopBorrow`), and a lend that spans
observations is refused (T1, §19: the checker's rule until surface A1, #843, for §62's shapes). The
design is to **lend again at each observation**, with no new rule: the owner lives in the loop's state, and each step borrows it by an
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
- **A load block whose body loops** (`borrow imm *g { 'y, v -> S }`, §36) is rewritten per
  observation only when the loaded content is persistent: the content is bound first,
  `let t = *g`, a copy, and `t` is lent at each step. A load of a linear content is not
  rewritten: it is elaborated as a load (§36), its body, loops included, in place, where the
  types of the loop's sources are known. A `for` over data there is the counted loop (§16), and a
  loop that ticks (an operation that resumes) is refused as any borrow across a suspension is.
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

**Not covered** (each would hold a borrow across a loop's tick, which T1 rules out
(T1, §19: the checker's rule until surface A1, #843, for §62's shapes), or needs a construct not built): a pipeline whose source holds the borrow, `for x in map(filter(iter(xs), p), f)` inside `borrow imm v { xs -> … }`. The
source could be rewritten to hold the owner, but the owner would come back only through the
pipeline's finishing value and residual: each adapter would pass them on, the `for` would bind
the finishing value, and the residual would have to hand back an owner that is consumable. A
`yield` inside a borrow block is rejected (§15, *Self-reference*). A div
function called with a borrow that is not lent from a place (a view, a field, a second borrow)
holds it across its loop. `|>` is §33's.

Programs: `corpus/axes/borrow-across-loop.bc`, `corpus/lend-mut.bc`, `lend-config.bc`,
`lend-pipeline.bc` (0 allocations, dispatched calls and copies beyond the table's own),
`lend-server.bc`, `lend-div.bc`, and the library's `lend-lib-loop.bc`, `lend-lib-gen.bc`,
`lend-lib-each.bc`; pairs `corpus/sugar/lend-block.bc`, `lend-let.bc`, `lend-div.bc`; rejects
`corpus/reject/lend-*.bc`. Every elaborated program is checked core, so `fundamentalC` and
`adequacyC` cover it. The per-observation lend is kept until surface A1 (#843, §19): its output is core the kernel checks. Each refusal above names its fix: iterate
by index or with a counted `for`, copy the value out, or end the borrow before the loop.

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

One call (§50's `willreturn`): `total_open`, a computation of `F B` (the empty row) in a context
`Γ`, closed by values in the relation at a tagged typed world whose completion lowers to `μ`,
reaches a value under every allocator (`fundamentalC` at the closing substitution, unpacked as
`total_every_alloc`); `total_call`, its instance at one argument; `total_open_pin`, the same under
`PinLaw`; and `total_subrun`, every redex a closed program's run reaches in a plain context runs
to a value (`total_every_run`, then `steps_plug_inv`).

"Div-free" is the type: a closed computation of `F A` is total, whatever it calls inside, since
a loop it holds is observed a finite number of times (by `div_fuel`, or not at all). A program
whose `main` loops is covered one prefix at a time instead (§11, `externs_loop_every_run`).

### The effect `Div` in the kernel

Divergence is also an effect the kernel handles (decision 67; `docs/pipeline-architecture.md`
§3.2). The kernel has it; the frontend keeps the elaboration above, with no `Div` in any row it
writes, until B2 (#563's successor) elaborates loops to it.

**The effect.** `Div` is the reserved name `divEff = 2³² − 1` with one must-resume operation

    tick : 1 ↠^lin Next        Next = 1 ⊕ 1        next = inl (),  close = inr ()

(`Core/DivDefs.lean`, `tickSig`). A row **holds `Div`** when the operation it finds at
`(divEff, 0)` has `tick`'s signature (`CTy.divAt`, `Row.divB`). `tick`'s continuation must resume:
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

- **`[then]`** at a row holding `Div` (`cwp_then`, `cwp_then_div`): a finaliser whose row is
  `Div`-free terminates by totality; one whose row holds `Div` (`effThenDiv`, §29a) puts `Div` in the
  enclosing row, which must be handled (`div_fuel`, `driveE n`) before the program is a closed
  `F A`. No separate rule is involved. A finaliser may perform operations and raise.
- **`[handle]` of another name around a computation that ticks** is typed only when its clauses
  resume `κ` in tail position (decision 68, a temporary restriction #564 lifts): `effHandleT`
  (`Core/DivHandle.lean`) writes the clauses out from a tuple `gs` of answering functions
  `g : !U(A ⊸ F_{Σ_N} B)`, `Σ_N ≤ Σ` a row of must-resume operations, as
  `λ(x, κ). (λw. κ.1 w) (g x)`, and an abortive operation's clause as `g : !U(A ⊸ F_Σ R)`.
  `effHandleV` and `effHandleVB` ask the handled row not to hold `Div`. A handler whose clauses are
  all abortive is `effHandleT` at an η-expanded clause tuple. A clause that works, then resumes `κ`
  in tail position or cancels it and leaves, with `κ`'s cancel its unwind finaliser while it works,
  is `effHandleL` (§51).

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
- **A loop source bound inside the body is not typed by LoopLend** (one bound in a `match` arm,
  say), so a load of persistent content whose body loops over such a source is rewritten per step
  with the source's type not known there.
- **`[handle]` of another name at a clause given `κ`** around a computation that ticks
  (`handle_general`, #564), beyond `effHandleT`'s and `effHandleL`'s (§51) classes.
- **Finalisers are total, as a theorem** (decision 69): every run of a finaliser whose row is
  `Div`-free terminates, the handler clauses its operations reach included. Its own run is a least
  fixed point (`ewpTS`): it performs finitely many
  operations, each segment finite. A clause it reaches runs at the handler's outer row: at
  `effHandleV` and `effHandleVB` that row is free of `Div` and the clause's run is a least fixed
  point too, but an `effHandleT` clause's answering function is at a row `Σ_N` that may hold
  `Div`, and may tick without end, as may an `effHandleL` clause's work (§51). Not proved.
- The model interpreter (`bcc interp`) copies the remaining input on every read.

---

## 15. Entry 14 — generators

### Motivation

A producer is easiest to write in direct style: a loop that `yield`s each element, with the
consumer deciding how many to take (#18, #107, #109, #188). Here yielding is an effect like any
other (decision 54): `Yield[T]`, a library effect (`lib/yield.bc`) whose one operation,
`ctl yield(x: T)`, is cancellable. A generator is a function that performs it,
`fn range(lo: i32, hi: i32) -> 1 with Yield[i32]`; a `for` over a call of one handles it (push); and
a call stored where a value is expected is the generator's **stored generator**, codata that a
consumer pulls. There is no generator type former and no iterator trait: everything below is
elaboration into §19's `handle`, `perform` and §7's `ν`, so the kernel, the checker's rules and the
proofs are unchanged.

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
  (its owned values consumed, §19's consume glue), and leave with the variables and the exit. The
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
  operation, and a cancellable continuation at a non-empty cancel row is not consumable (its
  cancel performs at the site's row, so it cannot be consume glue), and a clause is total. The `for`
  then observes `g`'s stored generator instead (below), a loop of the enclosing body.

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
  no consume, as a stored generator's must be (below).
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
`U (pull A K K)`; a source that fails raises, and is closed as a pure one is (*Stored generators
over a row*, below). A pipeline of adapters whose functions are known
allocates nothing and dispatches no call (`corpus/gen-pipeline-adapters.bc`: 0, 0, 0;
`gen-adapters.bc`, `gen-adapters-fail.bc` at their previous counts).

### Stored generators over a row (#910)

- A call of a generator `g` at a stored generator's place is stored whatever else `g` performs.
  Let `Σ` be `g`'s row at the call, less its iteration effect's site. The stored generator is
  `U (pull_Σ A B R)`:

      pull_Σ A B R ≜ νX. F_Σ((A ⊗ U X) ⊕ (B ⊕ U X)) & F_Σ R

  `pull A B R` is `pull_[] A B R`.
- An observation performs `Σ`: a `raise` inside `g` propagates out of the `next` that ran it, to
  the handler around the consumer. `close` is the cancel of `g`'s continuation, and the kernel
  types that at `F_{fin ⊕ Σ} 1` (`cancelTy`, §27), so it is at `Σ` too. The pull view's clauses
  answer at `F_Σ`.
- `pullView` (`Frontend/Sugar.lean`) carries `F_Σ` through the view. `pullSite`
  (`Frontend/Elab/Effects.lean`) stores it. The kernel's ν rules admit effectful leaves
  (`CTy.NuOk`), so nothing changes in Core.

**§12/§19 consume glue (the checker's `finalOf`).** A slot live across an operation that may be
cancelled or abort is consumed by `[then]`'s finaliser. Another case is a value that
is *dropped at a row* (`dropRow?`): a stored generator over a row `U (νX. C & F_{Σc} R)` (`Σc`
non-empty, `R` consumable), or a value built by `⊗` and `⊕` from such generators and consumable
types (`zip`'s state). Such a value is not `Consumable`, because `consumeE` is at `F 1`. It is
dropped at its row instead (`dropOne`):

- a generator is closed: `y <- (nu_out (force x)).2; consumeE R y`, at `Σc`;
- a pair is taken apart, `let (x, y) = v`, and a sum is split, `case v`, and each part is dropped;
- a consumable part is consumed.

The finaliser's row `Σ_D` is the union of the `Σc`. `[then]` (§27, `rEffThenD`) decides its
premises: `Σ_D ≤ Σ`, and every capturable operation's cancel row holds `Σ_D` (`thenFinB`).
Each close is a `[then]` whose own finaliser is the rest of the drop (`closeThen`). So a raise
from one close still closes the others, and each generator is closed exactly once.

**§12 where a dropped-at-a-row value is dropped.** Drops happen at scope end, as in Rust,
except that at a tail call they happen just before the call, as Rust's `become` does (RFC 3407).

- A value dropped at a row is owed to its scope like a consumable slot (`Env.pushOwn`).
- On a path that ends without using it, it is dropped at scope end, as #868's rule has it
  (`consumeOwedR`, `dropOne`): before a terminal that is a value, after the path's last effect;
  after a terminal that performs (an operation, a call that is not a tail call, a handler site),
  `x <- T; drops; return x`, as Rust drops after the block's last expression.
  Its generators are closed by `y <- close; consumeE R y; T` (`closeBefore`, the terminal placed
  under one more dead slot by `TTied.weaken`). A terminal whose type performs nothing cannot close
  it, and is refused there with that reason.
- On a path that ends in a tail call, it is dropped just before the call: after the rest of the
  path, in `become`'s order (the call's arguments, then the drops, then the jump). The bindings
  that perform nothing just before the call, `x <- return V` with `V` performing nothing
  (`Comp.becomeRun`: the call's A-normal argument bindings, and any `let` of a value before them),
  are placed after the drop rather than before it (`becomeDrops`, `dropsBefore`): they perform
  nothing, so the order is observably `become`'s, and the function value and the arguments they
  bind are not live across a close that may raise. Every binding that performs something stays
  before the drop. The call stays in tail position. The checker
  reads `V`'s effect-freedom off the term (`Val.runFree`: no `run` in it).
- That holds only when every value the call takes is bound by those bindings, or is one a raise
  can drop (`dropRow?`). When the call takes a linear value bound by a binding that performs (a
  stateful handler's result handed back by the call after a `with`), the drops are at scope end,
  after the call, and that call is not a tail call: Rust's ordinary drop order
  (`corpus/gen-raise-with.bc`).

**§27 cancel rows (Phase 2's `Fins`).** A function that holds a stored generator over a row
across its own operations is a finaliser site of the checker's glue. A function whose parameter
is `U (pull_Σc …)` runs that close when one of its capturable operations is cancelled. So each
capturable operation of its row gets `Σc`'s entries in its cancel row: its `yield`, at the `for`
site that consumes it, becomes `cancel[Fail]`. The table is unioned per name, and the
kernel checks every row.

**§15 adapters (`lib/adapters.bc`).** These are generic over the source's row with no change to
their code. A call whose stored-generator argument is over a row `Σ` is a copy of the adapter at
`Σ`, as a call with an effectful block is a copy at the block's row (§30):

- the parameter's type is `U (pull_Σ A K R)`;
- every place the body writes a stored generator's type (`zip`'s state annotations) gets its row
  by inference, each occurrence its own (`Elab.withRows`, `Elab.refineAsc`): from what flows into
  it (the value ascribed, through its pairs and injections), else from what it flows to (the type
  expected of it, the variable an assignment rebinds, the other arm of a `case`). An occurrence
  that nothing with a row reaches keeps its written row. So a pure stored generator a copy
  binds itself stays pure, and two parameters at different rows keep theirs. The checker
  re-checks every annotation;
- the copy's row is its own row (its `Yield` at the consumer's site) and `Σ`'s sites;
- the copy is keyed by `Σ`'s sites (`b{j}n{n}…`, as a block's).

A copy at `Σ` passes its parameter on: a call in the copy whose argument at a stored generator's
parameter is that parameter is a copy at `Σ` too (`pullArgsV`), in tail position as elsewhere.
The parameter is followed through `let x = y`, through pairs built of it and taken apart again
(`Cx.shapes`), and through copies (`Cx.pulls`).

Which stored-generator parameter a call has is read off the callee's own declaration
(`Env.pullArgs`), not the first template of its name: `take` of `lib/buf.bc` does not hide
`take` of `lib/adapters.bc` when both are included (`include rec` brings `buf`).

Every row the elaboration writes (the machine's `F[…]`, a site's clause rows, a counted loop's
row) is written with each entry's cancel row (`opSrcM`).

Types, at a source's row `Σ`:

    map[A, B, K, R](it: U (pull_Σ A K R), f: !(A => B)) -> K with Yield[B], Σ
    take[A, K](it: U (pull_Σ A K K), n: i32) -> K with Yield[A], Σ
    … (filter, skip, enumerate, chain, flat_map, take_until, scan, zip, chunks, lines, batch alike)

A source that fails raises. `take`, `take_until` and `zip` close a raising source as they close a pure one, and the
close runs at `Σ`. `corpus/take-failing.bc` takes a raising `upto`.

**Baselines.**

- No `CDerives` rule, relation, machine or Core change. `fundamentalC`, `adequacyC`,
  `fundamentalD` and `adequacyD` keep their statements. The new glue is `[then]` at `Σ_D`
  (`rEffThenD`, #868 Phase 1).
- Every corpus and kernel program keeps its output and its counts. A program with no stored
  generator over a row is checked and erased byte for byte as without this entry: `pull_[]` is `pull`, the
  copy keys are unchanged, and no cancel row grows. Its desugared text writes out, wherever it
  stores a generator, the pull view's clause types as `!U (A -o F B)` and its `iter` as `nu Y. …`. Their keys (which hash the term the interpreter runs)
  are unchanged.
- Every borrow guarantee. A stored generator over a row is linear like any other: it is closed by
  the glue, never dropped.

**Programs.**

- `corpus/gen-raise-take.bc`: a tokenizer stage that raises `ParseError` on malformed input,
  under `map` and `take 3`, raised to an outer `to_result`. Its source, which owns a list, is
  closed by cleanup exactly once on both paths: linear (at most once) and `live 0` (at least once).
  Answer `(inl i32[98], inr i32[5])`.
- `corpus/gen-raise-fold.bc`: a raising `try_fold` that is a plain `fold` with `to_result` attached;
  the step raises, or the source does. Answer `(inl i32[10], (inr i32[21], inr i32[1004]))`.
- `corpus/take-failing.bc`, its source raising. Answer
  `(inl i32[1], inr i32[4])`.
- `corpus/gen-raise-zip.bc`: `zip` over two raising sources. `(inl i32[66], (inr i32[3], inr i32[20]))`.
- `corpus/gen-raise-close-two.bc`: two sources whose closes raise, closed by one drop; the second
  close is the first's finaliser. `(inl i32[11], (inr i32[7], (inr i32[9], inr i32[9])))`.
- `corpus/gen-raise-pass.bc`: a stored generator over a row passed on from a copy, and dropped in
  one arm. `(inl i32[106], (inr i32[2], (inl i32[7], inr i32[2])))`.
- `corpus/gen-raise-annot.bc`: an ascription of two parameters at different rows (a raising and a
  pure one; `Fail`'s and `Oops`'s). `((inl i32[1036], inr i32[2]), (inl (inl i32[1036]), (inl (inr i32[2]), inr i32[20])))`.
- `corpus/gen-raise-local-pure.bc`: a pure stored generator bound in a copy at a row.
  `(inl i32[1017], inr i32[2])`.
- `corpus/gen-raise-unused.bc`: an unused stored generator before a tail call, and a sum holding
  one dropped at scope end. `((inl i32[4], inl i32[46]), (inl i32[103], (inr i32[2], (inl i32[103], inr i32[2]))))`.
- `corpus/gen-raise-become.bc`: a close that raises, at a tail call after work (a counted `tick`):
  the work happens first. `((inl i32[113], i32[1]), (inr i32[9], i32[1]))`.
- `corpus/gen-raise-op-terminal.bc`: paths ending in a value and in an operation, the close after
  the operation. `(((inl i32[113], i32[1]), (inl (), i32[1])), ((inr i32[9], i32[1]), (inr i32[9], i32[1])))`.
  Marked `old-backend-refuses` (below).
- `corpus/gen-raise-with.bc`: a tail call taking a stateful `with`'s result: drops at scope end.
  `((inl (i32[13], i32[1]), i32[1]), (inr i32[9], i32[1]))`.
- `corpus/gen-raise-local-bind.bc`: a local bound with a written type, passed on in a 9000-deep
  recursion. `(inl i32[3], inl i32[3])`.

Arms of a `case` that give stored generators over different rows at one place, each where the
other's is pure, are refused at the surface with that reason ("the arms of this `case` give
stored generators over different rows at one place"), not as a type mismatch in generated core.

**The old backend.** Two uses of a function holding a raising stored generator across a stateful
handler's operation, at two sites, are refused by the old backend's unwind lowering ("unwind: an
operation no handler catches", `Backend/Clos/Unwind.lean`'s `catch`): its flow analysis merges the
two copies' codes and their raise names. One use alone runs; the same shape without a stored
generator runs; the source stage and Backend2 run both. Such programs are marked
`old-backend-refuses` (N7 retires the old backend).

A cleanup that raises around a source's `yield` is provided (`u <- yield(x) unwind (D)`,
`corpus/gen-raise-close-two.bc`). A `with h { g() } finally { … }` whose body loops is refused
before any of this, as a handler around a loop (§21 *Open*, L1).

### Self-reference

A generator may not hold a borrow of its own local across a `yield` (Rust's generators forbid
it, and its `async` needs `Pin` for it). A borrow block's body may perform only abortive
operations (§19: a non-abortive operation crossing a borrow is T1, the checker's rule until surface A1, #843, for §62's shapes), so a `yield` inside a borrow block is rejected (`corpus/reject/gen-self-borrow.bc`).
A generator owns its data, or iterates by index, and borrows within one step. A stored generator that holds a
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

**A local whose type is not known** (#849, #686). Inference types a local from its binding; a
local whose binding it does not type (`let y = inl 3`, a call of a name not in scope, a loop's
variable, a binder of a `match` the elaboration cannot walk) has a slot whose type is *not known*,
never a type it does not have. Inference reads such a slot as not known (`TCx.tyV`,
`Elab.inferV`, over `Elab.Slots`), and does not ask the checker's synthesis about a node that
names it, the checker having no unknown type. Every reader of a local's type takes "not known" as
such:

- **At a call**, an argument whose type is not known is one inference does not type, as an
  injection is. When its parameter's type is determined by the other arguments, the argument is
  left to the checker at that type, and after the declaration's typed elaboration, with the call
  at its instance's types, the binding's type is solved from that use by the metavariables of
  `Frontend/Elab/Meta.lean` (`fillDecl`), as an injection's is before it. When nothing determines
  the parameter, the call is refused at the argument: `the type of this argument of f is not
  determined here` (the binding is ascribed, `let y: T = …`).
- **Where the type itself is needed** (`*e`, `borrow imm *g`), the refusal names the operand:
  ``the type of `key` is not known here``.
- **A name not in scope** is reported by the checker, `unknown variable`, as without the call.

A local whose type is known is unchanged, `1` among them. Why a binding is not typed (#686's
`match` over `imm` data, a generator call lifted inside a borrow block) is not changed here:
those refusals now say that the type is not known instead of reporting a type `1`.

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
- **A finaliser frame's clauses are one code.** `ubind (λx. N, λ_. D) M`, the consume glue around an
  operation, is converted with `N` and `D` one `sel` code called on `inj₁ x` to continue and on
  `inj₂ ()` to finalise (`markUbinds`), so what both use, a generator's owned state held across a
  `yield`, is captured once and not copied (`corpus/gen-close.bc`: 4 allocations, no copy).

### Baseline

No `CDerives` rule, relation clause, machine step or kernel type is added. `fundamentalC`,
`adequacyC`, `fundamentalD` and `adequacyD` keep their statements, and every theorem of §§1–14
and §19 is preserved: every construct of this entry is elaborated into core before checking.

### Open

- **A generator that holds a capability across a `yield`.** `yield` is cancellable, so what is
  live across it must hold no owned cell (§19's `[let]`); a capability (`ref input`, `ref output`)
  is not consumable and must be handed back, and a cancel answers `()` with no residual. So a
  generator over the input, or one that writes as it yields, is rejected by the checker
  (`corpus/pending/gen-digits.bc`, `gen-lines.bc`, `gen-lazy.bc`, `gen-adapters-io.bc`). It needs
  a cancel that hands back a residual, or a `must_resume ctl` iteration effect (no `break`).
- **Callbacks that yield** to a `for`'s site: a block takes the loop's threaded variables and
  hands them back at each call (§32, `corpus/yield-callback.bc`). `|>` chains the adapters as
  functions over stored generators (§33). Adapters written as handlers over a computation would
  hold the continuation across their own `yield` (*A body that performs a control operation*,
  above), and are not provided.
- **A total consumer of a generator that loops.** A `for` over one is div: its turns are
  unbounded. A finite source written as data, or a sized iterator (§16), is total, and so is a
  generator whose body does not loop.
- A stored generator over a row bound to a local, `let g : U (pull …) = g(…)`, is at the row of
  the generator (its binding's type is rewritten, `pulledTy`) and is passed on from there
  (`Cx.pulls`); but the cancel-row rule (`FinsHeld`) reads parameters, so such a local held
  across a capturable operation of the same function is not given the cancel row it needs.
- A stored generator over a row bound from an observation (`inl (x, it) -> f(it)`), or read out
  of a sum, and passed on to a function other than the recursion's own: `Cx.pulls` follows
  parameters, their copies and pairs, not injections.
- A written stored generator's type that nothing with a row reaches keeps its written row (an
  annotation on a function's result; a type alias of `pull` at a stored generator's binding,
  which `isPullTy` does not see through).
- A `for` over a LOOPING generator inside a control handler's body: the per-observation form (L1).
- Closing a stored generator over a row whose close performs a capturable operation (not only
  abortive ones): `thenFinB` decides it, and no program has one.
- A `for` over a stored generator over a row, or over a raising generator, inside a handler's
  body: a handler around a loop is not provided (§21 *Open*). The grounding programs consume by
  recursion (`drain`, `fold`) under `to_result` and `on_exhausted`.
- Pipes L2 (#921) rewrites the adapters as stages.
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
| an owned array `array A`, `A` persistent | as `&a` | the leaf's content, copied; the array is consumed after the loop |
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

So the bound equals the number of elements: every element is visited and none is consumed. Their
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
| `&a`, `&mut a` | rejected: the lend spans the loop, and an operation that resumes cannot cross a borrow (T1, the checker's rule until surface A1, #843, for §62's shapes); iterate by index, or copy the elements out |

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

- `for` over `μ` data (lists): an owned list's rest is a cursor but its drain to the end has no
  count. A borrowed list in order is copied out first (`corpus/print-borrowed-list.bc`): an
  iterator holding the borrow across its steps is refused by T1 (the checker's rule until surface A1, #843, for §62's shapes).
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
consumed). `push` on a full buffer grows it to twice its capacity (at least
8): a new array of fillers (`tab`), each element moved by `array_replace`, and the old array
consumed with the fillers left in it. Every operation is `tab`, `array_replace`, `array_size`,
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
`split_once`, `trim`, `find_str`, `eq_lit`, checked parsing (`parse_i32` and `parse_i64`, which
raise their error, §18; an overflow is an error, not a wrap), `push_i64` (the decimal form of an
`i64`, appended; §36 *JSON*), the integers written in a view folded into a state (`fold_i32s`, `fold_i64s`: each run of
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
resource, so it is copied and consumed freely, and an array or a buffer holds literals with no
lifetime. `'c'` is a character, the `i32` scalar value.

**Literal views.** `borrow imm "…" { v -> S }` (or on a `lit` variable) lends the literal's bytes
as a `text 'x`: the elaboration tabulates them into an array (`tab`), lends it (`slice_borrow_imm`)
to a callback that first copies the family (`array_copy`), and consumes the array after. It is a
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
  program's data before the heap, at an address the target chooses (`Target/Flat/Syntax.lean`,
  `dataBase`; the Wasm target's data segment is from `16384`). Every literal is one code, so a call of one is
  direct.
- **Literal views point into the data.** The erased shape of a literal view — the array lent by
  `withbor`'s term to a callback that first copies the family, then consumed — is recognised
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
- `write_lossy`, `char_indices`, `split_at_str`, `sub_str` and `push_hex` of the design's list are
  not provided.
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

    effect E[T, …] { fn op(x₁: A₁, …) -> B; ctl op(…) -> B; must_resume ctl …; multi ctl …; … }
    handler h(mut s: S): E = { op(x₁, …) = e; … }                                   (answering)
    handler h[T, …](p: A, …): E[A, …], A -> R with E₂[…] = { return(x) = M; op(x, …, k) = N; … }
    with h[A, …](e, …) { M }          with h(&mut c) { M }
    fn f(…) -> T with E₁, E₂[A] = …                                       (a written row)

An **effect** declares its operations, each **answering** (`fn`, Koka's `fun`) or **control**
(`ctl`, with the structural qualifier of §19: cancellable by default, `must_resume ctl` for must
resume, `multi ctl` for unrestricted). An effect is one kind or the other. A control operation
whose answer is `never` (the type `0`) at a cancellable or unrestricted qualifier is **abortive**
(§19). An abortive operation is cancellable: `multi ctl op(…) -> never` is rejected, and so is an
unrestricted operation answering `0` in a row of the core text (decision 63's restriction,
2026-10-12; §27 *Typing*). An effect may take type parameters (a control effect only).

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
| `with h(e) { M }` | `borrow mut (alloc(e)) { 'l, c -> M' }`: a `withbor` of the state's cell whose callback's parameter is the capability; the cell is consumed after |
| `with h(&mut c₀) { M }` | `borrow mut c₀ { 'l, c -> M' }`, and `c₀` is rebound |
| `op(v)` in `M` | `let (c, r) = h__op(c, v)`, `h` the innermost handler of `E` (or the one named, §38) |

The capability is threaded as a `let mut` variable is: bound again after each call, handed out of
each arm of a `match` or `if` that uses it, out of a borrow block, and through a `for`'s body.

**Control effects** are §19's. Each `with` of a control handler is a **handler site** with a
static name `n` of its own, and an operation is resolved lexically to the innermost site of its
instance (§38): `perform[n.i](v)`, or `abort[n.i](v)` for an abortive operation. The site is
`handle_with[n]((V_r : T_r), (V_c : T_c)) M`: the return clause `V_r` and the tuple `V_c` of the
operation clauses, `!` closures at the types `[handle]` gives them (`T_r`, `T_c`), the handler's type
parameters matched against the body's type and its arguments' types. The body's type is read
with the body's lends elaborated (`TCx.tyCL`, §11 *Sugar*), as a borrow block's result is, and so
is the result of a block `{ … }` whose body loops. The node holds its clauses:
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
it, or to what the enclosing function's copy was given (§38). A row carries its operations' cancel
rows, inferred per operation name and never written at the surface (§27 *The surface*).

**A call's binding.** A call lifted out of the value it is in is bound before it: `r <- C`, or,
when it hands back capabilities, `t <- C; let (c₁, (…, r)) = t`, and the value refers to `r`.
When the value is the call's answer alone, the call takes its place: `x <- return V` binds `x`
as the call's binding binds `r`, and a terminal `return V` in tail position is the call itself,
when the call hands back the capabilities the computation hands back (in order) or the
computation hands back none. This holds at every call that is bound so: a function's copy, a
block parameter (§32), an answering operation, a resume (§19), a handler site, a stored
generator's site, a recursive group's self-reference and a layer's `call` (§20). A parameter that is the function's only one is its lambda's binder, not bound
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
  is ascribed its row. An unwind ends the lend, and the lender's finaliser runs. A buffer's or a
  literal's block is its scheme (§17) with the array's lend in the unwinding form
  (`slice_borrow_*_u`), ascribed the scheme's type (`corpus/buf-lend-raise.bc`,
  `lit-lend-raise.bc`). The unwinding form of a marked scheme (a lent cell's, a literal's view,
  §57) is not marked, so a literal's view crossed by an abort tabulates its table into an array
  that is not the literal's read-only bytes. A load block (`borrow imm *g { 'y, v -> … }`, §36)
  is `withloadU`, `withload` at the callback's row: the load consumes only the `imm` borrow `g`,
  so an unwind ends the reborrow and hands nothing back, there is no finaliser, and the place `g`
  borrows is left as it was. So a load's body may raise, and may call a recursion, which performs
  `Exhausted` (§20) (`corpus/effects-load-raise.bc`, `rec-load-walk.bc`, `rec-load-exhausted.bc`).
- *In a call that lends a place*: `f(…, &mut x, …)` or `f(…, &x, …)` at a borrow parameter of a
  function that performs operations of the row is the borrow of the call (§11's lend) in its
  unwinding form at those operations, which must be abortive: `withbor2U`/`withbor1U` of a cell,
  of a cell scoped to the call for a `let mut` value, or `slice_borrow_*_u` of an array. `x` is
  rebound from what the borrow hands back. A capability the call threads is passed beside it, its
  lifetime parameter read off the capability's borrow (`corpus/lend-call-raise.bc`).
- *With answering capabilities in use*: the body of a control `with` is given a reborrow of each
  capability it uses (`withbor3`), so that the capability comes back when the body is abandoned.

**Consume glue** is the checker's (§19): a binding whose head may abort, at a row that cancels
(`Row.Cancels`), puts the consumes of the slots the rest uses in a `[then]` finaliser, in §12's
reverse binding order, as at the end of a path (`corpus/sugar/finaliser-order.bc`). A value
that is not consumable (§12, group 3) live across such a binding is rejected, naming it.

**Not provided**, each rejected with a message that says so: an operation inside a closure or
block that is not run in place, other than a block passed at a parameter of function type (§30),
and a function with a row passed as a value other than at a parameter of function type, where
it is the block that calls it (§33; stored callbacks, #161 part B; for a fold's algebra that
raises, K4 below); a lend `&mut x` in the arguments of an operation, of a block's call (§30) or of
a recursive group's own call (§20); an operation of an answering effect inside a clause of an answering handler;
a function with a row whose written result is a computation (a loop); type parameters on an
answering effect; an effect with both kinds of operation; an unrestricted operation that answers
`never` (`multi ctl`, above); a move out of a variable lent for a control handler's body, and a
capability passed on in a control handler's body (§41 *A control `with` lends what its body
writes*). Several instances of one effect are §38's, with what it does not provide.

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
`default` from one source; a buffer built halfway is consumed when the abort unwinds.
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
`from_utf8`'s buffer is consumed on the error, since an error holds nothing owned; provisionally:
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
- An error that holds an owned value: §19's `[raise]` asks its argument to consume.
- A capability threaded through a `for` over `&a` of an owned array: the lend around the loop
  takes `top` as its bound, so the loop's state cannot hold a borrow (`corpus/effects-map.bc`
  passes a view instead).
- Sites other than a handler site and a looping block's result may read a computation's type
  before its lends are elaborated (`tyC` where `tyCL` is meant).

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
on its continuation `κ`, which fixes `κ`'s class and its one use. Other systems take the
qualifier from the substructural lattice (Tov and Pucella's λURAL, whose point between linear and
unrestricted they call affine; Tang et al.'s related work; *Affect*'s affine continuations, in
its own terms). The kernel has two classes, unrestricted and linear, and the qualifier picks one
of three continuation types:

| qualifier | surface | class | its one use | `κ` is |
|---|---|---|---|---|
| **must resume** (`lin`) | `must_resume ctl` | linear | resumed exactly once: a must-complete computation | `U((B ⊸ F_Σ R) & ⊤)` |
| **cancellable** (`cancel`) | `ctl` | linear | resumed once, or cancelled (the cancel a consume when it is pure, `kTy_cancel_consumable_iff`) | `U((B ⊸ F_Σ R) & F_Σ 1)` |
| **unrestricted** (`unr`) | `multi ctl` | unrestricted | resumed any number of times, or cancelled; its captures are persistent (`lam_bang_persistent`) | `!U((B ⊸ F_Σ R) & F_Σ 1)` |

**A cancel has computational content: the continuation's consume.**

- To cancel `κ` is to **unwind** it: its frames finalise innermost first, and each lend in it
  ends, as §12 derives a record's consume from its fields', frame by frame.
- `(B ⊸ F_Σ R) & F_Σ 1` is a linear type with a cancel branch, the `A & 1` encoding. The `1`
  branch, `cancel`, is the consume. The additive `&` makes the two branches share the one
  captured context.
- A must-resume `κ` has no `1` branch, so it must be resumed.

**`raise` is an operation whose handler only cancels.** There is no separate mode.

- `Fail[E]` is `raise : E ↠ 0` at a cancellable or unrestricted qualifier; a program's is
  cancellable (§18).
- Its answer type is `0`, so the resume branch can never be taken, and the handler can only
  cancel.
- An operation with answer type `0` at a cancellable or unrestricted qualifier is **abortive**, and
  the machine cancels eagerly, in place ([unwind]/[finalise], below). The clause receives only
  the argument, and `κ` is never reified.

  That is what lets an abortive operation cross a borrow's scope: the borrow's callback returns
  by its unwind path and the lend ends, with nothing kept alive across it. It is not T1.

**Which operations cross a borrow's scope:**

| operation | crosses a borrow's scope |
|---|---|
| answering | yes: it is a call |
| abortive (answer type `0`, cancellable or unrestricted qualifier) | yes: unwinding ends each lend it passes, LIFO (*Theorems*) |
| any other control operation | no: its `κ` is reified, and a stored `κ` would hold a lend across a suspension (T1, #172) |

- **An answering operation** is a call of the handler's clause on the handler's state. The
  handler's **capability** is a value: the clause, as `!` code, beside the state, threaded as a
  `Mut` borrow (§18, #184), shared as an `Imm` view, or absent (a stateless, persistent `!`
  provider). Nothing in this entry assumes that a provider of answering operations is a lexical
  handler with linear state. A call is typed by §3's rules. So
  `borrow mut buf { … log(x) … }` with the handler outside is the callback capturing the outer
  `log` capability, an outer borrow that outlives the callback's lifetime. This is acceptance (2),
  and it needs no new rule and no new proof.
- **An abortive operation** is how an error is raised. `Fail[E]` is an ordinary effect,
  `raise : E ↠ 0` (cancellable), handled by ordinary handlers: `to_result`, `default`, `retry`,
  `map_err`.
  There is no sum for failure and no special case (#168). Unwinding closes scopes innermost
  first, which is BoLo's nesting order:
  - when an unwind passes a borrow, that borrow's callback returns, by its unwind path;
  - the lend ends, and the lender regains the place;
  - the frame's finaliser (§12's consumes) runs, and the unwind continues outward.

  Nothing is kept alive across a lend: this is not T1, which needs a continuation held while a
  borrow is out. The obligation is stated under *Theorems*.
- **Any other control operation** captures the rest of the computation up to its handler as a
  continuation `κ`, which the clause may resume now, later, or several times. It may
  **not** cross a borrow's scope, since a stored `κ` would hold a lend across a suspension. That
  is T1 (#172).

  A cancellable `κ` is consumed by exactly one of its two entries. So "a continuation cannot be
  consumed" (#185, `release_not_lolli`) is answered by the consume `cancel`, not by a `forget`:
  in Core, `forget κ` has no derivation at `1` (`not_release_kappa`, *Laws* item 4).
  A must-resume `κ` has no `cancel`, for must-complete computations.

*T1 below is the checker's rule until surface A1 (#843), which emits §62's suspending constants
and lifts T1 for their shapes, for programs without host externs (the kernel's host-externs unit is
pending), under `HandlerLawN`. A callback's own borrow held across a suspension, and a borrow
handed between paused computations, stay refused after A1 (#844 Tier 2, with #821's loan-out stop
clause).*

**T1: owned across suspensions, borrowed within.** No lend
stays open across a suspension whose handler is outside the lend: a resuming operation, `await`,
`yield`, or a loop's tick (`Div` is a handled effect, §14, so each step of a loop that is not
counted resumes). Data that crosses such a suspension is owned, moved into the suspended code and
moved back out; between suspensions, borrow freely. A suspension handled *inside* the lend's scope
does not cross it: a borrow lent from outside a scheduler that runs inside the borrow (scoped tasks,
`spawn_in`/`run_in`, §32), or around a generator pulled by hand inside it, is held by the suspended
code, and the lend still closes within one run. The one exception is R1 (§29), frozen as it is: a
`mut` lend of a task's own cell, its callback at `Row.ResumeOC` under `PinLaw`. Every other borrow
callback's row is `Row.Unwind` (*Typing*), which is how the kernel enforces the rule. A refusal under it names its fix: end the borrow before suspending; move
ownership in and out; iterate by index or with a counted `for` (§16); or copy the value out. Kept
beside it: borrows across abortive operations (above), the per-observation lend over loops (§14),
BOXED-κ (§28) and capabilities as borrows. Lifting T1 is §62's design; the approaches tried
before are in `docs/tombstones/lends-across-suspensions.md` (void).

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

`ubind` is `M to x. N` with a finaliser `D`, which runs instead of `N` when `M` unwinds. In core
text, `x <- M unwind (D); N` is checked at `D`'s own row, and a row entry may spell its cancel row
(§27 *The checker*). The surface `x <- M unwind (D); N` is the same, its `D` performing the control
operations of the sites around it (§27 *The surface*).

`H = (h_ret, h_op)` is a pair of values, `n` a literal, and `qs` the tags of the operations'
qualifiers (§25), which `[handle]` writes. Evaluation is argument-first, so `e` runs under the frame
`hnd (n, (qs, H)) [·]`; below, `hnd (n, H)` abbreviates it. A context `K` is **free of `n`** (`Kont.NoHnd n K`) when
none of its frames is `hnd (n, H′) [·]`. It may hold handlers of other names. A context is
**unwind-clear** (`Kont.NoUbind K`) when none of its frames is `ubind _ [·]`. The head steps
below and the cancel steps (*Cancels*) do not allocate:

    (μ, hnd (n, H) v)                  ↦  (μ, h_ret v)                                     [ret]
    (μ, hnd (n, H) K[perform (n, v)])  ↦  (μ, h_op (v, κ))     K free of n, where          [op]
          κ = λy. hnd (n, H) K[y]          (at a must-resume or cancellable operation, §25)
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
- **Other handlers' frames are transparent to it.** They are consumed, which is sound because
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

A cancel is not interceptable. (This is the κ.2 cancel of a `cancel` operation. A cancellable wait's
cancel, §29a, is a resume with `inr ()` and an ordinary raise, re-raised at every later wait of the
cancelled scope: law 5c.) The cancelled region `K` is torn down: nothing in it resumes, and
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
- **No error is consumed because of its name.** A name whose site the region re-enters, a dead
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
- **An unrestricted continuation consumed.** When the finaliser's continuation is unrestricted and
  its handler discards it, the kept error and the region's remaining finalisers go with it
  (`progConsume`; resumed instead, the error reaches its live handler, `progKeep`). This is the case
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
  | `progConsume` | a finaliser raises `2` (kept); a later one performs `4`, whose `unr` clause consumes its continuation | `inj₁ ()`; the live `2` never runs |
  | `progKeep` | as `progConsume`, the clause resuming | `inj₂ ()`: the kept `2` reaches the live `2` |

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

    C ::= … | F_Σ A            Σ = {n₁ : E₁, …, n_k : E_k},   E = {op_i : A_i ↠^{q_i} B_i}_i,   q ∈ {lin, cancel, unr}

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

    Δ; Γ ⊢ V : A_i        n : E ∈ Σ,   op_i : A_i ↠^{q} 0 ∈ E,   q ∈ {cancel, unr}
    ──────────────────────────────────────────── [raise]
    Δ; Γ ⊢ raise_{n,i} V : F_Σ B          (any B: an abortive operation, whose answer 0 is absurd)

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_Σ A    Δ; x : A, Γ₂ ⊢ N : F_Σ B    Δ; Γ₂ ⊢ D : F 1
    ──────────────────────────────────────────────────────────── [then]   (§27: D at its own row)
    Δ; Γ ⊢ M then x. N unwind D : F_Σ B

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_Σ A    Δ; x : A, Γ₂ ⊢ N : F_Σ B
    (Σ has an unrestricted operation ⇒ !Γ₂)
    (Σ has an abortive or cancellable operation ⇒ Γ₂ holds no owned cell: NoOwn, or use [then])
    ──────────────────────────────────────────────────────────────────────── [let]
    Δ; Γ ⊢ (λx. N) M : F_Σ B

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ H : !U(A ⊸ F_Σ R) ⊗ ⊗_i !U(A_i ⊗ K_i ⊸ F_Σ R)    Δ; Γ₂ ⊢ e : F_{Σ, n : E} A
    ──────────────────────────────────────────────────────────────────────── [handle]
    Δ; Γ ⊢ hnd (n, H) e : F_Σ R          (n ∉ Σ)

    K_i = U((B_i ⊸ F_Σ R) & ⊤) (lin),   U((B_i ⊸ F_Σ R) & F_Σ 1) (cancel),   !U((B_i ⊸ F_Σ R) & F_Σ 1) (unr)
    an abortive operation's clause is !U(A_i ⊸ F_Σ R): the machine has cancelled κ
    (§27: the cancel branch is at F_{F_i ⊕ Σ} 1, F_i the operation's cancel row)

- **As built** (`Core/Fundamental.lean`, `CDerives.eff*`; `Core/EffRules.lean`):
  - a row is a list of operations `(n, i, q, A_i, B_i)`, and `F_Σ R` is `CTy.effOf Σ R`;
  - `[sub]` is `RowLe` (every operation of `Σ` is `Σ′`'s);
  - `[raise]`'s argument type holds no owned cell (`VTy.OwnFree`): the raise abandons it, which
    is not a consume;
  - `[then]` asks `Σ`'s names to be nonzero and its keys unique, and `!Γ₂` at an unrestricted
    row;
  - `[handle]` takes `H` a value form over a part of the context whose live slots are
    persistent, the clause of the `j`-th operation at index `j` (`Row.ofEff`, `clausesTy`), and
    `n ≠ 0` (`CDerives.effHandleV`, §24); `h_ret` and the clauses as two variables is its
    instance (`CDerives.effHandle`).
  - at a handled row that holds `Div` (§14), `[handle]` is `effHandleT`, whose clauses resume `κ`
    in tail position; `effHandleV` and `effHandleVB` ask the handled row not to hold `Div`, and
    `[then]` asks it of the finaliser's row (decisions 68 and 69).
- **The must-resume `κ`** is the same `&` pair as the others, its cancel branch at `⊤`, so the
  clause can only resume it. The machine builds `κ` by the operation's qualifier (§25): at `lin`
  and `cancel` it owns a cell, and a must-resume `κ`'s cancel branch has no step.
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
  - **Abortive operations are cancellable** (§18). The kernel's `[raise]` admits an unrestricted
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
  additively, and disposes it (§12's consumes).
- **A finaliser's effects** (§27, decisions D2 and D3 of 2026-10-08): `D` is at its own row
  `Σ_D ≤ Σ`, and each operation of `M` whose continuation may be cancelled records `D`'s effects in
  its cancel row. The machine sends a finaliser's raises and operations to the nearest live handler
  (*Cancels*), and `[sub]` at the cancel's use asks them to have a live instance there. A plain
  `[let]` at a row with an abortive or cancellable operation (`Row.Cancels`) needs `Γ₂` to hold
  no owned cell (`Ctx.OwnFree`: borrows, `!`, data), since a cancel or an unwind abandons it.
- **Consume glue** is a surface obligation: the elaborator inserts a `[then]` finaliser for every
  owned local in scope at a possible abort, as Rust inserts drop glue. So the side
  condition "the abandoned context holds no owned cell" is met automatically. The kernel
  checks it; the elaborator establishes it.
- **Borrows.** Each borrow constant (`withbor` 1–3, `withload`, the slice borrows) keeps its
  pure form, and gains an **unwinding form** at a callback `F_Σ(['x] B)` whose row has only
  abortive operations. The unwinding form's term is the pure one's with `ubind`: when the callback
  unwinds, the lend ends, the source goes back to the lender, and the lender's finaliser runs:
  - `forget` for a `Mut`/`Imm` source;
  - the consume for an owned `Ref A`, at `Consumable A` (§12).

  Then the unwind continues outward. Non-abortive control operations stay inside a borrow's scope: every
  borrow callback's row is unwind-only.

  **As built** (`Core/EffBorrow.lean`, `CDerives.withbor1U` … `sliceBorrowIU`):
  - the unwinding constant is `U(src ⊸ U(∀'x ⊏ ⊓Δ. L ⊸ F_Σ(['x] B)) ⊸ F_Σ R)`, with the pure
    form's source `src`, lend `L` and result `R`;
  - its term is `withborU d = λr. λf. (f [] r) then b. (r, b) unwind d r`, with a closed finaliser
    `d : src ⊸ F 1` typed by a premise. The elaborator passes the source's consume `consumeE src`
    (§12), which is `forget` at `Mut`/`Imm`;
  - `withload`'s source is consumed by its load, so nothing goes back to the lender: its unwinding
    form is `withload`'s own term at the effectful type (`withloadU`), with no finaliser. The
    elaborator gives a load block whose body performs abortive operations this form (§18, §36);
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

  for `n : E ∈ Σ` at `lin` and `unr`; at `cancel` and `unr` the continuation's share also owes the
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
(*Cancels*). So an operation that raises must have an argument that consumes with nothing owned (a
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
    operation types over `F A`, `A` polynomial in `X`; it may sit under arguments and `∀` leaves
    (§22), and its operation types are then read at the leaf's lifetime substitution;
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
       released.
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
     storing it needed. A continuation stored while it captures borrows is what T1 rules out
     (T1, §19: the checker's rule until surface A1, #843, for §62's shapes). Non-abortive control operations cannot cross a borrow, so no stored `κ`
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
     - At a must-resume or cancellable operation the next two steps allocate `κ`'s cell at a
       location `ℓ` the memory does not hold, any such, and hand the clause `kappaC` at `ℓ`,
       cancellable exactly at a cancellable operation (`catch_cell`). Every run from the catch is a
       prefix of these three steps or goes on from them (`catchEv_cell`).
     - Resuming `kappaC` at `ℓ`, at a memory holding `()` at `ℓ`, frees `ℓ` and runs
       `hnd (n, H) K[w]` (`kappaC_resume`): three steps reach the `free`, and after it `κ`
       resumes as `kappa` does (`kappaC_resume_parts`, `kappa_resume_kResume`). A cancellable `κ`'s
       cancel frees `ℓ` and runs `κ`'s cancel run (`kappaC_cancel`). A must-resume `κ`'s cancel
       branch has no step (`kappaC_cancel_lin`).
     - On a run to a value, a use of `κ` at its cell frees the cell three steps later: `κ` is
       applied to `inj₁ ()`, or to `inj₂ ()` at a cancellable operation, and the memory holds `ℓ`
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
     exactly as `raise p` steps there: the frame that catches it consumes them (`abort_absorbs`;
     `abort_to`, `abort_app`).
   - *Sequencing*, `op(v) to x. P = op(v; y. (k y to x. P))`, is not yet a Core theorem.
3. **Static per-site names: no accidental handling.** An operation is caught by the nearest live
   handler of its name (*Names*); a handler of another name passes it, in the machine as item 1's
   H-fwd (`fwd_abort`). `tunnel` (E6, `Core/EffTier1Programs.lean`): `fwrap` handles `exnᵢ` around
   a callback that raises `exnₒ`, and the raise passes `fwrap`'s handler to `toResult`'s outside
   (`d_tunnel`, `tunnel_run`; the kernel program `tunnel`).
4. **Continuations are must-resume or cancellable; `unr` is tolerated.** A clause's `κ` is at `kTy`
   (*Kinds of operation*): at a must-resume or cancellable operation a thunk of an `&`, which is not
   persistent, its cancel branch at `⊤` at a must-resume one. So a typed clause uses `κ` as its
   qualifier allows, by inversion of `CDerives` (`Core/Inversions.lean`):
   - At every resuming must-resume or cancellable operation, every context and every cancel row, a
     clause that consumes `κ` (R1), resumes it twice (R2), or cancels and then resumes it (R4) has no
     derivation at its clause type; at every must-resume one, neither has a clause that cancels it
     (R3) (`refuses_R_clauses`). The refusals are of `κ`'s use, not of the clauses' form: at the
     clause type of a must-resume `1 ↠ 1` a clause that resumes `κ` once is typed, and a clause that
     cancels `κ` is typed at a cancellable operation and refused at a must-resume one
     (`clauseRefusals_pinned`).
   - `forget κ` has no derivation at `1` (`not_release_kappa`), and a handler whose clause stores
     `κ` in a cell and reads it out twice has none at all (`not_der_at08`). Moving `κ` through a
     cell and resuming it once is typed (`d_at08Once`).

   An unrestricted `κ` is `!`, and a clause may use it any number of times. That every run of a
   typed program uses each must-resume or cancellable `κ` it catches once (S6) is §25 *Open*.
5. **A cancel is not interceptable, and the cancelled region's frames are dead** (for κ.2
   cancels; a cancellable wait's cancel is a resume, law 5c of §29a). `κ`'s cancel
   branch runs the region with its handler frames and cancel delimiters removed (`Kont.dead`), so
   a dead frame catches nothing (`hasHnd_dead`, `catches_dead`, `noCC_dead`). Read prefix-closed
   (`cancel_prefix`, `Core/EffCancelRuns.lean`): take a run of a term a tied derivation types,
   from the empty memory, that cancels `kappa H K`, or `kappaC` at its cell, and reaches
   the start of the cancel run (after the cell's free). Every path from there is a prefix of the
   cancel trace of `K†` (`CancelTr`):
   - `K`'s finalisers fire innermost first, each by `[finalise-cancel]` and then `D ()` running
     alone under `cfin`, to `[cfin-ret]` or `[cfin-raise]`;
   - a running finaliser's `cfin` frame is passed by `[cfin-cancel]`, its error first;
   - the first kept error wins, and the canceller gets `()` or the kept error re-raised, an error of
     a name of the effect context (`CancelsNamed`). At a cancellable wait (§29a) the cancel is a
     raise of the cancel target, and law 6's *Unwinding* governs it: a finaliser's raise supersedes.

   The hypothesis is that each of `K`'s finalisers is a closed computation at a row of abortive
   operations of the context's names (`FinRow`). Typing then gives that it runs alone from every
   memory with finitely many cells (`finAlone_of_finRow`; at the empty row, to `()`,
   `finOK_of_finRow`). A finaliser that performs an operation a handler outside it answers (§27) is
   not covered (§27 *Open*). `progOutT` meets the hypotheses: a tied derivation types it, its run
   cancels `κ`, and its region's finaliser raises `2` (`progOutT_cancel_prefix`). So does
   `progOutTA`, the same program at a cancellable raise of `2` (`progOutTA_cancel_prefix`), typed by
   a tied derivation at an effect context with no unrestricted abortive operation
   (`EffCtx.NoUnrExn`, §18; `noUnrExn_Ξ₁₂A`): the shape the checker gives every program it accepts
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
     (`LiveOK.not_stuck`), `() ()` among them (`stuckAt_unit_app`): the cancel branch of a
     must-resume `κ` (`kappaC_cancel_lin`) is never reached.
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

1. **`Log` + `Fail`**, both ordinary effects: `log` answering, `raise` abortive (cancellable, answer
   `0`).
   - A function that logs and may raise.
   - The `Log` handler inside and outside the `Fail` handler (`to_result`). The logs are kept
     when `Log` is outside. They are lost when `Fail` is outside: the unwind ends `Log`'s
     `with`, whose finaliser consumes its state.
   - Once more with `log` a native (cancellable) control operation, to exercise rows and forwarding.
2. **`borrow mut buf { … log(x) … }`** with the `Log` handler outside.
3. **`borrow mut buf { … raise(e) … }`** with the `Fail` handler outside. Unwinding ends the lend
   (the unwinding `withbor`'s `ubind`), the buffer goes back to its owner (the owner's finaliser,
   or its enclosing borrow, which continues), and the handler receives `e`. Memory ends empty.
4. **`loop { log("tick") }`**, a `Loop` with the `Log` state in its state.
5. **Early exit.** `take(n)` stops a producer that holds a resource (an owned cell). The producer
   yields by a cancellable control operation; after `n` elements, the consumer's handler cancels the
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

   `nLogOutside` and `nFailOutside` do the same with `log` a native cancellable operation and
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
- `at06`: a clause that frees a cell the handled body also frees; a clause is at a `!` type,
  so it captures only persistent values (`not_der_at06`);
- `at08`: a clause that stores `κ` in a cell and reads it out twice (`not_der_at08`). `at08Once`,
  the same clause with the copy used once, is typed (`d_at08Once`), and every run of it ends at `()`
  with the memory empty (`at08Once_runs`); it is the kernel program `at08-once`;
- `at13`: a clause that discards `κ` (`not_der_at13`).

**The effect properties** (`Core/EffTier1Programs.lean`). Each program is a closed term with a
derivation tied to its effect context `ΞE` (`CDerivesAt`, read in `CDerives`), which has no
unrestricted abortive operation (`noUnrExn_ΞE`), and a run computed by `runM` from the empty memory
to its answer at the empty memory (`runM_val`):
- E1, a function at several rows: `hofTwoRows`, `hof = λg. g ()` let-bound once (§24's
  `[let-poly]`) and called with a pure callback, with one that raises `exn` under `toResult`, and
  with one that performs the cancellable `wait` under a handler that resumes `κ` at its cell. The
  callbacks `λ_. M` are §26's `[λ-dead]`. It answers `(tt, (inr (), tt))` (`d_hofTwoRows`,
  `hofTwoRows_run`).
- E2d: `sumGen`, a consumer of a generator let-bound once and used with generators at `yield ⊙ ∅`
  and at `yield ⊙ exn`; the raise of `exn` passes its reinstalled handler. It answers
  `(tt, inr ())`.
- E4, a deep handler: `deepGen`, whose handler of `yield`, reinstalled at the resume, catches both
  yields, its clause performing the must-resume `tick` at each; a handler of `tick` counts them. It
  answers `((), 2)`. Under a handler of `tick` that resumes, `deepGenPlain` answers `()`
  (`d_deepGenPlain`, `deepGenPlain_run`).
- E5, nested handlers in both orders: `withLog`, a state-passing handler of the must-resume `log`,
  and `toResult`. With `withLog` outside, the log is kept beside the error (`nestedLogOutside`,
  `(inr (), tt)`); inside, the raise unwinds `withLog`'s handler and its state
  (`nestedFailOutside`, `inr ()`).
- E6, no accidental handling: `tunnel` (*Laws* item 3).
- E7, abandoning a suspension: `timeout` cancels a body whose region holds finalisers: one that
  returns (`e7a`), one that raises `exnₒ`, handled outside (`e7b`), and two that raise, the first
  error kept and re-raised at the canceller (`e7d`). Each answers `inr ()`. E7c is rejected
  (*Laws* item 6).
- E8b, the finally law: `e8b` unwinds `exn_a` through a finaliser that raises `exn_b`, which
  supersedes it. It answers `inl (inr ())`.
- E9, a stored continuation: a clause answers a closure holding the cancellable `κ`, called after
  the handler has returned. It resumes `κ` (`storedKResume`, `ff`), cancels it (`storedKCancel`,
  `tt`), or cancels it and its region's finaliser raises `exnₒ`, caught outside (`storedKFin`,
  `inr ()`).
- E10: `timeoutProg`, `timeout` let-bound once, which cancels a body that waits and passes a body's
  raise. It answers `(ff, inr ())`.

E5's state function and E9's closure hold a `bool` across a `[let]` at a row with `exn`, so they are
typed where `exn` is cancellable (§27 *Typing*). The kernel programs `hof-two-rows`, `sum-gen`,
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
`k.resume y` and use `κ` nowhere else. A clause with an arm that raises out of it, cancels or consumes
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

**Cancel** is the state's consume. The resume code takes `inr ()` and switches on the state:
the callee's `k` is cancelled first (innermost), then the point's finalisers run innermost first,
and every other variable is consumed; borrows' unwinding forms are finaliser frames, so their
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
is captured once, not copied (the consume glue around an operation that holds an owned list or
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
- A non-abortive control operation crossing a borrow's scope (T1, #172). T1 is the checker's rule until surface A1 (#843), for §62's shapes (*Which operations
  cross a borrow's scope*, and this section's head).
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

    R = &ⱼ ∀'a⃗ < b⃗. (E ⊗ Pⱼ ⊸ F_Σ (E ⊗ Tⱼ))          (one member: its function type)
    gen : !U ((1 ⊕ !U(1 ⊸ R)) ⊗ 1 ⊸ R)               (`g__step__…`)

`'a⃗ < b⃗` are the group's own lifetime parameters (§31, *Generic recursive groups*), quantified in
each member's field of the record, so that each call of a member instantiates them afresh; a group
without lifetime parameters has no `∀` there.  `[spec §31]`

- **The generator** answers the record of the members' bodies, each taking `E` first and handing it
  back first, as a copy does. It is `!` code that holds nothing; when `E` has capabilities it is
  `!(∀'l₁ … 'lₙ. !U(…))` over their lifetimes.
- **A call of member `j` inside it** is a direct call of the self-reference:

      case self { inj₁ _ ⇒ abort[e.0] () | inj₂ g ⇒ (force (unbang g) ()).j [ℓ⃗] (E, W) }

  with `E` bound again after, `e` the site of the exhaustion effect, and `[ℓ⃗]` the member's lifetime
  parameters instantiated at the call's lifetimes (§31). It is a call's binding (§18,
  *A call's binding*), so a terminal that is its answer is the call itself, in tail position; a
  layer's `call` likewise.
- **A member's copy** is `(bounded_fix[1, R] (gen, (budget, ()))).j [ℓ⃗]`, at the budget `recBudget`,
  `ℓ⃗` the copy's own lifetime parameters. It
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
  out inside a loop's observation, where `Exhausted` has no handler: the surface provides no
  handler around a div computation, for any effect (`with to_result { f(x) }`, `f` looping and
  raising, is rejected the same way). Rejected with that reason (`corpus/reject/rec-loop.bc`). The
  kernel handles a div computation per observation: one observation `(nu_out l).1`, at a
  `Div`-free row, is handled by `effHandleV` inside `unfold`, and the continuation is stored as the
  rest of the codata for the next observation (`corpus/core-yield-pull.bc`; the surface's
  generators use it, `corpus/gen-div.bc`). Looping tasks under `spawn` by this route are #917.
- A native handler parameter (§19 *Open*).
- **`memo`**, a layer, needs a map (#211) and a layer of its own state: an answering effect with
  type parameters (§18 *Open*).
- A layer over a recursion under `deep`; the heap driver's members with different result types.
- Effects under `deep` (§20 *Open*; separate, per the spike). Generic recursion is §31.
- Recursion through a site (decision 57's parser, `corpus/reject/rec-through-site.bc`): a level's
  own handler is a site per level, which static names cannot give (generative names, L2, #173).
  Recursion through values: a member passed as a value is a function with a row (#161).

---

## 22. Entry 21 — the closure `Clo`: observations with arguments and a boxed rest

### Motivation

§2 wrote a closure called any number of times (cf. Rust's `FnMut`) as `(env, !code)` behind a `Mut`
borrow, the code taking the environment `E` and handing it back. That form names `E`, so a function
over such closures is written once per environment type (#233; `docs/effect-polymorphism.md` R2a).
The experiment of #236 (`docs/fnmut.md`) found that two relaxations of §7's positivity make such a
closure a codata type, its environment hidden by `ν`:

    Clo^c A B  ≜  νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1

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

### Observations that take borrowed arguments: `∀` leaves (#808)

An observation tree may also be `∀'x ⊏ @b. D` over an observation tree `D` (`CTy.NuLeaf`). With
it an observation takes a borrow lent for one call: `∀'x ⊏ ⊤. Mut 'x A ⊸ F(B ⊗ [@c] U X)` and
`∀'x ⊏ ⊤. Imm 'x A ⊸ …`, and in general any argument type that mentions the bound lifetimes.

- **Why it was missing.** `A ⊸ D` needs `X ∉ A` (`A.Cl 0`), which says nothing about lifetimes:
  `Mut 'x A ⊸ D` with `'x` free was already an observation tree. The gap was that `NuLeaf` had no
  `∀` case, so a lifetime could not be quantified at the observation, and every call shared one
  lend. `X ∉ A` stays: it keeps `X` out of a negative position (`cB_mono`'s `⊸` case passes the
  argument through unchanged, and an argument that read the candidate would need it antitone).
- **Positivity.** `NuOk C` is `NuShape C` and binder freshness: no `'x` bound by a `∀` leaf is free
  in `C` (`CTy.LeafBinds`). `unfold` asks the same of its state type (`CTy.BindsFresh`). The
  checker decides both (`CTy.nuOkB`, `CTy.bindsFreshB`); a written type is fresh by construction,
  since a binder is named `Δ.freshVar`, past every variable the body's free lifetimes name.
- **Relation.** `cB` at `∀'x ⊏ @c. D` is `cC`'s `∀` clause:
  `∀α, ⌜δ ⊨ α ⊏ c⌝ ─⋆ cB η D (δ[x ↦ α]) (e ())`. The candidate for `U X` is read at no lifetime
  substitution (`nuP`), so the rest an observation answers does not depend on `α`. One
  unfolding at the relation is the unrolling with the candidate at `δ` and the tree at an
  agreeing `δ'` (`cB_unroll`, `vCE_nuEnv_at`); under a `∀'x` leaf `δ[x ↦ α]` still agrees on
  `νX. C` because `'x` is not free in `C`. Monotonicity (`cB_mono`) gains the `∀` case. Up to
  `TyEq` (`cB_tyEq`) the two sides may extend by different binder names; one unfolding never
  reads the type the environment gives `X`, only its candidate (`vCE_poly_ty`, `cB_poly_ty`), so
  it is compared at the type `1` on both sides (`nuEnvU`).
- **Coiteration.** The node at `∀'x ⊏ @b. D` is the node at `⊸` with the argument `()` (`Λ` is
  `λ_`; `nodeV_all_steps`). In `node_ok` the candidate at `δ` is the candidate at `δ[x ↦ α]`
  because `'x` is not free in the state type (`candN_congr`).
- **The rest leaves a lend only boxed.** `U` has no outlives rule, so a rest that is to outlive the
  lend its call is made in is `[@c] U X`, as in `Clo`. A lend's callback answers `['y] B` with `'y`
  not in `B` (`withbor`); `B = I32 ⊗ [@c] U(νX. C)` qualifies when `'c` is outside the lend. The
  rest's type cannot mention the call's `'x` (it is `νX. C`, formed outside the binder), and the
  lend's existing compatibility lemma returns the lent cell.
- **Surface.** `forall 'x < @b. C` in a `nu` body, `Fun 'x < @b. M` for the observation, `M['a]` to
  instantiate it; a call with `&mut buf` is `borrow mut buf { 'w, m -> f(…, m) }` over a function
  that instantiates the observation at its own lifetime parameter. No judgment, rule or
  elaboration is added.
- **Kernel derivations** (`Core/NuBorrow.lean`): `File^c`'s body is positive (`fileBody_nuOk`);
  a `read` called on a lent `Mut 'y I32` and a `write` on a lent `Imm 'y I32` derive in `CDerives`
  at `F(I32 ⊗ [@c] File^c)` (`d_fileRead`, `d_fileWrite`), covered by `fundamentalC`
  (`fileRead_sem`, `fileWrite_sem`); `∀E` at the lend's lifetime leaves the rest's type
  `File^c` (`fileRead_inst`, `fileWrite_inst`).
- **A closed program** (`Core/NuBorrowPrograms.lean`): `File^⊤` made by `unfold` over a state
  `Ref I32`, its `read` called inside a `withbor` of a buffer lent `mut` (`withbor2`), the rest
  leaving the lend as `[⊤] U File^⊤`, its `write` inside a second lend `imm` (`withbor1`), then
  `close` and the buffer freed. This is one closed `CDerives` derivation (`d_fileReadProg`), run by
  `adequacyC` from the empty memory to `()` and the empty memory (`fileReadProg_runs`). Its variant
  `d_fileReadOut` answers what each step returned, `(1, (12, (5, 5)))`, with no cell left
  (`fileReadOut_eval`). The methods use their borrows. `read` exchanges the buffer's and the
  state's contents through the `Mut 'x I32` (`withswap`): the buffer, 7, takes the state's 5, and
  the state takes 7. `write` loads the buffer's 5 through the `Imm 'x I32` (`withload`), stores it
  into the state, and answers the state's old 7 plus 5. `close` answers the state, 5, and the
  owner frees the buffer at 5. Each value is read back after its lend ends.
  `fileTwice` and `fileConsumed` are not derived in the kernel. They run as corpus programs
  (below).
- **Programs** (each at its golden from `bcc interp`, through every stage and backend):
  `corpus/nu-file-read.bc` (lend `mut` to `read`, the buffer back, lend `imm` to `write`, `close`,
  free: `i32[121215]`), `corpus/nu-file-twice.bc` (two reads inside one lend, the first through a
  reborrow, one after: `i32[72123]`) and `corpus/nu-file-consumed.bc` (the object closed by its
  implicit consume: `i32[71]`). Each calls the observations through functions of their own
  lifetime parameters (`file_read<'a, 'c>`), so `File<'c>` is elaborated in several lifetime
  contexts, with other binder names in each; the checker relates them by `[α]` (§3, *Lifetime
  binders and `[α]`*). `corpus/nu-file-contexts.bc` writes the type in two contexts whose numbering
  differs and passes the object between them, and `corpus/alpha-all-u.bc` uses one type written
  as `all 'x < b. A` in one function and as `U (forall 'x < b. F A)` in another.
- **Baseline.** `fundamentalC`, `adequacyC`, `adequacyD`, `resourceSafety`, `fundamentalC_pin` and
  `adequacyC_pin` keep their statements. Changed statements: `CTy.NuLeaf` (the `∀` case),
  `CTy.instT` (passes under `∀`), `CTy.NuOk` (`NuShape` and freshness), `cB` (the `∀` clause),
  `cC`'s `ν` guard (`NuShape`), `CDerives.unfoldN` and its copies (the premise `BindsFresh`), and
  at the `ν` level `cB_unroll`/`effRetE_unroll` (the candidate's `δ` apart from the tree's),
  `cB_tyEq` (an environment related at every pair of substitutions), `node_ok`/`candN_post`/
  `unfold_compatX` (freshness of the state type), `sSB` (the `∀` clause).

### The closure

`Clo^c A B` above has two observations: `call` takes an `A` and answers a `B` with the rest of the
closure, and `close` ends it (`Core/Clo.lean`). A closure is a value of `U(Clo^c A B)`; one that
outlives `@c` is `[@c] U(Clo^c A B)`, the form in which it is stored, lent `mut` and returned,
and the rest every call hands back is of that form.

- **Positivity** at every closed `A` (`cloBody_nuOk`), and at an argument that is itself a
  borrowed closure (`cloBody_nuOk_higher`). An effectful closure,
  `νX. (A ⊸ F_Σ(B ⊗ [@c] U X)) & F_Σ 1`, is positive at closed operation types
  (`cloEffBody_nuOk`).
- **Relation.** `cC_clo_iff`: a computation is a closure of `Clo^c A B` when every `call` answers a
  `B` and a rest that is again a closure outliving `@c`, and `close` runs to `()`; coinduction is
  `clo_coind`.
- **Observable view.** Unchanged: the observable view relaxes `U` to `True` (`vC_obs_clo`), and
  `Imm̲` takes the closure to `Unk` (`immReborrow_clo`, `immReborrow_cloBox`), the paper's clause
  (4). A closure behind an `Imm` borrow is only released; behind a `Mut` borrow it is held at the
  program's view and called by `withswap`. §12.69's `obs_transfer` takes its `U C` arm
  (`obs_transfer_cloBox`).
- **Consume.** §12's `Consumable.nu`, group 2: consuming a closure runs its `close`
  (`consumable_clo`). It is not `Releasable` (`not_releasable_clo`) and not persistent
  (`not_persistent_clo`).

**Derived rules** (`Core/CloRules.lean`), each a `CDerives` derivation, so `fundamentalC` and
`adequacyC` cover them:

| rule | term | from |
|---|---|---|
| introduction | `mkE` over a state `s : S` and `!` code `step : S ⊸ (A ⊸ F(B ⊗ [@c] S)) & F 1` (`d_mk`) | `unfold`, `nuIn`, `&` |
| introduction outliving `@c`, when `S` does | the same (`d_mkBox`) | and `[]I` |
| call | `f π₁ a : F(B ⊗ [@c] U(Clo^c A B))` (`d_callClo`) | `nuOut`, `π₁` |
| close | `f π₂ : F 1` (`d_close`, `d_closeBox`) | `nuOut`, `π₂` |
| call through `Mut @a ([@c] U(Clo^c A B))` | `withswap` with the call as callback (`d_callMut`) | `withswap`, `[]E` |
| unrestricted to `Clo` | `mkE` at the state `!U(A ⊸ F B)` (`d_ofFn`) | the above |
| `Clo` to `A ⊸ F B` | `λa. call, then close the rest` (`d_once`) | the above |

A linear function is not consumable (`not_consumable_lolli`), so it is not the state of a closure
whose `close` must dispose of it, and there is no uniform coercion from `A ⊸ F B` to `Clo`.

**Three kinds of function**, three types (cf. Rust's `FnOnce`, `FnMut`, `Fn`):

| kind | type | copy | consume | §12 group |
|---|---|---|---|---|
| linear and not consumable | `U(A ⊸ F B)` | no | only by calling it | 3 |
| linear and consumable | `[@c] U(Clo^c A B)` | no | `close` | 2 |
| unrestricted | `!U(A ⊸ F B)` | yes | `forget` | 1 |

**Bounds.** A closure outlives `@c` when its state does (`d_mkBox`); a closure capturing
`Mut 'x T` is bounded by a lifetime below `'x`, never `'x` (`logState_not_outlives`), and no
closure outlives anything except through its box (`clo_not_outlives`). The box rule of outlives
is non-strict (§23), so a closure bounded by `'x` is lent `mut` inside `'x`'s own scope.

**Programs** (`Core/CloPrograms.lean`), each one closed `CDerives` derivation run by adequacy at
every host and by the interpreter: a counter called twice through `Mut` (`counterProg`, 4),
passed through `n` functions with a reborrow (`d_passF` at every `n`; `passProg 3`, 13), nested
(`nestProg`, 8), returned (`retProg`, 15), a logger capturing a borrow (`logProg`, 12), the two
coercions (`ofFnProg`, 23; `onceProg`, 5), and a closure consumed implicitly (`consumeProg`, 0).

### The checker

`CTy.nuLeafB` admits `A ⊸ D` at a closed `A`, and `VTy.polyB` admits `[@a] B`
(`Frontend/Check/Decide.lean`, sound by `nuLeafB_sound`, `polyB_sound`); `nu_in` finds the `ν`
type through an argument. A `type` declaration may take type and lifetime parameters,
`type N[T, …]<'a, …> = A`, and a use `N[A, …]<'b, …>` elaborates the arguments at the use and the
body in the declaration's scope with the parameters bound to them (`Frontend/Check/Elab.lean`):
substitution, with no kernel change (`docs/type-declarations-design.md` §4.1–4.2, `type` with
parameters). A template's type parameters under a `μ` or `ν` binder are shifted past it, so a
call matches a parameter of type `Clo[A, B]<'c>`.

### The library

`lib/clo.bc` (`include clo`) declares the closure and its operations:

    type Clo[A, B]<'c> = U (nu X. (A -o F (B * box 'c U X)) & F 1)

`clo_new` (a state and its step; the caller boxes it, `boxed['c] clo_new(s, step)`, at the
state's type), `clo_new_boxed` (the same, boxed by the function itself under the bound `S: 'c`,
§23), `clo_call`, `clo_call_mut` (through `mut 'a (box 'c Clo[A, B]<'c>)`),
`clo_close`, `clo_of_fn` (an unrestricted function as a `Clo`) and `clo_once` (a `Clo` as a
function called once). The name `Clo`
is provisional (decision 60).

### Lowering

Nothing new: `unfold` is a closed λ-term, and its node at an argument is one more λ. A closure
built under `boxed` keeps its unfolded code `!`, so its thunk's arms bind the code to a name
first (`g <- return (unbang f); …`); `Backend/Clos/Collapse.lean` builds such a thunk eagerly as
it does the unbound form, so a closure has one code and its calls through `mut` are direct calls
(`corpus/counts.expected`, `clo-counter`, `clo-depth`: no indirect call).

### Programs

| program | what it shows |
|---|---|
| `corpus/clo-counter.bc` | a closure owning a cell, stored in a cell, called twice through `mut`; the state persists |
| `corpus/clo-depth.bc` | the borrowed closure passed through three functions, with a reborrow |
| `corpus/clo-higher.bc` | a closure capturing a closure, and a closure taking a closure |
| `corpus/clo-capture.bc` | a closure capturing `mut 'x i32`, returned from its maker, bounded by `'w ⊏ 'x` |
| `corpus/clo-consume.bc` | closures closed and freed by their derived consumes |
| `corpus/clo-coerce.bc` | an unrestricted function as a `Clo`, and a `Clo` as a function called once |
| `corpus/reject/clo-outlives.bc` | refused: a closure bounded by the lifetime of the borrow it captures |
| `corpus/reject/clo-copy.bc` | refused: a closure used twice |
| `corpus/reject/clo-linear-state.bc` | refused: a linear function as the state a `close` consumes |

### Instances

`Clo^c A B` is the only abbreviation that uses the new shapes. §7's `Loop`, `D`, `Stream` and
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
- **Surface closure sugar**: a closure over a context elaborated to `clo_new` with the captures as
  the state and their consumes as `close`.
- **Strict outlives**: §23 relaxes the box rule and `withbor`'s side condition, gives `main` a
  lifetime of its own, and bounds a template's lifetime by its type parameters.
- **Polyvariant flow.** Closures built at two sites that reach one call are dispatched there
  (`clo-higher`).
- **A linear function as a `Clo`** is refused by inspection of the derived rules, with
  `not_consumable_lolli` its mechanical part; a parametricity statement is not made.
- A generic function's lifetime parameters are unrelated to the lifetimes in its type arguments
  unless a bound relates them (§23, `where S: 'c`); `clo_new` returns the closure unboxed, and
  `clo_new_boxed` is the bounded constructor.

---

## 23. Entry 22 — non-strict outlives: the box rule and `withbor`'s side condition; lifetime bounds and `main`'s lifetime

### Motivation

BoLo prints `⊏` in every outlives premise ([TR] p. 2, rows 2.35–2.37). Two of those premises
cost programs a scope each and protect nothing the model needs (`docs/outlives-strictness.md`,
#241): the box rule of `Δ ⊢ T ⊐ @a`, and the side condition of `withbor` (Ref → Mut). Relaxing
them to `⊑` is an **extension** of the calculus, read against the model the paper defines, as
§4 (Entry 3) is; it is not a correction of the paper, and `Paper/` is unchanged. Two
elaborations, with no judgment change, remove the rest of the cost in the `clo-*` programs: a
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
(`corpus/reject/clo-outlives.bc`).

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
which `allE` asks of it (`corpus/reject/clo-bound.bc`). The bounds are kept with the template
(`Mark.template`) and printed with it, `fn def f[S, …] where S: 'c : A = V`. `where` is a word
in that position, not a keyword.

`lib/clo.bc` declares `clo_new_boxed[S, A, B]<'c>(s: S, step) -> box 'c Clo[A, B]<'c> where
S: 'c`, which boxes the closure and every rest itself, and `clo_of_fn` is built on it.

### Programs

| program | what it shows |
|---|---|
| `corpus/clo-counter.bc`, `clo-depth.bc` | the closure stored and lent `mut` in `main`'s body, under `main`'s lifetime; built with `clo_new_boxed`, with no `boxed` |
| `corpus/clo-consume.bc`, `clo-higher.bc` | a closure over a closure, bounded by the same lifetime as the closure it holds |
| `corpus/clo-coerce.bc` | the coercions at `main`'s lifetime |
| `corpus/clo-capture.bc` | `logger`'s `'w < 'x`, filled with `dom`, gives `clo_new_boxed`'s bound; its scope `'w` stays (the `Mut` rule) |
| `corpus/main-lifetime.bc` | `'main` by name, and cells of `1` that allocate nothing |
| `corpus/borrow-in-scope.bc` | a cell holding `imm 'x i32` lent `mut` inside `'x`'s own scope (the side condition) |
| `corpus/reject/clo-outlives.bc` | still refused: a closure bounded by the lifetime of the borrow it captures |
| `corpus/reject/clo-bound.bc` | refused: a lifetime bound's instance called at a lifetime not below the type argument's |
| `corpus/reject/generic-lifetime-unknown.bc` | refused: a lifetime left undetermined where no lifetime is in scope, outside `main` |

Across the six `clo-*` programs, the scopes opened only to name a lifetime go from 10 to 1, the
cells written for them from 6 to 1 (`clo-capture`'s, a unit cell), and the `boxed[…]` annotations
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
  `clo_new` and `boxed['c]` (`clo-consume`'s `nest`, `clo-higher`'s `doubler`).
- **A lifetime without a cell.** `main`'s lifetime, and `clo-capture`'s scope below `'x`, are
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
and no borrow lemma changes. The checker (`Frontend/Check/`) types a finaliser at `F 1`: the consume
glue (§12's consumes) already was. The checker does not emit `[let-poly]`: it checks a `def` at
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

## 25. Entry 24 — the capture cell: a must-resume or cancellable continuation owns a unit cell

### Motivation

Decision S6 (2026-10-08). Tier 1's soundness property S6 asks
that a continuation caught at a must-resume or cancellable operation be used as often as it was
caught, and a must-resume one never be cancelled. BoLo's linearity is linearity of resources: no
`own` cell is leaked. A `κ` held no resource of its own, so a run that consumes it, resumes it twice or
cancels a must-resume one left the memory as a correct run would, and Core's relation could not tell
them apart. This entry gives each such `κ` a resource: a unit cell, allocated by the ordinary
allocator and freed when `κ` is used. It changes no BoLo definition: the cell is an `own` cell, and
BoLo's leak freedom and safety see the three runs above.

### Terms and machine

- **The handler value** is `(n, (qs, (h_ret, hs)))` (`hndVal`). `qs` is a right-nested tuple of
  tags, one per operation at the operation's index: `0` must resume, `1` cancellable, `2`
  unrestricted (`capTag qs i`, `2` where there is none).
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
- So a run that consumes `κ` ends with its cell allocated; a run that uses `κ` twice frees `ℓ` twice,
  which has no step unless `ℓ` was allocated again in between (never, under an allocator that does
  not reuse); a run that cancels a must-resume `κ` reaches `() ()`, which has no step.

### Typing

`[handle]` writes its effect's qualifiers into the term (`hndExpr n (map fst E) H e`, and
`hndTerm` at two variables): `handle_n e with H ≜ hnd (n, (qualsVal (map fst E), H)) e`. No rule
changes otherwise, and `CDerives` has the same indices. The checker emits the same tags
(`Frontend/Check/Rules.lean`, `rEffHandle`).

### Semantics

No change to `wpTS`, `wpG`, `ewpTS`, `opTable`, `contShare`, `KapRel` or the relation.

- `ewp_handle` takes the handler's tags and the hypothesis that each operation's tag is its
  qualifier's; `ewp_handle_vals` discharges it at `[handle]`'s tags (`capTag_ofEff`).
- At a must-resume or cancellable operation, the clause runs after the cell's allocation
  (`ewp_kappaCell`, from 6.141 through `ewp_alloc`), and `κ`'s relation `KapRel` holds of `kappaC`
  at the continuation's share and the cell: resuming frees the cell, then runs `hnd H K[w]`
  (`ewp_kappaC_resume`, from 6.142 through `ewp_free`); at a cancellable operation cancelling frees
  it, then cancels (`ewp_kappaC_cancel`). A must-resume `κ`'s cancel branch is at `⊤` in `kTy`, so
  `KapRel` asks nothing of it.

### Theorems

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`, `adequacyD_obs` and every compatibility
lemma keep their statements; `handle_compatC` and `handleV_compatC` are at the term with its tags.
The acceptance programs run as before, every cell freed (`Core/EffPrograms.lean`, the interpreter's
runs by `decide`); every kernel program prints the same value and `live 0` at the source and at every
compiled stage (`scripts/compile-kernel.sh`).

The machine's laws at the cell are §19 *Laws* item 1 (`Core/EffMachine.lean`). The catch of a
must-resume or cancellable operation allocates `κ`'s cell at a free location and hands `kappaC`
there (`catch_cell`), and every run from the catch that takes two steps has allocated the cell
(`catchEv_cell`): such a catch does not keep the memory. Resuming `κ` and a cancellable `κ`'s cancel
free the cell (`kappaC_resume`, `kappaC_cancel`); on a run to a value a use of `κ` releases it
three steps later (`use_frees_cell`); a must-resume `κ`'s cancel branch has no step
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
  capture event allocates `κ`'s cell (`catchEv_cell`), and a use of `κ` frees it three steps
  later (`use_frees_cell`). The reduction itself is not yet a Core theorem. The typing's side is:
  a clause that consumes `κ`, uses it twice, or cancels a must-resume one has no derivation
  (`refuses_R_clauses`, §19 *Laws* item 4).

## 26. Entry 25 — a λ whose binder is dead, at an effectful returner

### Motivation

Decision E (2026-10-08). Tier 1's expressiveness properties state their schemas over every
callback body: a closed computation `M` at `F_Σ B` is passed
as the callback `λ_. M`, which the higher-order function calls at `()`. As built, Core types
`λx. M` at `1 ⊸ F_Σ B` only by `[λ]`, with `x`'s slot live. `M` does not use `x`, so a leaf of
`M`'s derivation must consume the slot, and the rules with a `!Γ` premise (`[let]` and `[then]` at
a row with an unrestricted operation) take a context whose live slots are all `!`: a live slot of
`1` is not one. `thunk M : U (F A)` takes `M` under a dead binder, at the
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
is the λ either way, so every program erases as before. The promotion (§10) takes a live slot of
`1`, since `1` is flat; `[let]` and `[then]` at a row with an unrestricted operation (§19)
keep `!Γ` and do not, so `[λ]` with a dead binder is what binds a unit argument in a body that
contains them. The checker gives every unused `1` binder the dead form
(`corpus/core-callback-dead.bc`, counts `0 0 0`).

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
  (`capB`): its `κ` has a cancel branch, and `F` is read only there. Typing also reads it at a
  cancellable wait (§29a, `OpSig.finRead`), whose cancel unwinds through the finalisers around it. A cancel row is `⊤`
  (`CTy.top`) or a row, its layers `F.rowOf`, whose capturable entries carry cancel rows in turn:
  a finite tree. The default is the empty row (`F 1`), and every existing derivation uses it.
- **Order** (`FinLe`, `OpSig.LeF`, `RowLe`). `F ≤ ⊤`; `R ≤ R′` when each entry `R` finds is the
  one `R′` finds at its key (`n i q A B` and the marker `rc` equal), with its cancel row `≤` at an
  entry `finRead` reads.
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

      K_i = U((B_i ⊸ F_Σ R) & ⊤) (lin),   U((B_i ⊸ F_Σ R) & C_i) (cancel),   !U((B_i ⊸ F_Σ R) & C_i) (unr)
      C_i = F_{F_i ⊕ Σ} 1,   ⊤ when F_i = ⊤                                          (`cancelTy`)

  `F_i ⊕ Σ` is `F_i`'s layers ahead of `Σ`'s (`F.rowOf ++ Σ`), rows being read first match. At
  `F_i = []` it is `Σ`, so `κ`'s type is unchanged for every existing derivation. `[handle]` gains
  no premise: D3's check is `[sub]` from `C_i` to the row of the code that invokes the cancel. A
  handler that never cancels is checked for nothing.
- **Every other rule is unchanged**, `[let]`'s side condition included; `[perform]` and `[raise]`
  take entries at any cancel rows.
- **No unrestricted `exn`** (decision 63's restriction, 2026-10-12). An abortive operation is
  cancellable (§18), so a checked program's effect context has no unrestricted abortive operation
  (`EffCtx.NoUnrExn`), and no name's signature is one unrestricted `exn`
  (`EffCtx.NoUnrExn.ne_exn`). E9's stored closure holds `x : bool` across `cancel k`, a `[let]` at
  a row holding `exnₒ`, and `[let]` asks a persistent context at a row with an unrestricted
  operation, an abortive one included; so E9, as E5, is typed where no `exn` is unrestricted, which
  is every context the restriction leaves: `storedKFin` and `nestedFailOutside` (§19 *Programs*)
  are typed at `ΞE`, whose `exn` is cancellable (`dAt_storedKFin`, `dAt_nestedFailOutside`,
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
    nothing owned is left behind at the run's first stop (`cancel_frame_consume`, from `wpG_garbage`;
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
  reaches `inj₂ ()` (`progOutT_run`). **`progOutTA`** is the same program at a cancellable raise of
  `2`, typed by a tied derivation at a context with no unrestricted abortive operation
  (`dAt_progOutTA`, `noUnrExn_Ξ₁₂A`), and run alike (`progOutTA_run`).
- **`cancelKeptT`** and **`progReT`**: the kept raise of `3` caught by a live `3` outside the
  region, the region re-entering the site `3` in `progReT` (`f ()` at `{1}`); cancel row `{3}`.
- **`progFinOpT`** and **`progNC₁T`**: the finaliser performs `4`, whose live instance at the
  cancel is the outer handler, which resumes it, or cancels its continuation (`[cfin-cancel]`);
  cancel row `{4}`.
- **`progConsumeT`** and **`progKeepT`**: a finaliser raises `2`, kept, and a later finaliser performs
  `4` with `2` pending: cancel row `{2, 4⟨{2}⟩}` (`pend`). `H₄ₒ`'s unrestricted clause consumes the
  continuation, and the kept error with it (`inj₁ ()`, *Open*), or resumes it (`inj₂ ()`).
- **`progNCrecT`** (the leftover clause): two finalisers perform `4` under the handler of `4` that
  cancels. The second is a leftover of the first one's cancel, so `⋈` puts `4` in the cancel row of
  the `4` in the cancel row of `1`, which the cancelling handler's clause row, its own outer row,
  cannot hold: no derivation at any context and judgement (`not_der_progNCrecT`). Its run ends at a
  `perform 4` no handler catches (`progNCrecT_run`, `progNCrecT_stuck`).
- **`e7c nw ni qi`** (D3, E7c): `timeout (handle exnᵢ {…} (body (raise exnᵢ ())))`. `timeout`
  handles a cancellable `wait : 1 ↠ 1` and its clause cancels `κ`; the body's finaliser raises
  `exnᵢ`, handled only inside the cancelled region. `[then]` puts `exnᵢ` in `wait`'s cancel row, and
  the clause reads `κ`'s cancel branch at its own row, so no derivation types the program at a row
  without `exnᵢ` (`not_der_e7c`). At the row of `exnᵢ` it is typed, by a tied derivation at an
  effect context declaring `wait` and `exnᵢ` (`dAt_e7c_lift`, `d_e7c_lift`); at a cancellable `exnᵢ`
  that context has no unrestricted abortive operation (`noUnrExn_Ξe7c`).

**A pipe connector's step** (#918) is `[then]`: `M` resumes one stage's stored continuation, and
`Γ₂` holds the others', which `D` cancels (`corpus/core-pipe-step.bc`). `[then]`'s `!Γ₂` premise
holds exactly when the step's row has no unrestricted operation at any depth (`¬Row.UnrD`: no
`unr` operation, and none in a capturable operation's cancel row at any depth); a stage's
continuation is `U`, not `!`, at `lin` and `cancel`. Several stage cancels share one cancel region
when they are the finalisers of one captured continuation that the handler cancels
(`corpus/core-pipe-close.bc`), and `[cfin-raise]` then keeps the first cleanup error; as nested
ordinary unwind frames, the latest error wins instead. In these programs no cleanup raises. The
first-error region with raising cleanups is traced on the machine, untyped; a checked instance
needs the checker to emit `[then]` at a non-empty `Σ_D` (#868).

### Lowering

The backend lowers a finaliser that raises (`Backend/Clos/Capture.lean`, `Backend/Clos/Unwind.lean`),
not one that may suspend, performing an operation of a control handler: an unwind and a cancel arm
call a finaliser directly. `Capture` rejects such a finaliser with a message. The four shapes, a
finaliser that performs (`progFinOp`), a cancel nested in a cancel (`progNC₁`), and a kept error
consumed with an unrestricted continuation or resumed (`progConsume`, `progKeep`), are Lean runs
(`Core/EffCancel.lean`, `Core/EffCancelTyped.lean`) and interpreter runs, not kernel programs. The
checker emits finalisers that perform (*The checker*, below); one that may suspend is refused by
the backends as above, so such a program checks and runs at `bcc interp` only (#869). No kernel
program and no count changes. Finalisers that raise run at every stage in the kernel programs `e7a`, `e7b`,
`e7d`, `e8b` and `stored-k-fin` (§19 *Programs*).

### The checker (#868)

The checker emits `[then]` with a finaliser at its own row, and the cancel rows `[handle]` gives
its clauses. No Core change: `CDerives.effThen`, `CDerivesAt.effThen`, `TDerives.effThen` and the
cancel rows `fs` of `effHandleV`/`effHandleVB` are as above.

- **Cancel rows in core text.** A row entry of a cancellable or an unrestricted operation may
  carry its cancel row, `n.i cancel[R] A ~> B` or `n.i unr[R] A ~> B`, `R` a row written as a
  function's row is (`1.0 cancel[3.0] 1 ~> 0`). `⊤` is written `cancel[top]` (or `cancel[⊤]`),
  alone inside the brackets; the printer writes `[top]`. `top` elsewhere in a row is refused: "`top`
  (`⊤`) is a cancel row only: write it as `n.i cancel[top] A ~> B`". A bare `cancel` or `unr` has the empty cancel row, so text written before reads the
  same, and `Row.pp` prints the brackets only when the row is not empty, so a printed program reads
  back. `lin[…]` is refused, and so is a cancel row on an abortive operation. `elabRow` puts `R` in
  `OpSig.fin`.
- **`[then]` at the finaliser's row.** `x <- M unwind (D); N` is checked by `[then]`. `D` is
  checked at the empty row first; a finaliser that performs nothing gets `effThenA` with `M` at the
  site's row `Σ`, the derivation as before. Otherwise `D` is checked at `Σ`, and `Σ_D` is the row
  `D`'s derivation needs, read the same way as `Σ_M`'s (below: each operation `D` performs, at the
  cancel rows its own derivation needs); `D` is checked again at it, falling back to the site's
  filter; if it does not check there, the derivation at `Σ` is kept (the kernel's premises decide
  `[then]` at whichever row is used).
- **`Σ_M`, `M`'s own row.** When the finaliser performs and `hfin` fails with `M` at `Σ`, `Σ_M` is
  the row `M`'s derivation needs, synthesized from it: a `perform`, `await` or `raise` contributes
  its operation at the empty cancel row; a value's body (a thunk or a λ) contributes nothing where
  it is built, its row counted where it is forced or called; a call, its callee type's row, cancel rows included; a `[sub]`, its subterm's; a
  `[then]` inside `M` gives each capturable operation of its head the least cancel row that
  `ThenLe` and `PendLe` allow over its finaliser's row; inside `handle_n` the operations of `n` drop
  out; rows join by operation key, `⊤` absorbing. (So `progNC₁T`'s `1.0` is taken at the empty
  cancel row, and `progConsumeT`'s at `{2.0}`.) It is restricted to `Σ`'s operations, `M` is
  checked again at it when `hfin` holds there, and otherwise `M` stays at `Σ`; `RowLe Σ_M Σ`
  holds. `hfin` is decided over `Σ_M` (`thenFinB Σ_M Σ Σ_D`: for each operation of `Σ_M` whose
  cancel row is read, the cancel row of the operation `Σ` finds at that key holds `F ⋈ Σ_D`), and
  `PendPers` over `Σ_M` (`Σ_D.UnrD → Σ_M.PendPers`). So a capturable operation the finaliser
  performs need not be in its own cancel row.
- **The deciders.** `ThenLe`, `PendPers` and `divB Σ_D = false` are decided by `thenLeB`,
  `pendLeB`, `thenFinB`, `pendPersB` and `finPersB`, each with its `_sound` lemma (axioms within
  `propext` and `Quot.sound`); `thenFinB_sound` states the kernel premise over `Σ_M`:
  `Row.find SM n i = some o → Row.find S n i = some o' → o.finRead → ThenLe o.fin SD o'.fin`. A
  refusal names the operation that fails, at the cancel row it was checked with (D3), and which
  half of `PendLe` fails; it never says a row lacks what it holds. A nested entry is named as such
  ("the cancel row of 1.0 … holds 4.0, whose own cancel row … must hold …"). At `Σ_D = []` the checker emits `effThenA`, as before; `effThen` only at a
  non-empty `Σ_D`.
- **Handlers read their operations' cancel rows.** `[handle]` passes `fs j`, the cancel row the
  handled row gives operation `j`, so a clause's `κ` has its cancel branch at
  `cancelTy Σ (fs j) = F_{F_j ⊕ Σ} 1`. A clause that cancels `κ` then performs, at its own row,
  what the cancelled region's finalisers perform: D3 is `[sub]` there.
- **Written, and checked.** A cancel row is written, in handler and ascription types; a row the
  effects pass infers (`Env.rowOf`) carries the empty cancel row. `[then]`'s `hfin` checks each.

### The surface (#868, #953)

1. **Surface cleanup.** `with h(…) { M } finally { D }` (≜ `x <- (with h(…) { M }) unwind (D); D; x`)
   and `x <- M unwind (D); N` elaborate `D` as written, its operations resolved to the sites in
   scope. The checker types `[then]` at `D`'s own row `Σ_D` (*The checker*, `finC`): no change in the
   elaborator's output form. A raise in `D` during an unwind supersedes the pending one (§19 law 6,
   E8b); during a cancel it is kept and re-raised at the canceller (§27, E7b).
2. **Cancel rows are inferred, per operation name** (`Frontend/Elab/Fins.lean`). At each
   `x <- M unwind (D); N` of the effects pass's output whose site's row is `Σ` (the row of the
   function it is in, and the operations of the handler sites around it in that function), `Σ_D`
   is the entries of `Σ` that `D` performs: its `perform[n.i]`/`abort[n.i]`, and the rows of the
   functions it calls, less the operations of sites inside `D`. Every entry of `Σ` that captures a
   continuation (`capB`) has `Σ_D` in its cancel row. An operation's cancel row is the union over
   the whole program (site names are static, one per site). Each entry of a cancel row carries the
   empty cancel row.
3. **The rows carry them.** The effects pass runs once, the table is read off its output, and,
   when it is not empty, the pass runs again with it: `Env.rowOf` gives every row entry (a copy's
   row, a block's, a recursive group's, a stateful handler's state function) its cancel row, and a
   handler site's info carries its operations' (`HInfo.fins`). The typed elaboration builds the
   site's row `Row.ofEff n ops 0 fs ++ Σ` and its clauses at `clausesTy Σ R ops fs` (`κ`'s cancel
   branch `cancelTy Σ F`). The kernel checks every one of these (`[then]`'s `ThenLe`, `[handle]`,
   `[sub]`'s `finLeB` at calls); the elaborator decides nothing the kernel does not re-check.
4. **A clause that does not use a cancellable `κ` whose cancel performs** (#953; Rust's drop
   model). The kernel's `κ` is consumable only when its cancel branch is
   `F 1` (empty row); a consume is effect-free. When its cancel branch `cancelTy Σ F` performs
   (the inferred cancel row `F` or the handler's outer row `Σ` is not empty), the elaboration
   cancels `κ`, `u <- (force k).2; let () = u; T` (`[&E₂]`), exactly once on each path of the
   clause that does not use `k` (`Frontend/Sugar.lean`, `cancelAtEnds`, `cancelDropped`):
   - **on finishing**, at the end of the path, after all its effects: before a terminal value
     `return V` (`callFree`), as SPEC §12 places a consume; after a terminal that performs (a call,
     an operation), which is the path's last effect: `x <- T; cancel k; return x`. `<>` and
     `absurd` absorb it;
   - **on an abort or a cancel through the path**: each head `M₁` of `x <- M₁; N` on the path,
     `k` live and not mentioned by `M₁`, is `x <- M₁ unwind (cancel k); N` (`[then]`, the finaliser
     at the cancel's row, *The checker*) when the row it is typed at holds an abortive operation of `Σ` or
     one that captures a continuation. That row is read, not rebuilt from syntax
     (`Fins.opsOf`, one walk the typed elaboration and the inference share): the operations the
     head performs, the row of every function it names as the effects pass wrote it in that copy's
     type (`Fins.fnRows`; a local's by its type), and, for a handler site in the head, the row the
     kernel types `handle_n` at, the row around it where its clauses run (`Σ`). `UNPROVED:` at the
     walk (a copy is named only to be called, or passed to a block parameter whose callee's row
     holds it; an over-counted capturing operation makes the elaboration refuse, below). Any other
     head is left as it is, so a clause whose heads can neither abort nor be cancelled through and
     that uses `κ` on every path elaborates exactly as without this entry. A region of the clause's
     own (`x <- M₁ unwind (D); N`) whose body does not mention `k` is such a head as a whole: its
     own finaliser runs first, then `k`'s cancel. A loop is such a head when its body can abort or
     capture (a capture is then refused, below); its `break` and `continue` stay in the clause, and
     a `return` in a clause is refused before this rule. A loop whose value is bound
     (`let r = for …; N`) is wrapped with the binding of its value,
     `r <- (loop …; r <- return forRes; return r) unwind (cancel k); N`, so the wrap is around the
     loop as the typed elaboration elaborates it (`boundRes?`). A head of `x <- M₁; N` or of
     `x <- M₁ unwind (D); N` that mentions `k` is entered by the same rule.
   Exactly once: from its binding `k` is live until the first of a head's abort (its finaliser
   cancels it; nothing after runs), the end of the path (the cancel before the terminal), or a use
   the program wrote (nothing is inserted after it). `[then]`'s finaliser and rest are exclusive,
   and the kernel checks `k`'s linearity on each. In a handler with a state (§21) the clause's code
   is the state's function, which the path continues into (`HInfo.stateful`), by the same per-path
   rule (an arm that resumes, an arm that drops). The rule lives in `Frontend/Elab/Fins.lean`
   (`cancelAtEnds`), used by the typed elaboration and by the inference.
   **Order.** The clause's effects come first, then `κ`'s cleanup, on both paths:
   `corpus/fin-cancel-order.bc` writes `A` (finish) and `B` then raises `7` (abort); the cleanup
   raises `3` both times: `AB`, `(inr i32[3], inr i32[3])`. Cancel-first would write nothing; an
   abort that left `κ` uncancelled would answer `inr i32[7]`. The kernel program `timeout`
   (`cancel k; return ff`) agrees: its only effect after the cancel is the terminal. The checker's
   consume insertion is not reused: it inserts `consume` nodes that carry `Consumable`.
   **The inference needs no cancel row for the inserted cancels.** A wrapped head performs no
   capturing operation of `Σ` (that is refused, below), so no cancel row is read under it, and
   *The checker*'s `[then]` takes `Σ_M`'s cancel rows from `M`'s own finalisers. **Limit:** the cancel
   performs the cancel branch's row `F ⊕ Σ`; when a wrapped head performs a capturing operation of
   `Σ`, that operation's cancel row would hold itself (`⊤`), which the kernel refuses (without the
   wrap it refuses `k` live across it): refused by the elaboration, "this clause's continuation is
   live across `Ask.ask` (1.0), an operation that captures a continuation, and its cancel performs:
   if the continuation captured at `Ask.ask` (1.0) is cancelled, this one must be cancelled with
   it, and `Ask.ask` (1.0)'s cancel row would contain itself" (`corpus/reject/fin-cancel-capturing.bc`).
   Core text spells `⊤` (`cancel[top]`); the surface does not infer it there (*Open*).
   **What a terminal performs** is read syntactically (`callFree`): every call counts as an effect,
   an answering effect's (a capability's, in no row) included, so a cancel is never placed before
   one; it decides only the order of the cancel and a call that performs nothing.

5. **Capabilities stay refused** (`Frontend/Elab/Effects.lean`, `trC`'s `.unwind`): an answering
   effect's capability used in `D` is refused, "a cleanup can't yet use `c`, which the body also
   uses (the kernel's [then] splits them; see #868)" when `M` uses it too, and "a cleanup can't yet
   use `c`: a capability is threaded through the code around it, and the kernel's [then] gives the
   cleanup a context of its own (see #868)" when only `D` does. This is the kernel question K-b
   (Open).

6. **Reading cancel rows back.** The typed elaboration and its inference re-read a `handle_n`'s
   row from its clauses' types with their cancel rows (`clausesReadF`, `finsOf`), as the checker
   does (`Frontend/Sugar.lean` `.handle`, `Frontend/Elab/Infer.lean`).
7. **`Σ_D` from the derivation**: *The checker*'s `opKeysOf` reads what a `[sub]`'s subterm performs, not
   the sub's source row (`corpus/core-fin-sub-row.bc`); a two-operation
   cleanup needs it.

8. **A thunk at its own row** (`Fins.walkV`): a block literal's finaliser is inferred at the row the
   block runs at, the operations it performs (by the handler sites' and functions' entries,
   `glob`), beside the row around it (`corpus/fin-block-finaliser.bc`).
9. **A handler with a state, typed at its site's row** (§21). Its clauses answer the
   function of its state, which the site forces where the `with` is. The typed elaboration types it at the row of the site (`hndCtlC`, `S`), the fact the site's own typing gives. They differ when
   a site in scope performs nothing below a borrow block that sits between it and the `with` (the
   block's callback is at the row its body performs): the function's row then held the unused
   site and the force at the site was refused ("not within the row"). (`corpus/state-row-unused-site.bc`). `corpus/fin-cancel-unused-site.bc` (`e2`): `B`, `inr i32[3]`.

| program | what it shows | answer |
|---|---|---|
| `corpus/fin-e7b.bc` | E7b: a cleanup's raise during a cancel, kept, re-raised at the canceller | `inr ()` |
| `corpus/fin-e7d.bc` | E7d: two cleanups in a function, cancel rows through its row; first error kept | `inr ()` |
| `corpus/fin-e8b.bc` | E8b: a cleanup's raise during an unwind supersedes | `inl (inr ())` |
| `corpus/fin-cancel-reraised.bc` | `cancelKeptT` | `inr ()` |
| `corpus/fin-cancel-reentered.bc` | `progReT` (surface names are per site: the inner handler is another name) | `inr ()` |
| `corpus/fin-cancel-propagated.bc` | `progOutT` (the cleanup names the outer handler, `o.ex2()`) | `inr ()` |
| `corpus/fin-raise-unwind.bc` | `finally` raising during an unwind: supersedes | `inr i32[2]` |
| `corpus/fin-raise-cancel.bc` | `finally` raising during a cancel: kept, re-raised | `inr i32[3]` |
| `corpus/fin-timeout.bc` | #953, E10 `timeout`: dropped `κ` cancelled at two rows | `(inl (), inr ())` |
| `corpus/fin-cancel-tail.bc` | a performing terminal before the cancel | `AB`, `inr i32[3]` |
| `corpus/fin-cancel-arm.bc` | a stateful clause, `k` resumed on one arm, dropped on the other | `(inr i32[3], inl (inl i32[5]))` |
| `corpus/fin-cancel-region.bc` | an abort out of the clause's own `unwind` region | `inr i32[3]` |
| `corpus/fin-block-finaliser.bc` | a finaliser in an effectful block | `inr i32[3]` |
| `corpus/fin-cancel-unused-site.bc` | an unused capturing handler outside a stateful one | `B`, `inr i32[3]` |
| `corpus/state-row-unused-site.bc` | a state function at its site's row (no cancel) | `B`, `inl i32[5]` |
| `corpus/fin-resume-capturing-row.bc` | a head that neither aborts nor captures, `κ` resumed, no finaliser: as without this entry | `inl (inl i32[5])` |
| `corpus/fin-drop-capturing-row.bc` | the same head, `κ` dropped: cancelled at the end | `inr i32[3]` |
| `corpus/fin-handler-head.bc` | a `with` in a clause as a head, typed at the clause's row (abortive): wrapped | `inr i32[3]` |
| `corpus/fin-handler-head-raise.bc` | a `with` whose body raises to its own handler, as a head | `inr i32[3]` |
| `corpus/fin-cancel-loop.bc`, `fin-loop-break.bc`, `fin-loop-continue.bc` | an abort out of a `for` in the clause (with its own `break`/`continue`): `k` cancelled on the way out | `inr i32[3]` |
| `corpus/fin-bound-loop-abort.bc`, `fin-bound-loop-finish.bc`, `fin-bound-loop-pure.bc` | a bound loop: wrapped with its value's binding when its body raises (`inr i32[3]`); finishes and resumes (`inl (inl i32[5])`); a pure body, unwrapped (`inl (inl i32[5])`) | see left |
| `corpus/fin-generic-call.bc` | an abort out of a generic function's call, its row read from the copy's type | `inr i32[3]` |
| `corpus/reject/fin-cancel-capturing.bc` | the `⊤` limit: the clause's row holds a capturing op | message |
| `corpus/fin-cancel-order.bc` | the inserted cancel after the clause's effects, on finish and on abort (option C) | `AB`, `(inr i32[3], inr i32[3])` |
| `corpus/reject/fin-capability.bc` | `stdout` in the body and the cleanup: refused | message |

All at every stage of both backends, `live 0`. The kernel program `stored-k-fin` has no surface
twin: the stashed closure cancels `κ`, so its type is `U(1+1 ⊸ F_{[1.0]} (1+1))`, a function type
whose row is a handler's name, which a surface handler's answer type cannot write (effectful
closures, #161).

- **A function that holds a stored generator over a row** across its own operations is a
  finaliser site: each capturable operation of its row gets the close's row in its cancel row
  (§15 *Stored generators over a row*).

### Baseline

`Paper/`, `Support/`, the machine and the effectful `wp` are unchanged; no borrow rule and no borrow
lemma changes. Every existing derivation types at empty cancel rows. A program with no finaliser
that performs gets `Σ_D = []` and `ThenLe.nil`, and the checker emits `effThenA` there, so its
derivation, the judgment-freeze golden and every count are as before. `fundamentalC`,
`adequacyC`, `fundamentalD`, `adequacyD`, `adequacyD_obs` and every compatibility lemma are
unchanged: the checker emits a rule already proved. The kernel programs `e7b`, `e7d`, `e8b`,
`stored-k-fin`, `cancel-reraised`, `cancel-reentered` and `cancel-propagated` become checkable
core text with their kernel answers (`inr ()`, `inr ()`, `inl (inr ())`, `inr ()`, `inr ()`,
`inr ()`, `inr ()`), each with a corpus twin whose golden is `bcc interp`'s.
`corpus/core-fin-nested.bc` has nested cancel rows where `D` performs only part of the row
(`inr ()`), and `corpus/core-fin-sub-row.bc` is `e7b` with the finaliser's raise bound,
`u <- abort[1.0] (); absurd u`, under a `[sub]` (`inr ()`). `core-fin-cancellable` (core text) is an
`abort[1.0]` unwinding through a finaliser that performs `4.0 cancel 1 ~> 1`, checked at
`Σ_M = [1.0]`, `Σ_D = [4.0]`; `bcc interp` answers `(inr (), i32[1])`. It joins the corpus with the
lowering of a finaliser that may suspend (#869). `corpus/core-fin-top-row.bc` prints a `⊤` cancel
row and checks it again (`()`, `live 0`). `core-fin-nc` (core text, `progNC₁T`'s shape: a cancel's
finaliser performs a capturable operation whose own cancel row is empty) checks, `()`, `live 0`; it
joins the corpus when Backend2 lowers a cancel row holding a machine operation (#869).
`core-fin-consume` (core text, `progConsumeT`'s shape) answers `inl ()` and `core-fin-keep`
(`progKeepT`'s) `inr ()`, each with `live 0`; both join the corpus with #869.
`corpus/core-fin-check-nc.bc`, `-consume.bc`, `-keep.bc`, `-gapdeep.bc` and `-gapcall.bc` are
checked in the corpus (a `def` checked and not called; `main` returns `()`): the first three are
`progNC₁T`'s, `progConsumeT`'s and `progKeepT`'s shapes, `gapdeep` two nested finalisers that both
perform capturable operations, and `gapcall` a call of a function parameter;
`core-fin-check-afinc.bc`, `-same2.bc`, `-d2nested.bc` and `-dthunk.bc` are checked the same way:
`Σ_D` at its own row, two finalisers performing the same operation, a call whose row nests `4.0`,
and a closure built in `M`. At the surface, a program none of
whose finalisers performs a control operation gets an empty cancel-row table: the effects pass
runs once, and every row and clause is what it was.

### Open

- **The lowering of a finaliser that suspends** is Backend2's (§69); the old backend refuses it.
- **A dropped continuation cancelled on an abort inside a capturing operation's handler**: `⊤`,
  the limit of *The surface*.
- **Drop flags.** A head that uses `k` on some of its paths cancels it at the end of the others,
  inside the head, not at the end of the enclosing path as Rust's drop flags would.
- **A cleanup that performs a cancellable operation** needs that operation's cancel row to hold
  itself at every depth, `⊤`. Core text spells it (`cancel[top]`); the surface's inference does
  not infer `⊤` yet, so the kernel refuses such a program, and a cleanup's operations are
  `must_resume` today.
- **Per-occurrence cancel rows.** The union per name is the least row only when every finaliser in
  an operation's scope is relevant to it.
- **An `if` as the head of a written `unwind` that uses `k` on one branch**: the head is a value
  `run case …`, which the elaboration does not enter (values are not paths); refused.
- **A handler site inside a block literal in a head** is counted at the clause's row: an
  over-count, which can refuse a program.
- **Rows the typed elaboration makes itself** (a `for`'s site, a stored generator's) carry empty
  cancel rows; a finaliser inside one that performs is refused by the kernel.
- **The lowering of a finaliser that performs a control operation** (#869): neither backend lowers
  it, so such a program runs at `bcc interp` only.
- **`Σ_M` and `Σ_D` are synthesized from the derivations**, not proved least: they can over-count
  (a thunk built and never forced), which is safe, since the kernel checks `M` and `D` at the rows
  taken.
- **`Σ_M` is resynthesized only when `hfin` fails at `Σ`.** A program whose `hfin` holds at `Σ` but
  whose `PendPers` fails there, and would hold at `Σ_M`, is refused: a gap in completeness, not in
  soundness.
- **`await`'s cancel rows** are not read by the synthesis; core text cannot reach them today.
- **Nested `[then]`s are checked again at each level**, so the work is exponential in their depth.
- **The deciders check every layer and member of a cancel row**, the kernel the first `Row.find`
  hit: stricter only when a cancel row repeats an operation key.
- **Answering effects in a finaliser** (a capability: `Stdout`, `Fs` #769, `Net` #597; a `fn`
  effect): the capability is a threaded `mut` borrow, and `[then]` splits the context `Γ₁ | Γ₂`,
  so `M` and `D` cannot both hold it; R1 (§29) needs empty cancel rows (`Row.ResumeO`), and an
  unwinding lend's finaliser `d : Ref T ⊸ 1` is closed, pure and abortive only. It does not type
  today by any route, and #940 (a `let mut` both `M` and `D` write) has the same root. The
  smallest change proposed is a fused `[then]` over a lend (`m : Mut @a T ∈ Γ₂`; `M` gets a
  reborrow, `D` gets `m` back at `Σ_D`): one rule and its compatibility lemmas. Its raise path is
  direct; its cancel path is a lend across a suspension, which needs #844 Tier 2 and #821.
- **An owner's finaliser that performs** (a declared value's drop that closes a socket): not a
  consume (§42 *Not this*); Backend2's `genLendU` lowers only a constant finaliser.
- **Task codata** (`lib/async.bc`, `F (A + …) & F 1`): a task whose finalisers perform needs its
  close at `F_R 1`; it waits on the lowering of a finaliser that suspends.
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
  simulation relation that confines the law's frames to continuations. "No error is consumed" is
  proved on the runs whose `[op]` steps capture no kept error. An unrestricted continuation
  discarded with a kept error inside it is the tolerated exception; a must-resume or cancellable one
  holding a kept error waits on S6's use exactly once.

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
  the share's stratum besides `KapRel`. At a must-resume or cancellable operation `κ` also holds its
  capture cell (§25), an `own` cell, in every stratum (`ResU.inStratum_single_own`). From `KapRel`,
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

The chain interpretation of §62 has a second named hypothesis of the same form, `HandlerLawN`
(`Core/Chain/HandlerLawN.lean`): the compatibility lemmas of `[handle]` at a value form, BOXED-κ
`[handle]` and `reify`, from which `FundamentalN` and plain adequacy `Goal791N` are proved (§62,
*The named assertion*).

*R1 and `PinLaw` stay as stated here until surface A1 (#843, §19).*

**R1 as on main** (the checker's rule; decision 71's freeze is void by decision 72, and §62
replaces it as design). R1, with §29a's cancel-path
widening, stays exactly as this entry states it, and `PinLaw` (`Core/PinLaw.lean`: `lendFrame`, `loopFrame`) gets no new field, case or premise.
R2 is in the judgment and is not emitted, and that is frozen too. T1 is §19's rule until surface
A1 (#843), for §62's shapes.

### Typing

    Δ ⊨ b defined   x fresh   T, B free of 'x   B has no U   Δ ⊢ T ⊒ @b'   Row.ResumeOC Σ 'x
    M closed but for m   ·  ⊢ d : Ref T ⊸ 1        Δ, 'x ⊏ b ; m : Mut 'x T ⊢ M : F_Σ ([@x] B)
    ─────────────────────────────────────────────────────────────────────────────── [lend-R]
              r : Ref T ⊢ withborU d r (Λ. λm. M) : F_Σ (Ref T ⊗ B)

    Δ; · ⊢ e : J        Γ consumed
    ───────────────────────────────── [nil-dead]
    Δ; Γ ⊢ e : J

- `Row.ResumeO Σ 'x`: every operation of `Σ` resumes (none abortive), none is unrestricted, its
  cancel row is empty, it answers `1`, its name is not `0`, and its argument is closed data: free
  of `'x`, outliving every lifetime, with no `U` (`NoThunkT`). `await` and `yield` are such
  operations (`resumeO_await_yield`); `raise` is not (`not_resumeO_raise`). The rule's premise is
  `Row.ResumeOC`, which also admits a cancellable wait and its cancel target (§29a), and every row
  `Row.ResumeO` admits (`Row.ResumeO.toC`).
- The term is §19's unwinding `withbor` (`withborUV d`); only the callback's row differs. `d` is the
  owner's finaliser, the source's consume: it runs when a continuation captured inside the
  callback is cancelled.
- `[lend-R]`'s premise is the callback's derivation in the extended judgment, so a relaxed lend
  may hold another. The rule concludes at the context `r : Ref T` alone. `[nil-dead]` places it
  under a program's other slots, as `(λr. withborU d r (Λ. λm. M)) x`: the λ is typed at the empty
  context and placed at any consumed one. `[nil-dead]` is admissible for `CDerives`
  (`CDerives.append_dead`, §26) and sound by `semC_dead`; it is in the extended judgment because
  `[lend-R]` concludes at one fixed context. It also lets a relaxed lend sit under binders inside
  another's body, so `LendFrame`'s premise ranges over those derivations too.
- R2 (`lendLoopR`, the `imm` lend over a loop whose state holds the borrow,
  `docs/async-capabilities.md` §3.3) is in the judgment as well, an instance of `LoopFrame`;
  `PinLaw.loop` derives its compatibility lemma. The checker does not emit it, and that is frozen
  (T1, §19: the checker's rule until surface A1, #843, for §62's shapes).

**The extended judgment.** `CDerivesP` (`Core/PinDerives.lean`) is `CDerives` with every premise
in `CDerivesP`, plus `lendR`, `lendLoopR` and `nilDead`. It is generated from
`Core/Fundamental.lean` by `scripts/gen-pin.py` (templates in `scripts/pin/`), so a rule added to
`CDerives` is in it after a rerun; `python3 scripts/gen-pin.py --check` fails when the generated
files are stale. §28's BOXED-κ (`effHandleVB`) is in it so, its case in `fundamentalC_pin`
`handleV_compatCB`, as in `fundamentalC`.

**`PinLaw`** (`Core/PinLaw.lean`) is a `structure … : Prop` of two schemas: `LendFrame`, the
relaxed `withborUV` lend's compatibility lemma at every `LendForm` (R1 is the form `ref`), and
`LoopFrame`, the per-observation lend's (R2). Each is stated at its rule's own premises plus the
callback's (steps') `SemC`, mentions no depth or holder, and has every quantifier over code a
quantifier over `CDerivesP` derivations. It is a hypothesis of the theorems that use it. `PinStop`
and `PinLoop`, the compatibility lemmas of R1 and R2 at the rules' premises alone, are derived
(`PinLaw.stop`, `PinLaw.loop`), and `pinLaw_iff` shows the two schemas say what they say together.

`LendFrame`'s row premise is `Row.ResumeOC` (§29a), which widens `Row.ResumeO` for the cancel path
in three ways, and these widen the asserted domain:
1. the marked abortive cancel target is admitted at operation `1` of a name whose operation `0` is a
   cancellable wait. This is OQ-1 option (a) of `docs/async-capabilities.md`, taken for the cancel
   path only: an abort at an operation handled outside the lend, after a suspension inside it. The
   evidence is OQ-1(a)'s: the LIFO frame lemmas (`wpTS_M_frameU`) with GhostEnd's `Consume` are proved;
   that they compose across the suspension is not checked;
2. the cancellable wait answers `1 ⊕ 1`, not `1`. This is OQ-5's restriction, relaxed for marked
   waits. The answer is read only by `[await-c]`'s `case`, since `[perform]` refuses a marked
   operation;
3. the wait's cancel row is any cancel row.

The relation does not read the marker. Until the effect context carries it (§29a *Open*), a kernel
handler chooses its markers, so the domain is lends across any marked `lin 1 ↠ 1 ⊕ 1` operation and
its marked abortive partner.
`LendFrame`'s premise is the body's `CDerivesP` derivation, so what it covers is every body that
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
only the borrow crosses it (L0, U3) is refused (T1, §19: the checker's rule until surface A1, #843, for §62's shapes): the program ends the borrow
before the `await` itself. Each refusal names that fix, or moving the value in and out.

The checker types `withbor2r` by `[lend-R]` at the slot of `p`: it checks `M` at `Δ, 'x ⊏ @b` and the
context `m : mut 'x A` alone, and decides `Row.ResumeOC` (`Row.resumeOCB`, sound), `NoThunkT` (`noThunkB`)
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

`bcc trusted` lists the same under `typing:`, each site with the schema of `PinLaw` it instantiates
(`LendFrame` at its form, or `LoopFrame`).
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
    PinLaw.stop : PinLaw → PinStop          PinLaw.loop : PinLaw → PinLoop
    pinLaw_iff : PinLaw ↔ PinStop ∧ PinLoop

`fundamentalC_pin` is `fundamentalC`'s induction, case for case, with `hPin.lendFrame` at `lendR`
(form `ref`) and `hPin.loopFrame` at `lendLoopR`, each at the induction hypothesis of its callback
(steps), and `semC_dead` at `nilDead` (`Core/PinFundamental.lean`, generated). `PinLaw.stop` and `PinLaw.loop` follow from it;
`PinLaw.of_stop_loop` is the converse.
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

- A derivation that uses a relaxed rule is not claimed tied (decision R): a tied `CDerivesP` is not
  built.
- What `LendFrame` ranges over (above): kind R of `docs/unsafe.md`.
- *Not built; §62 is the design that replaces them:* L0 (U3), R2 at the
  checker (U6), shrinking `PinLaw` (U8; its live analogue is #838, shrinking `HandlerLawN`), and
  `docs/async-capabilities.md` OQ-1 to OQ-5 as routes to wider relaxed lends. BOXED-κ (U1,
  §28) and `lib/async.bc` (U2, §30) are built.

---

## 29a. Entry 28a — cancellable waits: a cancel as a resume with a raise (#750)

### Motivation

#750 (plan agreed in comment 6528120064, user decisions of 2026-10-31). A task's cancel is a resume
of its stopped `await` with `inr ()`, which the task re-raises as `cancelled`; finalisers run with
the task's region live. Cancellation is level-triggered (Trio-style): the cancelled state belongs to
the task's scope, and every cancellable wait in a cancelled scope raises `cancelled`. Shielded
waits ignore it. The kernel gains a marker and two proved rules; `PinLaw` keeps its two schemas,
its lend schema's row widened (§29).

### Typing

- **The marker.** `OpSig.rc : Bool` (default `false`), mirrored in `CTy.eff n i q A B fin rc C` and
  compared by `OpSig.Sig`, so `[sub]` neither adds nor consumes it. Neither the relation nor the
  machine reads it (`semC_effOf_rc`: the relation at `F_Σ A` reads `Σ` up to markers). A
  *cancellable wait* is `OpSig.Cancellable`: marked, `lin`, answering `1 ⊕ 1`; its *cancel target*
  is `OpSig.CancelTarget`: marked, abortive, at `1`. Both are decided (`cancellableB_iff`,
  `cancelTargetB_iff`). The handler rules `effHandleV`/`effHandleVB` take the body's row as
  `Row.ofEff n E 0 fs cs ++ Σ`, `cs j` the `j`-th operation's marker (`CDerives.effHandleCs`).
- **`[await-c]`** (`CDerives.effAwait`, in `CDerivesAt`, `CDerivesP` and `TDerives` too):

      Γ consumed   Σ(n, 0) = a Cancellable   a.A = 1   Σ(n, 1) = c CancelTarget
      ────────────────────────────────────────────────────────────────── [await-c]
      Γ ⊢ await_n ≜ perform_n (0, ()) to r. case r {inl u. return u | inr u. raise_n (1, u)} : F_Σ 1

  `[perform]` gains `hac : o.rc = false` and `[raise]` `hrc : o.rc = false`: only `[await-c]`
  performs a cancellable wait or raises its cancel target, on `inr ()` (`not_der_perform_await`,
  `not_der_raise_cancelled`). `await_compatC` proves it
  from `[perform]`, `case`, `[raise]` and `[let]`; `fundamentalC` keeps no hypothesis.
- **Cancel rows** (§27) are read at `OpSig.finRead o := capB o.q o.B || (o.rc && !o.abort)`: `FinLe`,
  `OpSig.LeF` and `[then]`'s `hfin` record a finaliser's row in a cancellable wait's cancel row.
  The relation reads `fin` only at `capB`, as before.
- **`[lend-R]`** takes `Row.ResumeOC Σ 'x` (§29): each entry `Row.ResumeO` admits, a cancellable wait
  at operation `0` of a nonzero name taking closed data at any cancel row, or a cancel target at `(n, 1)` whose
  `(n, 0)` is a cancellable wait; and `Row.divB Σ = false` (a marked `tick` is refused,
  `not_resumeOC_markedTick`). No other abortive operation is admitted (`not_resumeOC_raise`).
- **`[then]` with a finaliser that may loop** (`CDerives.effThenDiv`, also in `CDerivesAt`):
  `effThen` without `Row.divB Σ_D = false`, at a body with no capturable operation. **Proved**: at a
  `Div`-free `Σ_D` by `then_compatC`, at a `Div` row by `then_compatC_div`. Its proof follows
  `cwp_then`: `ewp_frame_then_orR` (the segment, a raise's `D (); raise` as a premise),
  `seq_raise_cwp` (that run at `cwp`, by `cwp_bind_le` at the seq-raise frame),
  `closing_then_div` (`Closing` with `D`'s own `Closing` at `closeSig :: Σ_D`), and
  `cwp_then_div` (the coinduction up to `cwp`). `hcap` keeps every cancel run off `D`. A cancel
  unwinding through a ticking finaliser is typed by it (`d_thenTickAwait`), and by typing a task body
  would reach that under `div_fuel`, whose callback is at `tick` ahead of the task's row (no
  derivation here composes the two); `effHandleV`'s `hdv`
  keeps `Div` out of the task handler's own row only. A closed program uses it and runs
  (`d_thenDivFuel`, `thenDivFuel_runs`). A finaliser whose row holds `Div` puts `Div` in the
  enclosing row, which must be handled before the program is closed; totality covers the rest.
- **A value that is not consumable is closed on every exit, the cancel included.** No new premise:
  `[await-c]`'s cancel target is abortive, so the row `Cancels` (`Row.cancels_of_await`), and
  `[let]`'s `hW` refuses a value that is not `OwnFree` held across the wait
  (`let_refuses_decl_across_await`). A finaliser that consumes it is the way out
  (`d_closeOnCancel`). A value that is consumable gets it on the cancel unwind, as on an error's:
  only values that are not consumable need written code.
- **`Row.CancelTotal` / `Row.CancelEnds`** (`Core/AwaitCancel.lean`), decided with `_iff`s, are
  typing-only predicates and premises of no rule. `CancelEnds` (`CancelTotal` and no `Div` where the
  row has a cancellable wait) is the termination target: a cancelled task ends at a `Div`-free row.
  No theorem reads `CancelEnds` yet: the general statement is open. A closed instance ends by
  adequacy (`stickyScope_runs`). A row with `Div` carries no termination guarantee.

### Semantics: level-triggered cancellation

No machine step, relation clause or primitive is added. The cancelled state is the task handler's
state; its `await` clause reads it.
- **Law 5c** (`await_cancelled`): with the flag at `inr ()`, `hnd (n, H) K[await_n]` steps to
  `hnd (n, H) K[raise_n (1, ())]`, `K` free of `n`, the memory unchanged; so every later wait in the
  scope raises again. No handler of `n` sits between the raise and the wait's handler
  (`cancelled_not_caught`, with `catch_abort`). A shielded
  wait (an unmarked `complete`) reads no flag (`shield_catch`): a finaliser that must wait uses it.
- **Laws 5 and 6** (§19) stay for κ.2 cancels; for cancellable waits 5c replaces law 5 and law 6's
  *first error kept*, while law 6's *Finally* and *Unwinding* apply to the `cancelled` raise: a
  finaliser's raise supersedes it. A handler inside the task may catch that raise; the cancel is
  then raised again at the next cancellable wait, not lost (`d_swallow`, `sem_swallow`,
  `swallow_sticky`, `retry_sticky`).
- **The scheduler's clause is typed by passing the state**: `d_stickyScope`, an immediate scheduler
  at the answer `U(Flag ⊸ F Flag)` whose `await` clause resumes `κ` with the flag
  (`stickyScope_eval`).

### Not built

The surface `await` and `complete`, `lib/async.bc`'s `cancelled` clause and a suspending scheduler's
typing, `run_in`, the checker emitting `effAwait` or `effThenDiv`, the nursery over owned or copied request data
(over borrowed data it stays refused after A1: #821 / #844 Tier 2), cancel scopes inside a task, and the lowering of a
suspending finaliser.

### Open

- **The effect context carries the marker.** `RowAt` compares `(q, A, B)` only. Before the surface
  declares a cancellable wait, `EffCtx` carries `rc`, `RowAt` compares it, and the tied handler rules
  derive `cs` from `Ξ`.
- The general `CancelEnds` termination theorem.
- `finRead` and `CancelTotal` have no semantic consumer under level-triggered cancellation; whether to
  keep them is the user's.
- Route (a) for derived consumes: a task holding borrows is not consumable and is awaited or
  cancelled explicitly; each refusal names its fix (unit B).

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
   resumes was always a div loop (§16 *Effectful bodies*), and the surface wraps no handler around
   a div computation (§21 *Open*), so a task with a counted loop that awaits could not be spawned.
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
  is refused (T1, §19: the checker's rule until surface A1, #843, for §62's shapes): a task ends its borrow before each `await`, or is lent
  the place from outside its scheduler (`spawn_in`, §32).

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
- the group's lifetime parameters are **quantified in its fixed-point type**: each member's field
  of the record `R` (§21) is `∀'a₁ < b₁. … ∀'aₙ < bₙ. (E ⊗ Pⱼ ⊸ F_Σ (E ⊗ Tⱼ))`, the parameters
  nested in the order they are declared, so that a bound naming an earlier parameter is under its
  binder. The generator's field for a member is `Fun 'a₁ < b₁. … fun p → body`. Only the
  capabilities' lifetimes `'l` stay outside the fixed point, fixed for the whole recursion: the
  generator, each layer's transformer and the fixed point's `R` are generic in them alone
  (`!(∀'l⃗. !U(…))`). A member's copy keeps the type a copy has, `all 'a < @.` over the group's
  lifetime parameters and then the capabilities', and instantiates the field at its own `'a⃗` after
  projecting it;  `[spec §31]`
- **a call of a member inside the group instantiates the member's lifetime parameters afresh**, at
  the call's lifetimes: `((force (unbang g) ()).j ['ℓ₁] … ['ℓₙ]) (E, W)`. A member may so call itself
  on a view at a shorter lifetime than its own, the view of a child a load exposes (`'y` of
  `borrow imm *t { 'y, v -> … }`). The effects elaboration writes the application without the
  lifetimes; the typed elaboration fills them, by one general rule: **an application `M x` of a
  computation whose type is `∀'a⃗ < b⃗. P ⊸ C`, its lifetimes not written, is `M ['ℓ⃗] x`, each `'ℓ`
  read off `x`'s type matched against `P`**, as the lifetime arguments of a call of a generic
  function are (§15). A lifetime `x`'s type does not determine is the meet of the lifetimes in
  scope. The kernel checks the instantiation against each bound, as at any `.inst`, and refuses one
  that does not hold. A call of itself is at the group's own type parameters;  `[spec §31]`
- the abortive branch of a call of itself, `abort[e.0] ()`, is ascribed the member's result when
  the result names none of the group's lifetime parameters; otherwise it is not ascribed, and the
  checker types it at the other branch's answer (`case`'s synthesis inside a row, §19);  `[spec §31]`
- under the heap driver (§20), the machine's source `g__mach_src` is a template, and each of its
  instances `g__gN__mach_src` is made into its machine `g__gN__mach` (`recMachine`), its frames at
  the instance's types; a member's copy `x__deep` names the machine at its type arguments,
  `g__mach[T, …]`, which is the machine of the source's instance at `T, …`.

A recursive function in a library module takes part in recursive groups as one of the program's
does; its reports are not printed, as a library copy's are not.

**Not provided**, each rejected with a message:

- **Polymorphic recursion at types**, a member calling itself at other type arguments: the
  self-reference is at the group's own types, and the call is a type error at its argument.
  (Recursion at other lifetimes is provided, above.)
- **A group with lifetime parameters under the heap driver** (`with deep`): the machine's frames
  would hold views at the lifetimes of the calls that pushed them. Rejected with a message.
  `[spec §31]`
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
`rec-lifetimes.bc` (recursion with a lifetime parameter, generic and not), `rec-life-rounds.bc`
(a recursion over a borrowed array calling itself on a view lent at a shorter lifetime),
`rec-life-mutual.bc` (two members calling each other at shorter lifetimes and at their own),
`rec-life-cap.bc` (a group with a capability whose lifetime stays fixed while its two view
lifetimes swap at each call), `generic-pair-arg.bc`
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

`Async` is `effect Async { ctl await(); ctl log(x: i32) }`. `log` is cancellable, resumes, answers
`1` and takes closed data, so `Row.ResumeO` admits it (§29) and a `log` inside a relaxed lend is R1.

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
`clo-capture.bc`'s `'w`.

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
is linear, with a cancel branch, and the victim is held by the task that cancels it, not by the
queue; and its finaliser log `[10, 11]` is not written: the lend's finaliser is typed pure at the
empty context (R1's `· ⊢ d : Ref T ⊸ 1`, §29), and the backend does not lower a finaliser that
performs a control operation (§27 *Open*). `live 0` and `--check tags` show that both cells are
freed and the lend ends before its cell is.

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
- *Not built; §62 is the design that replaces them:* **an `imm` relaxed
  lend** (OQ-2), a fold whose algebra
  suspends under its borrow. `corpus/async-borrow.bc` is that program rewritten: the list is an
  array lent from outside the scheduler to tasks of `spawn_in`, read by index.
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
  - *its captures*: flat values only (§10's promotion), or a box at a lifetime
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
cancelled (a borrow is not consumable to run, so a cancel is safe). Two tasks given one capability
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
consume:

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
  (`Target/Wasm/Runtime.lean`). `bcc interp … -- arg…`, `bcc run <file> arg…`,
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
| `clock` | proved (7): a cell holding the time | the heap cell `run_io` makes by `mk_clock`; the time is the host's monotonic clock; assumed (1) |
| `clock_now`, `clock_sleep` | proved (7) | WASI `clock_time_get`, `poll_oneoff`; assumed (1): the real clock is not checked against the model |
| `args` | proved (7): a cell holding the arguments | the heap cell `run_io` makes by `mk_args`, over the arguments, read once; interpreter-checked (2) |
| `read_arg` | proved (7) | the arguments in memory (WASI `args_sizes_get`, `args_get`); interpreter-checked (2) |
| `mk_clock`, `take_clock`, `mk_args`, `take_args` | proved (7) | host functions, as §11's harness: a make allocates a fresh heap cell, the clock's holding the time `0`, the arguments' the stream `0xFFFFFFFF` (`mk_args` consumes its argument, a byte list, whatever it holds: the stream is the host's arguments); a take frees it (`take_clock` answers its contents, `take_args` the empty list); assumed (1), each claimed to meet its extern's contract at every call, with no condition on the run |

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
  raised back before each return and tail call (`Target/Wasm/Lower.lean`, `lowerFn`). A raise
  returns through the frame and consumes the cell with it. LLVM's counterpart is an `alloca`.
- **A suspension inside a scope.** A code that may suspend is a state machine whose state holds
  the variables live at its resumption point, and whose resume code is a new call with a frame of
  its own (§19 *Lowering*); a slot open at the point would be held in the state past its frame.
  Such a scope keeps a heap cell (`Clos.Prog.suspendedScopes`). No program has one: the typing
  refuses a resuming operation across a borrow block's body (a continuation held across a lend is
  T1, the checker's rule until surface A1, #843, for §62's shapes), and a lend in the arguments of a function that threads
  a capability. A scope between
  two suspensions is framed in each code that runs it: `corpus/async-lend-slots.bc`.
- **Capability cells are heap cells.** `stdin`, `stdout`, `stderr`, `args` and `clock` (§11,
  §34) are each allocated by a call of a harness make, which `run_io` makes, and freed by its take
  (`Backend/Clos/Convert.lean`, `mkValue`, `takeValue`; `Backend2/Convert.lean`, `mkClosOf`,
  `takeClosOf`): a fresh cell at each call meets the make's contract with no condition on the run.
  Removing these allocations is #747.
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
- A sum's boxed payload with a null-pointer niche (the tag word consumed), as Rust's `Option<Box>`.
- An owned fold over a tree still recurses natively (Backend README, *Stack*).
- Placing the objects that remain by escape analysis (stack, frame arena or heap): the scoped
  cells are placed by the elaborator's scope, not by an analysis.
- **Allocation is an effect (decision 70, #763): decided, not built.** Every heap allocation is
  written in the program (not necessarily as `box`). The heap is the outermost handler of the
  effect, a linear state handler, and arenas are nested handlers. Rows carry the effect, inferred
  as `Div` is, and it is visible in signatures. This entry introduces none of it. Until rows carry
  it, nothing downstream can read from a function's type whether it allocates.
- A buffer's growth inside `push` is an allocation the source does not write while `push` is a
  primitive. When the buffer is library code written in the language, the growth is a written
  allocation there, and `push`'s row carries the effect (#763).

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
`view 'a T` at `T = i32`) is left out of the instance (`consumePhantoms`), and its other mentions in
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
  persistent one. At a body that performs operations, which must be abortive, the load is
  `withloadU['a, 'y, A, B, [r]]` (§19 *Borrows*), `r` the operations the body performs, and the
  block's value `((), b)` for the `b` it answers (§18 *In a borrow block's body*).
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

    type Map[K, V] = ((array (1 + i32) * array K) * array V) * i32
    type MapRef[K, V]<'h, 'k, 'x> = ((array_imm 'h (1 + i32) * array_imm 'k K) * array_imm 'x V) * i32
    type Set[K] = Map[K, 1]

| function | type | |
|---|---|---|
| `map_new[K, V](cap)` | `Map[K, V]` | room for `cap` entries before it grows |
| `map_insert(&mut m, k, v)` | `V + 1` | the value displaced; a key already present keeps its first key |
| `map_lookup(&m, k)` | `V + 1` | a copy of the value (`V` persistent) |
| `map_contains(&m, k)` | `bool` | |
| `map_remove(&mut m, k)` | `V + 1` | the value taken out |
| `map_len(&m)` | `i32` | |
| `map_get(r, k)` | `imm 'x V + 1` | a view of the value, `r : MapRef[K, V]<'h, 'k, 'x>` |
| `map_entries(r)` | `sized D i32 (imm 'k K * imm 'x V)` | every entry in slot order, the key lent at `'k` and the value at `'x` |
| `map_iter(r)` | `sized D i32 (K * imm 'x V)` | every entry in slot order, the key copied out of its slot (a key that is its own view) |
| `map_fold(r, f, s)` | `S` | `f : !((imm 'k K * imm 'x V) * S => S)` over `map_entries(r)`'s entries from `s` |
| `map_drain(m)` | `sized (i32 * i32) (i32 * T) (K * V)` | consumes `m`: every entry taken out in slot order, owned |
| `map_size(r)` | `i32` | |
| `set_new[K](cap)`, `set_insert(&mut s, k)`, `set_contains(&s, k)`, `set_remove(&mut s, k)`, `set_len(&s)` | | `set_insert` answers whether `k` was new |

`r` is the map lent as a family, `borrow imm m { 'x, r -> … }` (above); while it is lent the map
cannot change, so no view outlives a growth (linearity, as §17's *No view across growth*). `D` is
the lent record's three views, `((array_imm 'h (1 + i32) * array_imm 'k K) * array_imm 'x V)`, and
`T` the owned one's, `(array (1 + i32) * array K) * array V`.

**Iteration** (#879). Each iterator is a sized iterator (§16) whose state is the slot, so a `for`
over it is counted by its data's length:

- `map_entries(r)` answers, at each occupied slot, the key's element of the keys' family
  (`array_get`, `imm 'k K`) and the value's (`imm 'x V`): any key type, owned ones included. A key
  is read through a load, `borrow imm *k { 'y, s -> … }`, whose view of a `string` is
  `array_imm 'y u8 * i32`, its text `key_prefix(s) : text 'y` (`lib/key.bc`).
- `map_iter(r)` is `map_entries(r)` with the key copied out through a load: only where the key's
  view is the key (`view 'y K = K`: an integer, a view, a pair of them).
- `map_fold(r, f, s)` is a `for` over `map_entries(r)`, as `fold_lines` of `lib/text.bc` is over
  lines.
- `map_drain(m)` takes `m`; its data is the count `(0, cap)` of slots and its state the slot and
  the owned table. Each step takes the entry at the slot out (`array_replace` with the fillers,
  the slot left empty) and answers it, or a skip at an empty slot. A loop that stops early
  (`break`, `return`, an abort) leaves the iterator's state, and with it the table and every entry
  not yet taken, to its consume (§12): the map is consumed either way, and with a consumable `K`
  and `V` every entry is.

**The order.** Every iteration visits the entries in slot order, from slot 0 up. A key's slot is a
function of its hash (deterministic, `lib/key.bc`), the table's size and the keys inserted and
removed before it, so the order is the same on every run, engine and backend for the same
sequence of insertions and removals; it is not the insertion order and not sorted.

**The table.** Open addressing with linear probing over a power-of-two table at most half full,
grown by doubling. Three arrays of the table's size: the slots, each `inl ()` or `inr h`, the
entry's slot hash; the keys; and the values, the key and the value of an entry at its slot's
index and the fillers of `K` and `V` where there is none (so `K` and `V` have a filler: integers,
views, arrays, buffers, and pairs and sums of them). Keys and values are arrays of their own so
that the map lent fieldwise lends each entry's key and value as array elements (`array_get`), at
`'k` and `'x`; a key inside a sum (`1 + (i32 * K)`) has only a load's view, at a lifetime that
cannot leave the load. Removal shifts the entries after the hole back over it, each whose probe
sequence passes it (Knuth's algorithm R), so a search never meets a tombstone. A probe compares slot hashes, then `equal` on the two keys' views. Every loop is
counted by the table's size; a search ends at an empty slot, which a half-full table has.

**Keys and values.** A key sought is given by value and consumed after the search: it is lent to
the search, a cell of the caller's frame (§35). A key may be a view (`text 't`): the map's type
then mentions `'t`, and the map cannot outlive what its keys borrow. A linear `K` or `V` makes the
map linear: it is consumable exactly when its keys and values do (§12). A replaced key is
consumed, so `K` is consumable or is persistent.

**Generic `data`.** `Map`, `MapRef` and `Set` are generic `type` abbreviations, transparent: there
are no `data` declarations (§31 *Open*), so the representation is not hidden outside the module.

### JSON: `lib/json.bc`

`include json` gives a JSON value, its parser and its serialiser, written in the language over
§36's map, §17's buffers and text, and §19's errors. The module is ordinary source: no kernel,
checker or backend change. `include json` names the module (`json` among the library modules
read at startup).

- **The value.** `data Json = Null | Bool(bool) | Int(i64) | Float(f64) | Str(string) |
  Arr(Vec[Json]) | Obj(Map[string, Json])`: owned, an array's elements in a `Vec`, an object's
  members in a `Map` keyed by an owned `string` (§42 data, §36 map). A number is chosen at parse
  time, as serde_json's `Number` is: a literal with no fraction or exponent that fits `i64` is
  `Int`, exact, except `-0`, which is `Float(-0.0)` (as serde_json reads it; an `i64` has no
  negative zero); any other number is `Float`.
- **Parsing.** `json_parse<'a>(t: text 'a) -> Json with Fail[JsonError], Exhausted` parses a
  whole document from text lent at `'a`, by recursive descent, RFC 8259's grammar:
  - every string escape; a surrogate pair decoded to one code point, a lone surrogate refused;
  - numbers by JSON's strict grammar: an integer literal that fits `i64` by `parse_i64`, exact;
    any other by `parse_f64`, correctly rounded; a number past `f64`'s range is an error;
  - the input checked as UTF-8 first; whitespace is space, tab, CR, LF only;
  - bytes after the value are an error.
- **Errors are effects.** A malformed document raises `Fail[JsonError]`, with `type JsonError =
  i32 * i32`: a code and the byte offset where it was found. Codes: 1 no value starts here; 2 not
  `,` or `]` after an element; 3 not `,` or `}` after a member; 4 not a string where a key
  belongs; 5 not `:` after a key; 6 a string not closed; 7 a bad escape; 8 a control byte in a
  string; 9 a malformed number, or one past `f64`'s range; 10 a malformed `true`, `false` or
  `null`; 11 bytes after the value; 12 the input is not UTF-8; 13 a lone surrogate. The raise
  unwinds every frame, consuming what each had built.
- **Depth.** The parser's recursion is one group under `bounded` (§20): a document nested past
  the budget performs `Exhausted`.
- **Serialising.** `json_ser<'a>(j: imm 'a Json, out: string) -> string with Exhausted` appends
  the compact form of `j` to `out`, by borrow: it lends the value and walks arrays with `elems`
  and objects with `map_entries` (§31 loads). `Int` by `push_i64`, exactly as parsed; `Float` by `push_f64` (an integral float as `3.0`);
  strings re-escaped (`"`, `\`, control bytes as `\u00XX` or their short escapes).

- **Lookup.** `json_get_with[B]<'a>(j: imm 'a Json, k: lit, f: !(all 'x < top. imm 'x Json + 1 => B))
  -> B`: `f` receives an object's member at key `k` as a view at its own block lifetime, `inr ()`
  if `j` is not an object or has no such member, and returns a result free of that lifetime. Its
  callback is written in core text, pure: the surface has no block generic in a lifetime (#1003),
  and a core-text block cannot perform (#161).

**Stated limits.**
- **Duplicate keys:** the last value wins; the earlier one is dropped.
- **Member order:** an object serialises in its map's slot order (fixed by the keys' hashes and
  the insertions, so deterministic), not the input's.
- **Numbers:** an integer literal past `i64`'s range (above 2^63 − 1 or below −2^63) is read as
  `Float`; serde_json keeps positive ones up to 2^64 − 1 exact as `u64`, which needs the `u64` width (#981); a `u64` number in `Json` waits on it. Arbitrary-precision numbers are not provided.

**Preserves.** No kernel, checker, elaborator or backend change. No existing program's output or
counts change but `corpus/json-parse.bc`'s: it becomes `include json` plus its `main`, its input
gains an id past 2^53 and `-0`/`-0.0`, its integers print exactly, and the deep case moves to
`corpus/json-deep.bc`, so its answer is `(inl (inl i32[658]), inl (inr (i32[3], i32[29])))` and its
allocations fall from 5942 to 673.

**Programs.**
- `corpus/json-parse.bc`: `include json` and its `main`; its input has `"id":
  505874924095815681`, printed back exactly, and `-0` and `-0.0`, printed as `-0.0`.
- `corpus/json-deep.bc`: twelve thousand nested arrays perform `Exhausted`.
- `corpus/parse-i64.bc`: `parse_i64` at `i64`'s minimum and maximum, an overflow, and `-0`.
- `corpus/json-get.bc`: `json_get_with` finding a member, and three misses.
- `corpus/reject/include-unknown.bc`: its list of modules ends in `json`.

**Open.**
- Streaming parse (from a reader, not a whole text) and a pull-based tokenizer (pipes).
- Number formats other than `f64`.
- Pretty printing.
- **Lookup by view.** `json_get<'a>(j: imm 'a Json, k: lit) -> imm 'a Json + 1`, a member as a
  view at `j`'s lifetime, cannot be written: a view projected inside a load (§36) cannot leave it
  at the outer lifetime, and no view can be boxed out of a borrow block (`Imm 'x _ ⊐ 'x` is
  refused). It needs a persistent reborrow in the kernel, a model extension (#999).
  `json_get_with` is today's form.

### Programs

| program | what it shows | answer | counts |
|---|---|---|---|
| `corpus/poly-operators.bc` | `(+)`, `(*)`, `(==)` at `Complex`; a generic `dot` at `i32` (the instructions) and at `Complex` (the cases) | `(32, ((-9, 12), true))` | `0 0 0` |
| `corpus/poly-providers.bc` | `equal`, `hash` and `order` at strings of two capacities, views, sums; specificity of `buf A` over `A * B`; a family of the program's | `(111, (7, -1))` | `2 0 0` |
| `corpus/map-views.bc` | views of buffer values, two at once, read through `borrow imm *v`; `map_iter`; 200 colliding keys, every third removed | `(106, (52, (133, 13267)))` | `32 0 0` |
| `corpus/map-iter-owned.bc` | `Map[string, i32]` iterated by `map_entries`, each key printed from its text view; `map_fold`; the map looked up, grown and iterated again after the lend | five lines, then `6636065` | `16 0 0` |
| `corpus/map-drain.bc` | `map_drain` of `Map[i32, string]` to its end, and stopped by `break` with three entries left, `live 0` | `91625` | `23 0 0` |
| `corpus/aoc/2024-01.bc`, `2024-11.bc`, `2022-21.bc` | #490's map days: counts, interning to indices, keys that are views of the input | the Rust answers | `9 0 0`, `276 0 0`, `18 0 0` |
| `corpus/leetcode/arrays/0001-two-sum.bc`, `0217-contains-duplicate.bc`, `strings/0049-group-anagrams.bc`, `graphs/0128-longest-consecutive-sequence.bc`, `heaps/0347-top-k-frequent-elements.bc` | a map, a set, `string` keys, `map_iter` | as their headers | `28`, `22`, `79`, `24`, `40` allocations, no indirect call or copy |

`corpus/aoc/2024-11.bc` is `-- check: no-source`: the source interpreter takes about half an
hour over it, and its golden is that interpreter's output, written once from it.

Rejected: `corpus/reject/poly-second-case.bc`, `poly-overlap.bc`, `poly-machine-case.bc`,
`poly-no-case.bc` (`equal` at a function). Still pending: `corpus/pending/aoc-2020-07.bc`, behind
#491 and #492 (with both written around, its map gives the Rust answers);
`lc-0070-climbing-stairs-memo.bc`, behind the `memo` layer (an effect with type parameters).

Each program edited from its pending form keeps its algorithm: `include map`, and `map_get(&m, k)`
read `map_lookup(&m, k)`, the copy; `0347` visits its entries with the map lent (`map_iter(r)`), and
`0049` makes a new group's key again for its insertion, since the lookup consumes the key it is given.

### Baseline

No change to `CDerives`, the relation, the machine, `PinLaw`, the checker or the backend, and no
kernel program changes (`corpus/kernel-counts.expected` unchanged). `fundamentalC`, `adequacyC`,
`fundamentalD` and `adequacyD` keep their statements and cover every elaborated program. Every
existing corpus program keeps its output, golden and counts. The table of three arrays (#879)
keeps every map program's output and golden; each allocates one array more per table, at
`map_new` and at each growth, and its loads, stores and bounds checks move with the probe, which
reads a slot's hash from an array of `1 + i32` and loads a key only when the hashes agree.

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
- **A recursive walk of what a load exposes** (`corpus/pending/data-json-map-ser.bc`): a load
  block's body (`borrow imm *j { 'y, v -> … }`) that performs an abortive operation (recursion's
  `Exhausted`, §20) is refused, "its place has no unwinding form here": the kernel's `withload`
  has its unwinding form (§19 *Borrows*), but the load form does not elaborate to it. So a borrowed
  `Json` whose objects are `Map[string, Json]` is not serialised by borrow; its entries are
  iterated (`map_entries`), but the recursion into a value is refused. An elaborator change (#879).
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
(`Target/Wasm/Lower.lean`, `floatIn`, `floatOut`), so the module uses Wasm's `f32`/`f64`
instructions. `trunc` is lowered as its range test (two float comparisons against the bounds of
Wasm's range, false at a NaN) and `trunc_sat` inside it, so the compiled code never traps. Printed,
a float value is `f32[n]`/`f64[n]`, its bits, as an integer prints its bits (`Target/Value.lean`).

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
consumed, and an operation went to the innermost handler of its *effect*. Programs worked around
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
  continuation is at the row of the `with` (`[handle]`), so the function's row is the row at the
  `with`, as the site's typing has it (§27 *The surface*).

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
  recursive groups, unwinding borrows, consume glue. The rewrite is one pass over the declarations at
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
  count, and exit status `1` (`Target/Value.lean`, `reportExit`). Every stage does the same: the source stage's model run
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
| `corpus/div-recover.bc` | `default` and `to_result` recover a zero divisor; a buffer built in a counted loop consumed by the unwind | `((i32[4], i32[4294967295]), …)` | `5 0 0` |
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

- `aoc/2024-11`: `div_u64` and `rem_u64`, which `/` and `%` (signed) would change. `aoc/2022-12`,
  `aoc/2023-03` and `aoc/2022-21`, kept here for a borrow of a buffer that an abort would cross,
  use `/` and `%` since that borrow is provided (§18), with their output and counts unchanged;
- `leetcode/matrix/0054`, `0073`, `0079`: the division is inside `cases`, a loop over the input
  with no bound, and the surface provides no handler around a div computation (§21 *Open*); the refusal is
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
the other: no Wasm quirk is carried into native code. The flat IR (`Target/Flat/Syntax.lean`)
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
- The runtime (`Target/Native/Runtime.lean`, C, trusted) is the allocator with the Wasm
  runtime's specification and algorithm, so `live` and the counts agree, and the POSIX platform
  of §11 and §34: `read`/`write` on the descriptors, unbuffered; the arguments from `argv`;
  `CLOCK_MONOTONIC` and `nanosleep`; the exit status of §39. The entry runs on a thread of a
  512 MiB stack.

### Tests

`scripts/compile-native.sh`, a step of `make gate-full` (passing with a notice when there is no C
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
- Aliasing attributes from the borrow invariants (`noalias`, `readonly`, #531) for the old
  backend; the new backend's are §50's.
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
| `x <- M`, `x : A <- M` | `x`, the value of `M`, where `x` resolves to a `let mut` variable ('do' Unchained's A4, `x ← s`); otherwise R1's new variable |
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
  inside an expression (`checkRun`); a `for`'s `else` value that writes. A control handler's body,
  which may be abandoned, hands nothing back: what it writes is lent around it (below). Koka's precedent is the escape
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
| `borrow k P { b -> S }` | `{P} ∪ W(S)` | the callback hands back `(result, W)` beside the places declared outside it that it lends; the binding rebinds `P` and `W` |
| `modify P { v -> S }` | `{P} ∪ W(S)` | the callback hands back `(c, (r, W))`, the new content `c` and the result `r` (`()` when there is none; `Sugar.modifyBody`); of a `let mut` value, the body runs in place |
| `with h(e) { S }`, answering | `W(S)` | as a borrow block of the state's cell (§18) |
| `with h(…) { S }`, control | `W(S)`, and the places `S` lends | each lent around the site, `borrow mut &mut x { 'l, x -> … }`; in `S` the name is the borrow; the binding rebinds `x` (refused for a capability) |
| `borrow k &mut x { b -> S }` | `{x} ∪ W(S)` | the lend rebinds `x`, as `modify &mut x`; `b` is a borrow of `x`'s content |
| a read of a lent `x` | `{x}` (the borrow) | bound before the computation it is in |
| `run M` | `W(M)` | `M` hands back `(value, W)` where it is bound; inside an expression, refused |
| `if …`, `match …` inside an expression | `W(M)` | read as `run M` (a call argument, an operand, a pair component, the right side of `x = …`, a field initialiser): `f(if b { 1 } else { 2 })` is `f(run if b { 1 } else { 2 })`; where it is bound it hands back `(value, W)`; inside an expression, refused when `W` is not empty, the refusal naming the construct as written |
| a closure: `{ p -> S }`, `!{ … }`, `{ S }`, `thunk`, `thunkv` and their `!` forms | `W(S)` | marked `writes(W) V` (`VSugar.writes`); at a block parameter of a call, the copy passes `W` in and out at each call; elsewhere refused |
| a `for`'s `else { d }` | — | refused when `W(d)` is not empty |
| a handler's clause | its `mut` parameters only | the state is threaded by §18 |
| a declaration (`fn`, `main`, `def`, a `poly` case) | its own `let mut`s | no `let mut` reaches another declaration |

**Places declared inside a block.** The places a borrow block or a `with` body hands back, or a
control `with` lends around its site, are the places it lends that are declared outside it. A lent name
is declared inside the block when a binder in the body declares it, at any depth of the borrow
blocks, `with` bodies and `run`s the body runs in place, and the name is not bound where the block
begins: a `let mut x` declared in an inner `with`'s body and lent there is the inner body's. A
binder of a name already bound outside (a capability rebound, `let (stdout, …) = …`) is not a
declaration, and that place stays the outer block's. R1 renames every other shadowing binder in a
program's source, so a name declared inside never stands for an outer place; core text is read by
the same rule (`bcc print` round-trips; `corpus/with-nested-lend.bc`).

### A control `with` lends what its body writes

A control handler's body (`with h(…) { S }`, `h` declared `handler h…: E, A -> R`) may be
abandoned, so it hands nothing back. Each enclosing `let mut` variable `x` that `S` writes (R2),
and each place declared outside `S` that `S` lends, is lent around the handler site, and inside
`S` the name `x` is that borrow:

    let r = with h(…) { S }     ⇒     let r = borrow mut &mut x { 'l, x -> with h(…) { S } }

nested, one lend per place, the first written outermost. In `S`, `x : mut 'l A`:

- `&mut x` at a call is a reborrow of the borrow (`withbor3`, or `withbor3U` where the call
  performs abortive operations);
- `x = e` evaluates `e` first, its reads and lends in order as below, to a value `t`; then
  `modify x { _ -> (t, ()) }`. `e` may perform the handler's operations;
- `modify x { … }`, `modify &mut x { … }` and `borrow mut x { … }` take the borrow itself;
- a read of `x` is `*&mut x`, the content copied through the borrow (`withswap`). A read
  rebinds the borrow, so it counts as a write of the borrow (R2) and every frame it is in hands
  the borrow on;
- in an expression that reads or lends a lent `x`, every read of `x` and every call (and `run`)
  in the expression is bound in the order the source evaluates them, left to right, a call's
  arguments before the call, whatever the call's arguments are, since any call may write `x`
  (through a reborrow, or a closure it is passed): A-normal form for those terms. So a read after
  such a call sees its effect: `g(&mut c) * 100 + c` and `apply(!{ u -> c = c + 7; 0 }) * 100 + c`
  both read `c` after the write, as Rust does. Only call-free subterms (operators on bound values)
  stay in place. A `while`'s condition is bound at the start of each turn,
  `loop { if c { M } else { break } }`;
- a move out of `x` (a read at a linear type) is refused: "a value can't be moved out of `x`
  here: it is lent for the body of a control handler, which may be abandoned, and its type `A` is
  linear";
- `x <- M` of a lent `x` is refused, naming `x = …`.

After the `with`, `x` holds the writes made before an abort, as in Rust: the lend ends when the
handler site answers, whether the body finished or a clause abandoned it. The lends hand the
places back where the `with` is bound, as `run` hands back what it writes; inside an expression
the `with` is refused by `run`'s rule (`checkRun`), naming it. The elaborator inserts existing
core forms, which the kernel checks: `alloc`, `withbor2` and `free` (a cell scoped to the site)
for a `let mut` value, `withbor2` of a cell, `withbor3` of a borrow (a nested control handler's).

- **Capabilities are not lent.** A body that passes on `stdin`, `stdout` or `stderr` (a cell a
  function takes and hands back, §11) is not given a borrow, which such a function cannot take.
  It is refused for the capability alone; its plain `let mut` variables are still lent. The
  message names only the capabilities, one or several: "the body of `with to_result` takes `stdout`
  and would hand it back, but a control handler's body may be abandoned: pass a capability
  outside the handler, or perform its effect inside (SPEC §41, R3)".
- **Which handlers.** The parser knows the control handlers in scope as it knows the `data` table
  (`Parser.dataIn`, `tableOf`: the prelude's, the included modules' and the program's own
  `handler … : E, A -> R` declarations). In core text (`def`, `main : C`, a printed program) a
  control handler's body hands nothing back: the lends are written around it, so `bcc print`
  reads back. What a control handler's body lends is not counted among what an enclosing block
  lends (`Val.lentNames … ctl`).
- **The general forms**, each usable on its own:
  1. `borrow mut &mut x { 'l, b -> S }` (`borrow imm &x { … }`): the place `x` lent to the block,
     the borrow chosen by `x`'s type as `&mut x` at a call chooses it: `x : ref A` gives
     `withbor2` (`withbor1`) of the cell; `x : mut 'a A` the reborrow `withbor3` (`mut` only);
     `x : A` a value a cell scoped to the block (`alloc`, the borrow, `free`, the cell's lend
     marked `lendCell`). The lend rebinds `x` (`Comp.elab`), as `modify &mut x` does.
  2. `&mut m` at a call, `m : mut 'a A`: the reborrow `withbor3` (`withbor3U` at an abortive row),
     handing `m` back.
  3. `*&mut m`, `m : mut 'a A`, `A` not linear: the content, read by `withswap` (a copy), `m`
     rebound.

  Instance inference (`Elab.Instances`) gives a lent block's binder the borrow of what `x`
  holds, and `*&mut x` the content, so `raise(x)` in a lent body infers `Fail`'s argument as it
  would outside.
- **Baselines.** No change to `Core/`, `Support/` or `Backend2/`: the fundamental property,
  adequacy and every borrow guarantee are as before, and the inserted lend is a core form the
  kernel checks. Every corpus program keeps its output and counts. Answering `with` bodies, and
  control bodies that write nothing outside, are elaborated as before.

**`if` and `match` as expressions.** The parser inserts `run M` for an `if` or `match` where a
value is expected; the kernel checks it as a written `run`. At a statement or a `let` head an
`if`/`match` is read by the computation grammar as before (`startsComp`), and juxtaposition
(`V W`) does not start at one (`startsValAtom`).

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
| `corpus/mut-control-with.bc` | a resuming handler's body that assigns | `i32[5]` |
| `corpus/mut-control-raise.bc` | `let mut`s assigned in `with to_result`, raised midway; reads through the borrow | `(inr i32[11], i32[11012])` |
| `corpus/mut-control-lend.bc` | a string buffer lent `&mut` to a bounded recursion in `on_exhausted`, its length read with `modify`, used after | `(i32[3], (i32[3], i32[4]))` |
| `corpus/mut-control-exhausted.bc` | the same where the recursion exhausts its budget: the buffer keeps the partial state | `(i32[4294967295], i32[10002])` |
| `corpus/mut-control-nested.bc` | nested control handlers writing one variable (a `withbor3` reborrow of the outer lend) | `(inr i32[110012], i32[110012])` |
| `corpus/reject/mut-control-move.bc` | a move out of a lent variable | refused, naming `buf` |
| `corpus/reject/effect-try-lend.bc` | `&mut stdout` passed on in `to_result`'s body | refused, naming `stdout` |
| `corpus/mut-control-order.bc` | reads and reborrows in source order (`g(&mut c) * 100 + c` = 108) | `(inr i32[108], (i32[101], i32[8]))` |
| `corpus/mut-control-call-order.bc` | a closure argument's write seen by a later read | `(inr i32[115], (i32[8], i32[15]))` |
| `corpus/mut-control-assign-raise.bc` | `c = chk(c + 1)`, an effectful right side, raising midway | `(inr i32[3], i32[2])` |
| `corpus/reject/mut-control-cap.bc` | a body assigning `c` and passing `stdout`: the refusal names `stdout` only | refused |
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

- **A `run` that writes inside an expression** is refused: it needs the expression's calls lifted
  in order around it.
- **Loops in a control handler's body** (`while`, `loop`, `for`): the body's type is not
  determined there ("the type of the body `h` handles is not determined here"), so the rule for a
  `while`'s condition is not exercised by a program.
- **A task's body** (`with spawn { … }`) that writes an outer `let mut`: lent around the site, the
  task outlives it, and the kernel refuses (BOXED-κ at `top`: "`c`, of type `mut 'l i32`, is used
  inside, and it cannot be shown to outlive `top`").
- **A read of a lent variable inside a closure** in the body lends from the closure, refused as
  any lend there; an `imm` lend `&x` of a lent variable (an `imm` reborrow of a `mut` borrow) is
  not provided.
- **#940: a finaliser's writes to an outer variable** are not handed back after the `with`, with
  or without the lend around the site; §42's refusal of them stands until they are.
- **Capabilities in a control body** (`corpus/pending/async-progress.bc`): §34 *Open*.
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
- **`case V { … }` and `for` as expressions** are not read as `run`: `case` is printed core, and
  `for` as a value needs its loop result bound (`let r = for …`).

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
Faces and dot (U2), abstraction (U3), codata (U4, U5), derive (U6, U7) and data unfolds (§11.1 A3)
are later units; the `fold` block (§11.1 A2) is §60's, rules F1 and F2 below.

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
Every source position carries the module it was read from: the program, written as the program's
path, or a library module `m`, written `lib/m.bc`. A diagnostic at a position inside an included
module, a parse error among them, is reported as `lib/m.bc:L:C: …`, and a span it quotes is that
module's text. Line and column numbering is unchanged, and names generated from positions use
the line and column only, so the elaborated term is unchanged.
The table holds the `type` abbreviations in scope too, read in the same pass, which the block
classification and the class `P` open (§61). Its `type` declaration is placed where the group's first member is, so a type declared later is
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
- **An array** is a recursive position with no `box` (§6.11, §61): its recursion is under the
  array's allocation. A constructor whose recursion is only under arrays and written boxes is not
  a block (`data Tree = Tip(i32) | Node(i32, array Tree)` is `μX. i32 ⊕ (i32 ⊗ array X)`), and a
  block's field may be an array of the root.
- **The class decides the positions** (§61): a declaration's recursion is accepted exactly when
  its `μ` body, each application of a non-recursive declaration opened to its structure and each
  application of a non-recursive `type` abbreviation to its body (§61), is in §6's class `P`
  (`FoldP.PB`, `pBodyB`). So the root may sit inside another type under any cell or array: a
  block's `tail: Option[List]` is the cell `ref (X ⊕ 1)`, `Vec[Option[Trie]]` is
  `array (X ⊕ 1) ⊗ i32`, `Map[string, Json]` holds it under the array of the map's values. Whether
  a constructor is a block is read the same way: `Obj(Map[string, Json])` is not one,
  `Node(Pair[T])` with `type Pair[A] = A * A` is.
- **Refused**: a field whose recursion is outside `P`, at the declaration, naming the former
  (`X` under `imm`, `mut`, a view, `!`, `[@a]` or an array of borrows; under `U` the checker
  refuses it); a recursive declaration or abbreviation around the root (a `μ` nested in a `μ`,
  U3); and a block
  constructor written without `box`, at the construction (E3).
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
| E3 | `C(…)` of a block, without `box` | refused: "`C` builds a block, one cell per field: allocate it with `box C(…)`", except in a `fold_reuse` arm (F2) | parser |
| E4 | `N { f: e, … }`, `box N { … }` | E1/E2 with the fields in declaration order; each field once, all of them; when the written order differs, the values are bound in the written order first | parser |
| E5 | `e.f` | a field of a one-constructor declaration, by the receiver's type (*Fields*) | typed |
| E6 | `x.f = e;` | `modify &mut x { r -> … }` (`x` a `let mut`), `modify x { r -> … }` otherwise: `r`'s fields bound, `e` with `x.g` read as `r`'s field `g`, the record rebuilt with `f`'s new value; the old one is consumed (§12) | parser, typed |
| M1 | `match e { p₁ -> M₁ \| … }` | a decision tree (*Match compilation*) | parser |
| M2 | `match (e₁, …, eₙ) { (p₁, …, pₙ) -> M \| … }` | M1 over the columns `e₁ … eₙ`, each bound once, no pair built | parser |
| M3 | `let p = e; N` with a constructor pattern | M1 with one arm | parser |
| M4 | the arms of M1–M3 | reports: refused when not exhaustive or when an arm is never reached | parser |
| F1 | `fold_imm e { p₁ -> M₁ \| … }`, `fold_own e { … }`, `fold_reuse e { … }` | §6's fold of the root of the group the arms' constructors name, at its `μ`'s body and the type expected of the block, applied to the algebra at `A_R`, `A′_R` or `A″_R`, whose body is M1 over its parameter with the recursive fields folded (§60) | parser (the arms), typed (the fold) |
| F2 | `C(e₁, …, eₖ)` of a block, without `box`, in a `fold_reuse` arm | the block reassembled from its cells: E1's `inj_i (e₁, (…, eₖ))`, rolled and ascribed, the kernel checking that each `eⱼ` is a cell (§60) | parser |

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
`x`, §41's R2); a persistent receiver consumes it. Elsewhere a `mut` borrow, or a variable that is
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
  is not `X` is outside §6's `FShape`, so the type has no fold and no consume (§12), and a
  program that consumes one implicitly is refused;
- a block, `box Node(…)`, is allocated cell by cell (*Open*): three objects a node.

So A7 waits for a block to be lowered as one object (N1, layouts from types): the block form is in
`FShape`, has its consume, and is then one object a node, the rule's count.

### Declared types that are not consumable (#746, L-D over L-T)

Every consume is derived (§12); the language has no written consumes. A declaration may put its type
among the linear types that are not consumable, for a value whose silent destruction is a bug: a
transaction that must be committed, a promise that must be answered, a guard that must be
released. It is no new class and no new type former: a field holds §11's `Tok`.

    data N = C(…, must_close g: A, …)            data N = { …, must_close(f) g: A, … }

`must_close` (spelling provisional) marks a field; `must_close(f)` also names the function `f` that
consumes the value, which only the error messages read: nothing calls `f` unless the program writes
the call. The rules, beside the table's:

| # | construct | elaborates to | where |
|---|---|---|---|
| D4 | a field `must_close g: A` | the field's type is `A * tok` (`Tok`, §11), in the structure, a block's cell (`ref (A * tok)`) and its shape | `Elab/Data.lean` (`structOf`, `typeDecls`) |
| E7 | a value `e` for a marked field, in `C(…)`, `box C(…)` or `N { … }` | `(e, tok_mint ())`: the constructor mints the token | `Elab/Data.lean` (`conVal`) |
| M5 | a constructor pattern's sub-pattern `p` at a marked field | `let (x, t) = o; _ <- return (tok_burn t); …`, then `p` matched against `x`: the written `match` burns the token, where the arm is reached (a variable or `_`), or before `p` is tested | `Elab/Data.lean` (`MPat.burn`, `burnBind`) |

The parser calls each of these with the table, as it calls D1–M4.

`tok_burn` is emitted at M5 only; E7 is the only `tok_mint`. A row that binds the whole value to a
variable passes it on unburned. So a declared value is consumed exactly where the program writes
a `match` on it (directly, or in the function that consumes it), and every other way it could go
is refused by a kernel fact, not by a check of the elaborator:

- **Unused at the end of its scope**: its type is not consumable (`decl_linear`), and the
  checker inserts a consume only as a `consume` node, which carries `Consumable`
  (`TDerivesP.consume_consumable`).
- **Live across a computation that may abort or cancel**: `[let]`'s `hW` asks the rest of the
  context to be `VTy.OwnFree` (§19), and a type holding `Tok` is not (`decl_not_ownFree`). The
  program is accepted when the value is consumed before, lent to a computation that handles the
  abort inside the loan, held as the state of a handler that handles the abortive operation
  itself, its clause consuming the state (`corpus/decl-handler-state.bc`), or under a `[then]`
  whose written finaliser consumes it (`finally`, below). A handler's state does not carry it
  across an abort the handler does not handle: the state is passed on at each resume, live across
  the rest of the body, which may abort (`corpus/reject/decl-handler-state-abort.bc`).
- **Lent across a computation that may abort** (`Core/DeclLend.lean`): the lend consumes the
  owner's cell `Ref N`, and the computation holds only the loan, which holds no owned cell at any
  payload (`decl_loan_ownFree`), so `hW` admits it. Where the lend ends decides the rest:
  - *the abort handled inside the loan*: the callback returns, the lend is the pure `withbor`, and
    the owner gets the value back (`d_declInside`, `declInside_runs`). At the surface, `&t` passed
    to a function whose body is the `with` (`corpus/decl-lend.bc`: commit on an answer, roll back
    on an error). A `with` whose body lends a place declared outside it, or a call whose `&`
    argument threads a capability, is refused at the surface for any type, not for this one
    (`corpus/reject/effect-try-lend.bc`, `corpus/reject/effect-lend-capability-call.bc`).
  - *the abort crossing the loan*: the lend is the unwinding form (§19 *Borrows*), whose
    finaliser `d : Ref N ⊸ 1` runs on the source when the abort ends the lend. The kernel admits
    any closed `d` of that type. One that consumes the value is derived at every payload with a
    consume (`declFinOf`: frees the cell, consumes the payload by its consume, burns the
    token; `d_declFinOf`), and the whole program runs at payload `1` (`d_declAcross`,
    `declAcross_answers`). The checker passes the
    source's consume, which `Ref N` has none of (`decl_ref_not_consumable`), and the surface
    has no form that writes `d`; so the lend is refused
    (`corpus/reject/decl-lend-abort.bc`). A written finaliser for a lend is *Open*.
- **Copied**: it is not persistent, so no split duplicates it (`Ctx.SplitP.both_live_iff`).
- **A field read that discards it** (E5's projection): `getAt` asks the discarded fields to be
  `Releasable` (§5); a field read of a record that holds one at another field consumes it.
- **Its borrow** is linear and consumable (`decl_imm_consume`, `decl_mut_consume`): a loan ends
  and the value is not consumed. `Imm̲ 'b (A ⊗ Tok) = Imm̲ 'b A ⊗ Unk`, so a view reads the fields
  and releases the token's view.

**The guarantee** is the type's linearity: a declared value is used exactly once, the checker never
copies it or inserts a consume for it, and no abort abandons it. Any function the value is passed to may
consume it with a written `match`; nothing ties a token to one consumer. Every run also ends with
every cell freed (`adequacyC`, `adequacyD`), the token's cell among them.

**The entry consumes `main`'s result by its consume.** A program with no externs whose
`main : F A` answers a value that is neither unrestricted nor a loop the driver runs is entered as
`main : F 1 = io_main_result : A <- M; return ()` (`Frontend.Check.discardEntry`): the checker
consumes the result by its consume, at a `consume` node (`entry_derives`, over `consumeSlot_derives`), and
the run ends with every cell freed (`entry_runs`, from `adequacyC`). The host never abandons a
value. At a declared type there is no consume (`entry_decl_not_consumable`), so the program is
refused: "`main`'s result is not consumed in its scope, …". A program with capabilities already
asks its result to be unrestricted (§11). `mint` allocates the token's cell at any location the
memory does not hold and `burn` frees it (`mint_step`, `burn_step`).

**A borrow's view.** A view of a marked field releases the token (`Imm̲ 'b Tok = Unk`). When a
binder's slot of a view is not used and cannot stay live where its scope ends (under `boxed[@a]`,
whose context must outlive `@a`, and `Unk` outlives nothing), the checker consumes it by its derived
consume at the head of its scope (`consumeStuck`, `consumeSlot_derives` at `Consumable.unk`); it is not owed and its
consume does nothing observable. So `t.id` reads through `imm 'a Txn` (`corpus/decl-view.bc`).

**`finally` on `with`** (user, 2026-10-30: "the syntax should be with open finally"):

    with h(…) { M } finally { D }  ≜  run (x <- (with h(…) { M }) unwind (D); _ <- D; return x)

the kernel's `[then]` (§24, §27) around the handled computation. `D : F_Σ 1` is written once and
placed twice, as the finaliser and on the normal exit, so it runs once on either; each placement is
a term the checker types, at its own row (§27). The parser reads `finally` as the sugar `fin`,
which the effects pass (§18) elaborates beside `with` (`Frontend/Elab/Effects.lean`, `goV`); it
reads `[then]`'s parts for their rows and elaborates a `with` inside them. The handled computation
and the finaliser thread no capability, so a finaliser performs no answering operation (see
*Open*); it performs control operations, resolved to the sites around the form (§27 *The
surface*). It is decision 2's "cleanup goes
in a finaliser", made readable, and not a consume: `D` is a call the program wrote. `[then]` gives `M`
and `D` disjoint contexts, so a value `D` consumes is not used in `M`: "commit in the body, roll
back on an abort" lends the value to a computation that handles the abort inside the loan and
then commits or rolls back on its answer (`corpus/decl-lend.bc`), or holds it as the state of a
handler that handles the abort and rolls back in that clause.

**A `finally` clause that assigns or lends a `let mut` declared outside the handler is refused**
(`corpus/fail/finally-assign.bc`): "a `finally` clause can't yet assign `d`, a variable declared
outside the handler: its write would be lost (#940)". A `let mut` declared inside the clause is not
affected.

**Errors name the consumer.** A value whose type holds a marked field, unused at the end of its
scope or live across an abort, is refused with one message that names the value and its type
(the declaration's name), the field that carries the obligation, and the fix: "pass it to `f`
before its scope ends" when the field names `f`, otherwise "consume it with a `match` on `N`". The
message reads the declarations (`Data.Table`); the refusal is the kernel's.

**Not this:** an implicit call of the named function at the end of a scope without a written
`finally`. That would be a consume that is not derived.

**Open (#746).**
- *I/O in a finaliser.* `[then]`'s `D` is at `F_Σ 1` beside `N` in one context: a capability the
  effects pass threads into `D` would be consumed there and not handed back, and `[then]`'s split
  `Γ₁ | Γ₂` admits no capability both `M` and `D` use (§27 *Open*, with #940's root).
- *A written finaliser for a lend the abort crosses.* The kernel's unwinding lend takes any closed
  `d : Ref N ⊸ 1` (`d_declAcross`); the checker passes only the source's consume
  (`Frontend/Check/Consts.lean`, `finaliser`), so at a declared type the lend is refused. A
  surface form would name the consumer for the unwind, say `borrow imm c { v -> S } unwind f`,
  and the checker would type `f`'s closed body at `Ref N ⊸ 1` (pure: a `lolli`) in place of
  `consumeE`. The same unit needs a lend of a record or a place at an aborting row: `borrow` takes
  only a cell or an array, and `&` in the arguments of a call that threads a capability is
  refused for any type, so `let mut t = begin(…); … raise …` stays refused with the finaliser
  alone. Not in this entry: until then, handle the abort inside the loan or use `finally`.

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
| `corpus/reject/data-field-borrow.bc` | a recursive field under a borrow, outside `P` | refused, naming the borrow |
| `corpus/data-option-block.bc` | a block whose field holds the root inside an option, `tail: Option[List]` | `i32[6]` |
| `corpus/reject/data-no-root.bc` | mutual recursion with no member on every cycle | refused |
| `corpus/data-fold-*.bc`, `corpus/fail/data-fold-*.bc`, `corpus/reject/data-fold-*.bc` | the fold block (F1, F2) | §60 |
| `corpus/decl-txn.bc` | a transaction held as a value, begun in one function and committed in another, which matches it | the committed id |
| `corpus/decl-promise.bc` | promises stored in a queue (a recursive declaration of blocks) and answered later by a `fold_own` (§60), each by a `match`; a recursion under a depth budget would abandon the rest at exhaustion, which the kernel refuses | the answers' sum |
| `corpus/decl-guard.bc` | a guard stored in a record beside data, released by a `finally` on a `with` | the guard released on the normal exit |
| `corpus/reject/decl-txn-raise.bc`, `decl-promise-raise.bc`, `decl-guard-raise.bc` | each of the three with the value live across a `raise` and no finaliser | refused: `[let]`'s `hW` (`decl_not_ownFree`) |
| `corpus/decl-view.bc` | `t.id` read through `imm 'a Txn`, the token's view consumed implicitly, the transaction committed after | i32[712] |
| `corpus/decl-lend.bc` | a transaction lent by `&t` to a function whose body is a `with to_result` around a `raise`, the loan read again after it: the abort handled inside the loan, then committed on an answer or rolled back on an error | `(i32[203], i32[7])` |
| `corpus/reject/effect-lend-capability-call.bc` | a record that is consumable lent by `&` in the arguments of a call that threads `Fail`'s capability | refused at the surface, for any type |
| `corpus/reject/decl-lend-abort.bc` | a transaction's cell lent to a borrow block whose body may raise, the abort crossing the lend | refused: the unwinding lend's finaliser is the consume, which `Ref N` has none of (`decl_ref_not_consumable`) |
| `corpus/fail/decl-burn-written.bc` | a program that takes a record apart as a tuple and writes `tok_burn` | refused by the parser: `tok`, `tok_mint` and `tok_burn` are read only in the elaboration's own source, so a printed elaboration reads back the same |

Each rule is pinned beside its elaboration written by hand (`scripts/check-sugar.sh`):
`corpus/sugar/data-forms.bc` and `data-update.bc` beside core forms, and `data-box-tree`,
`data-particles`, `data-turnstile` and `data-config` beside a surface program with no declaration
(`corpus/sugar/<name>.lowered.bc`, `-- lowers: corpus/<name>.bc`), which must erase to the same
term.

T10 has no declaration: its form as written is tuple assignment and `let (mut a, mut b)`,
`let mut` sugar outside this entry (#626, #632).

### Baseline

No change to `CDerives`, `Core/`, `Paper/`, `Support/`, the relation, the machine or the checker,
but §11's `Tok` for *Declared types that are not consumable*: the opaque kind `tok` with its relation,
`VTy.OwnFree` at the host kinds only, and the two constants `tokMint` and `tokBurn` with their
compatibility lemmas. `fundamentalC`, `adequacyC` and `adequacyD` keep their statements. No
`Paper/` or `Support/` file and no step of the machine changes: `mint` and `burn` are λs over
`alloc` and `free`.
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
  recursion over a borrowed recursive value is §6's fold, written as a `fold_imm` block (F1, §60):
  a load's view is at a lifetime shorter than the borrow's, and a group's members recurse at their
  own lifetimes (§20).
- **A generic block's construction** needs its fields' types from the arguments (`alloc(e)`): an
  injection without its type is to be ascribed.
- Field paths through several records (`d.spec.replicas = …`), update syntax `N { f: e, ..r }`,
  and variant payloads updated in place (#19).
- **A block reassembled from its cells** without `box` (typed elaboration §5.3's `Node(c₁, c₂,
  c₃)`) outside a `fold_reuse` arm: refused, asking for `box` (E3). In a `fold_reuse` arm, which
  binds the emptied cells, it is F2 (§60).
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
- **A position quoted inside a message's text** (a family's case, a loop note) renders as `L:C`
  without its module, and Backend2's driver (`Backend2/Driver.lean`) prints a front-end error
  under the program's path.

---

## 43. Entry 42 — the new backend's pure fragment: compiling the typed term (N1)

### Motivation

`docs/compiler.md` (#555) found that the backend compiles the checked term's erasure and
recomputes from it what the checker established: layouts by unification, copies and consumes from
occurrences, fixed schemes by recognisers. Unit N1 (#636, `docs/n1-plan.md`) is the new backend
of §4.2 of that design, for the programs with no effect node: it compiles `Checked.t`, the typed
term, and reads each fact from its node. The old backend stays `bcc`'s default and the
differential oracle until N6.

### Language

No change: no type, rule, term, typing, elaboration or semantics. Every program's kernel term is
the one it was, and its output.

### Lowering

`Backend2/`, the default of `bcc compile|run`, `bcc interp --stage lir|flat` and `bcc-counts`
(`--backend old` selects the old backend until it is deleted). The fragment is the programs whose typed term has no effect node
(`effPerform`, `effRaise`, `effHandle*`, `effThen`, `effLet` at a nonempty row, `effSub`,
`lendR`, `lendLoopR`, `nilDead`, the `…U` borrows, `iterate`, `divFuel`, `reify`,
`bounded_fix`): 222 corpus programs, I/O programs and codata among them. A program outside it is
refused by the new backend ("outside the pure fragment") and compiled by the old.

- **The LIR** (`Backend2/Syntax.lean`): named A-normal form whose every variable has its type,
  `LTy`, the typed term's `VTy` with lifetimes, `[@a]` and `!` erased (`Backend2/Types.lean`);
  first-order functions; closures of `lam`, `unit` and `amp` codes (a `&`'s two components share
  one environment). Every variable is consumed once on every path.
- **Closure conversion** (`Backend2/Convert.lean`) follows the derivation: at a split the masks
  `u` place the copies (a slot both parts use, persistent by `Ctx.SplitP`'s `dup`) and the consumes
  (a live slot neither part uses), and a leaf consumes its context's other live slots (`DeadP`,
  `SoloP`). No copy or consume is inferred from occurrences. A constant applied to its arguments
  (a spine of `lolliE`) is its operation; used as a value, a closure that applies it.
- **Derived nodes and constants read**: `consume A` is `A`'s consume (`consumeAt`); `array_replace`
  and `slice_replace_mut` are a slot swap, the old contents moved out and the new moved in, with
  no copy or consume (#608); `withswap` moves its contents out and back (its load's copy and its
  store's consume cancelled); `divLit` is its division with no error arm (§39); `litFn`'s bytes are
  the program's data and its table a code that reads them; `fold_own`, `fold_reuse`, `fold_imm`
  and `unfold` are functions generated from their node's shape and body; `lendCell`'s cell is a
  frame slot when its owner is freed in its function.
- **Specialisation**: a `use` node's body is converted once per key (declaration, type arguments,
  the elaborator's key) and its value's term instantiated at each later use; a body that takes a
  closure is converted at each use, so that its closures' codes are each use's.
- **The closure flow** (`Backend2/Flow.lean`), a 0-CFA run once on the LIR: a call whose function
  holds one code is a direct call.
- **Layouts from types** (`Backend2/Layout.lean`): each variable's layout is built from its type;
  the places a value moves between share one representation, so the codes that reach a closure
  place are its class, laid out as a tag and the widest environment, or on the heap when the
  class holds itself (§35); §35's one box a node; a cell is as wide as the widest type of its
  class (`Checked.cells`); an array of cells whose class holds only `i32` (or `f32`) has 4-byte
  slots, of `u8` 1-byte ones.
- **Literal views** (`Backend2/LitViews.lean`): an array tabulated from a literal's table and only
  read (lent shared, then destroyed) is the literal's bytes in the data when its length is within
  the literal's.
- **The word IR** (`Backend2/Lower.lean`) is `Target/Flat/Syntax.lean`, with
  `load32`/`store32` for 4-byte slots, and its Wasm and LLVM emitters are shared
  (`Target/Flat/Host.lean` holds what they read of a host operation).
- **Checks**: the LIR interpreter (`Backend2/Interp.lean`: consumption, copies and consumes at
  types that own no cell, cell writes, live objects) and the LIR lint (`Backend2/Lint.lean`);
  `scripts/check-backend2.sh` fences every module of `Backend2/` off the old backend (no `Backend`
  module in its imports, directly or not; what the two share is in `Target/` and `Pipeline/`) and
  every module but `Driver.lean` off the elaboration, and bans the erasure and the deleted passes'
  names.
- **The closure classes, checked** (#674, `Backend2/LayoutCheck.lean`, docs/compiler.md §10.1):
  every compile checks the layouts' and the closure flow's results, not their analyses, before
  anything reads them. A failure is the compiler's error (`internal: closure classes not a fixed
  point: …`). The layouts must be a solution of the program's constraints: every move joins its
  places, every closure reaches a class that holds its code, every code fits its class, every node
  is its type's, every box and heap class is on a cycle (§35), and the widths, boxes, heap
  classes, bytes in a cell and static cells' bytes satisfy their equations.
  The flow's sets must be a solution of the flow's constraints, and a direct call needs a set of
  one code. Read from the typed term: a cell's width class. Trusted: that the lowering reads these
  facts correctly. This is not the final state: #674 replaces the analysis (defunctionalisation in
  Core, closure types in Core, or uniform boxed closures).

### Programs

Every program of the fragment at its golden at the LIR interpreter, the word IR, Wasm and natively
(`scripts/compile-backend2.sh`), its counts pinned in `corpus/counts-backend2.expected`.

### Baseline

No change to `CDerives`, the relation, the machine, the checker, the elaboration, the old backend's
output or a kernel program. `corpus/counts.expected` and `kernel-counts.expected` unchanged.

### Open

- **Codata observations dispatch**: resolved by §45.
- **Bounds checks in a counted walk** (L-3): resolved by §46.
- **A block as one object** (§42 *Open*, A7): a block's cells are freed one by one by its type's
  consume and by a match that binds them, so one object needs a way to free an interior cell.
- The effectful programs (N2, N3), `bounded_fix`'s budget as a stack-pointer compare (NEW-b),
  pointer reversal for owned folds (B6), frame slots and LLVM attributes by rule (N5).

## 44. Entry 43 — the new backend: `Λ` erased (N1 part 2)

### Motivation

A `Λ` erases to `λ_. M` and an instantiation to `M ()` (§3). Compiled as written, every
polymorphic function is a closure whose code returns the closure of its next `Λ`, and every use
runs one call per lifetime argument before the call it is for (#636: the probe of a map's key
called two such codes per probe). The typed term says more: the body of each `Λ` the checker
builds erases to a λ-value, so an instantiation runs no code.

### Language

No change: no type, rule, term, typing, elaboration or semantics.

### The rule

- **The fact** (`Frontend/Check/Derived.lean`, `allI_inst`): for an `allI` node whose body `t`
  has `t.isLam` (`TExpr.isLam_eq`: its erasure is a λ-value), the instantiation
  `(λ_. t.erase) ()` steps by one β, at every memory (`PureSteps`), to `t.erase` with the binder's
  slot filled by `()`, a λ-value. No code runs and no memory is touched: an instantiation's value
  is the body's. `allE` and `allEV` erase to the same `M ()`, and `force` at a `∀` to its
  operand (`forceE`).
- **The lowering** (`Backend2/Types.lean`, `Backend2/Convert.lean`): `∀'x. C` is `C` in the LIR's
  types, so `U (∀'x. F A)` is `A` and `U (∀'x. C)` is `U C`; an `allI` node is its body,
  converted with the binder's slot dead; an `allE` or `allEV` node is its operand. A borrow's
  callback, `fold_imm`'s algebra and answer, and the I/O externs are at the erased types. An
  `allI` whose body is not a λ-value is outside the new backend's fragment; the checked corpus has
  none. (§63 states the fact at a body that erases to a value form.)

### Programs

Every program of the fragment at its golden at every stage; no `∀` type remains in any program's
LIR.

### Baseline

No change to `CDerives`, the relation, the machine, the checker, the elaboration, the old backend's
output or a kernel program. `corpus/counts.expected`, `kernel-counts.expected` and
`corpus/counts-backend2.expected` unchanged: the instantiations were direct calls, which no
count counts.

### Open

- The native run times of `parse` and `wordcount` are unchanged by it: LLVM had inlined the
  instantiations. The gap's cause was the counted loops' index (§46).

## 45. Entry 44 — the new backend: codata's η-thunk as a derived node, one code for literal tables (N1 part 2)

### Motivation

A loop's codata is written `f <- return (unbang (unfold[C, S] step)); …;
thunkv nu_in < (nu_out (force f s)).1, (nu_out (force f s)).2 >`, by the library and the
elaboration: `thunkv` takes only a λ, so the observation of `f s` is η-expanded. The thunk's code
and `unfold`'s observation code reach the same places, so they share a closure class and every
observation dispatched (§43 *Open*: 122 programs, 37 → about 2M indirect calls). The old backend
removed the thunk with a recogniser over its closure IR (`Collapse`), which `docs/compiler.md`
§3.6 deletes. And every string literal's table was a code of its own, so a function given two
literals dispatched on each byte it read.

### Language

No change: no type, rule, term, typing, elaboration or semantics. A program's erasure is unchanged.

### The derived node

- **`nuEta f s t`** (`TExpr.nuEta`, `scripts/pin/TExpr.tmpl.lean`), over the typed term `t` of a
  `thunkv` at a `ν` type, with the variables `f` and (optionally) `s` it observes. Its typed rule
  (`TDerivesAt.nuEta`, `TDerivesP.nuEta`) says the term's erasure is the scheme `nuEtaB f s`:
  the `&` of `f s (inj₁ ())` and `f s (inj₂ ())` (with no `s`, of `f`), each arm optionally
  binding `f` to a name of its own first (`g <- return (unbang f); …`). §65 generalises the
  scheme to an η-tree of the observations at any depth (`NuTree`). The checker builds it at
  `thunkv` when the erasure is the scheme (`rNuEta`, `nuEtaOf?`, `Frontend/Check/Rules.lean`);
  the node is kept by moving the term's variables (`nuEtaB_shift`, `TExpr.shift`).
- **The fact** (`Frontend/Check/Derived.lean`): the thunk's observations are `f s`'s, by pure
  steps (`nuEta_obs`); with no state, `f`'s (`nuEta_var`); and at `f = unfold step` (`hN C g`,
  the value `unfold step` steps to), every observation reaches the same observation of
  `etaN C g s`, which `f s` steps to by one β at every memory (`nuEta_unfold`, from `hN_steps`).
  So the codata may be computed where the thunk is built.
- **The lowering** (`Backend2/Convert.lean`): a `nuEta` node with no state is its variable; with
  a state, when `f` is a variable a `bind` bound to the `unfoldN` constant applied to a step
  (`isUnfoldApp`, read from the `bind` node's value; followed through copies and captures), it
  is the call `f s`, made there. The codata of a loop is then only `unfold`'s code, and each
  observation a direct call. Any other `nuEta` node is compiled as its thunk.

### Literal tables

Every literal's table is a closure of one code over its offset and length in the data
(`litCode`, `Op.litByte`), so the tables of a program are one class of one code;
`tabLit` reads the literal's offset and length from that closure's environment.

### Programs

Every program of the fragment at its golden at every stage; each program's `indirect` at most
the old backend's (37 in all, equal on every program).

### Baseline

No change to `CDerives`, the relation, the machine, the elaboration, the old backend's output or a
kernel program, or any program's erasure. `corpus/counts.expected` and `kernel-counts.expected`
unchanged.

### Open

- A `nuEta` node whose `f` is not bound to `unfold step` where it is built (a parameter) is
  compiled as its thunk.

## 46. Entry 45 — a counted walk's read in range: the typed fact (N1 part 2, L-3)

### Motivation

A `for` over a view is a counted walk (`TExpr.walk`, §16): `count_try` or `count_fold` over the
view's length, whose step reads the view at the counter. The walk node fixed only that its term is
a counted loop; that the step reads, at its index, the view the bound was taken from was the
elaboration's (§43 *Open*), so every read kept its bounds check. This entry puts that fact on the
typed term.

### Language

No change to any type, rule, typing or semantics. The elaboration of a walk over a shared view
changes shape, not meaning: the view's copy and its length are taken inside the walk's marked
value, `run (let (v, c) = array_copy v₀; return count (step, (array_len c, (0, (v, …)))))`, where
they were bound before it; and the step's read is marked.

### The typed fact

- **`walk m read t`** gains `read`: its typed rule (`TDerivesAt.walk`, `TDerivesP.walk`) has the
  premise `read = true → walkReadB m t.erase = true`. `walkReadB`
  (`scripts/pin/TExpr.tmpl.lean`) reads the term as its binders see it (`normAt`, so that the
  fact is kept by moving variables: `walkReadB_shift`). At a shared view it fixes that the loop is
  `let (v, c) = array_copy v₀; count (λq. S, (len c, (i, s)))`, the bound the view's length and
  `s`'s first component the view; that the step `S` takes its argument apart, copies the view and
  reads the copy at the counter (`walkStepB`); and that every tail of each arm hands the copy's
  view on as its state's first component (`walkTailsB`). At a unique view it fixes that the step
  splits one element off the view and reads that head at `0`.
- **`walkGet m t`**, a derived node over the read the elaboration marks
  (`Frontend.SchemeMark.walkGet`), its rule `walkGetB m t.erase`: `array_get (g, i)`, or
  `slice_get_mut (h, 0)`. The checker sets `read` when `walkReadB` holds and the walk's term holds
  one `walkGet` outside the walks inside it (`rMarked`, `walkGets`).
- **The lemmas** (`Frontend/Check/Derived.lean`): the bound is the view's length
  (`walk_copy_len`); the step runs only below the bound (`walk_index_lt`, `walk_fold_index_lt`);
  below it a shared view's read answers its leaf (`walk_get_leaf`); the head of a split by one is
  read in range whatever the view (`walk_get_split`).
- **The lowering** (`Backend2/Convert.lean`): inside a walk with `read`, a `walkGet` node's read
  is `idx` with no test.

### The counted loops' index

The loops the new backend generates (`count_fold`, `count_try`, `array_new`'s, `array_free`'s, an
array's consume) run their index `i` below a bound under `2³¹` (`arrLen`, `clampLen`), and
step it only after `i < n`. Both are `i32`s held zero-extended, so the test is a word compare and
the step a word add that does not wrap (`Op.cntLt`, `Op.cntSucc`), where they were the 32-bit
host operations with their truncations. This is the cause of the gap §44's measurement left:
with it `parse` runs at the old backend's time (153 ms against 153 ms, Rust 127 ms) and
`wordcount` within 4% of it (132 ms against 127 ms, Rust 104 ms), native, median of 11.

### Programs

Every program of the fragment at its golden at every stage. The 33 programs of the fragment with
a walk have no test at the walk's read; their bounds column goes down
(`corpus/counts-backend2.expected`).

### Baseline

No change to `CDerives`, the relation, the machine or a kernel program. Every output, golden and
exit status unchanged. The old backend's counts are unchanged except `data-config`'s loads and
stores, which go down (209 → 161, 49 → 25): the walk's copy and length inside its value.

### Open

- That a tail handing on the view's variable hands on its value in every run is fixed of the
  term (`walkTailsB`), not proved of the runs: a lemma over the step's reduction would pin it.
- At a unique view the split's own test stays: its range needs the view's length at step `i`,
  `n − i`, which the same lemma over the step would give.
- That the read the step makes is the one its `walkGet` node marks is the elaboration's mark,
  counted by the checker.

---

## 47. Entry 46 — the new backend: effect erasure by handler law (N2)

### Motivation

`docs/compiler.md` §3.2 (#552) erases effects by handler laws applied at known sites, each rule
reading its applicability from the typed term. Unit N2 (#647) builds the rules in the new backend
(§43) for the clause kinds whose laws Core has: abortive operations and tail-resumptive clauses.
Every program the new backend compiles has no `handle` and no `perform` left: an operation is a
direct call, an abort a branch to its handler's join, and nothing is captured.

### Language

No change: no type, rule, term, typing, elaboration or semantics.

### Lowering

`Backend2/`. Each rule reads the node's fields and the checker's facts; none recognises a term.

- **Rows in the LIR's types** (`Backend2/Types.lean`, `ofC`): `F_Σ R` is `R ⊕ P`, `P` the payload
  of `Σ`'s abortive operations (answer `0` at a cancellable or unrestricted qualifier,
  `OpSig.abort`): their
  argument types, one summand per operation, each key once, in the row's order (`payOf`); with no
  abortive operation it is `R`. A non-abortive operation has no run-time content in the type.
  `Div`'s operations stay outside the fragment (N4).
- **`raise`** (`effRaise`): the payload at its operation's summand, `inr`: a jump to the handler's
  join (`catch_abort`; frames that catch nothing of its name are passed, `abort_absorbs`).
- **`[let]` at a row** (`effLet`): `N` on `inl`, the abort handed on and `N`'s context consumed
  (`effLet`'s `hW`: it holds no own cell), the branch per call of §19 (`abort_to`, `abort_passes`).
- **`[sub]`** (`effSub`): the payload of `Σ` re-injected at `Σ'`'s summands (`RowLe`).
- **`[then]`** (`effThen`): `N` on a value; on an abort the finaliser `D`, then the abort, or the
  finaliser's own, which supersedes it, handed on (`then_ret`, `then_fin`, `unwind_prefix`).
- **The unwinding borrows** (`withbor1U`, `withbor2U`, `withbor3U`, `withloadU`, `sliceBorrowMU`,
  `sliceBorrowIU`; `withborUE d`): the lend as §43's; the callback's abort ends it, runs the
  finaliser `d` on the owner and is handed on (`then_fin`). A finaliser that is not a constant is
  outside the fragment.
- **`[handle]`** (`effHandleV`, `effHandleVB`), read from the node: its name `n`, its operations
  `E`, its clauses' kinds `ks` (§19 *Clause kinds*, `classifyHandler_sound`), its outer row `Σ`,
  the masks, and the clauses of its pair written in place. Every clause must be `abortive`, or
  `tail` with its direct call licensed (below); any other kind leaves the program outside the
  fragment. The handled computation runs in place; a value goes to `h_ret` (`catch_ret`), an abort
  of `n`'s operation `j` to clause `j` (`catch_abort`), an abort of `Σ`'s handed on (`fwd_abort`).
- **A direct call** (`effPerform`). At a static name, the facts license operation `j`'s direct
  call when every `handle` node of the name (`Backend2/Driver.lean`, `directFacts`)
  - classifies the clause `tail` (`ks`), so its body `M` resumes on every path in tail position
    and uses `κ` nowhere else (`TailResumesAt 0 M M'`, `TailResumesAt.subst_kappa`,
    `TailResumesAt.kappa_free`);
  - holds names of the clause's own code (`handlerNames`, its row's where it has none) that `main`'s
    flow record cannot catch (`cond2B` at `Checked.flows`): no frame between a `perform` and its
    handler catches them (`Checked.unhandledNames`, `tail_clause_names`);
  - holds one closed clause for it (`closedAt 0` of the node's clause), at one outer row and one
    signature, so the clause a `perform` reaches is the same code at every node and needs nothing
    from its handler's frame.

  The clause's work `M'` (`M` with each resume `κ.1 y` replaced by `y`, read along the paths of
  `TailResumesAt` through `[⊕E]`, `[⊗E]`, `[1E]`, `[let]` and `[sub]`, the right unit and the
  alias of `κ` included) is one function, made before the conversion (a `perform` may stand in a
  function made before its handler). A `perform` of the operation calls it on the argument
  (`tail_resumes`: the clause runs as its work followed by one resume, which `kappa_resume_steps`
  takes back into `K`); its aborts, at the outer row's payload, are re-injected at the `perform`'s
  row, and a `perform` at a row that does not hold them is outside the fragment.
- **`main`'s exit status** (§39): when `main` is served `Fail[DivError]` by the platform's handler
  (`Checked.exitsOnDivError`), its value `inl v` reports `v` and `inr ()` ends the run with the
  status `1`, at the LIR interpreter, the word IR and both targets.

### The postcondition

The LIR has no `handle` and no `perform` former, so a program the new backend compiles has none
left. `bcc lir --erasure` prints, for a compiled program, the `handle`, `perform` and `raise` nodes
the conversion erased (each `use` body once per key), and, for any program, the `handle` nodes left
for the state machines (a clause of kind `once` or `stored`, the stored-continuation sites) and
those left by a rule this entry does not build. `scripts/compile-backend2.sh` requires `left 0 0`
of every program it compiles and pins the line in `corpus/erasure-backend2.expected`.

### Programs

272 corpus programs at their goldens at the LIR interpreter, the word IR, Wasm and natively, 50 of
them effectful: every one whose handlers are abortive or directly called and that has no
`bounded_fix` (N4). Their counts are pinned in `corpus/counts-backend2.expected`, with no indirect
call; the 222 programs of §43 keep their counts.

### Baseline

No change to `CDerives`, the relation, the machine, `Core/`, the checker, the elaboration, the old
backend (still `bcc`'s default) or a kernel program. `corpus/counts.expected` and
`kernel-counts.expected` unchanged.

### Open

- **`tail+state`** (§19 *Handler state*): the clause answers the state-passing function, and the
  `handle` node's value is that function, applied to the initial state by the code after the node.
  The rewrite that keeps the state in a cell (`handle_fold` for the `hnd` encoding) needs the
  initial state at the node, and that the clause's work after its resume is a value, so that the
  continuation's segment and that work commute. Neither is a fact of the typed term; the programs
  stay with the old backend.
- **`resume-or-cancel`**: the cancel in place runs the region's finalisers under §19 *Cancels*
  (the region's handlers dead, the first finaliser error kept) and then the clause's rest. Its
  representation, a summand of the operation in the payload of every row that holds it, depends on
  the clause's kind, which the rows do not carry; not built.
- A tail-resumptive clause that captures values, or that differs between the nodes of its name:
  its direct call needs its captures at the `perform` (evidence), as §19 *Open* says.
- `once` and `stored` clauses (N3); `bounded_fix`, `count_try`'s exits, `unfold`/`drive` as loops and `tick`
  (N4).

## 48. Entry 47 — the new backend: `bounded_fix` as its machine step (N4, loop part)

### Motivation

Unit N4 (`docs/compiler.md` §6.1, #652) compiles the loop forms the elaboration produces as LIR
loops. On this baseline those are `count_try` (§16), `unfold` with its drive (§7, §11, §14) and
`bounded_fix` (§20). The first two have been compiled by the new backend since §43 and §45:
`count_try` is a native loop whose exit `inr e` leaves it, `unfold` a code of observations, and the
runtime's drive of `main`'s loop a self tail call. After §47, the one loop node that no rule
compiled was `bounded_fix`. It stopped 48 programs, and 44 of them have no other node outside the
fragment. This entry compiles it from its machine step.

### Language

No change: no type, rule, term, typing, elaboration or semantics.

### Lowering

`Backend2/`. The rule reads the node's type and nothing else.

- **`bounded_fix (s, (k, a))`** (`boundedFix`, read at its spine; `genFix`): the head step
  `Head.boundedFix` (§20; `boundedFixNext`, `fixSelf`), `s` run on `(self_k, a)` with
  `self_0 = inl ()` and `self_{j+1} = inr (λx. bounded_fix (s, (j, x)))`. It becomes one function
  per node, `bounded_fix(s, k, a)`. The function tests `0 < k` with the budget read unsigned
  (`cntLt`, as §16's counter), builds the self-reference and calls `s` on `(self, a)`. The
  self-reference at `j + 1` is a closure of its own code over `s` and `j`, where `j` is `k − 1`
  (`Op.cntPred`: the budget is not `0` there, so it does not wrap). The code's one function is
  `bounded_fix(s, j, x)` again. The step type `(1 ⊕ U(A ⊸ C)) ⊗ A ⊸ C` gives the LIR types of the
  self-reference and its code. A `selfCall` (§21) is a call of that closure, which the 0-CFA makes
  direct. So a step that calls itself in tail position is a loop of tail calls with its budget,
  and one that calls it elsewhere is a native recursion bounded by it (§20's `bounded`).
- **`Op.cntPred`**: `k − 1` of a word that is not `0`, at the LIR interpreter, the word IR, Wasm
  and natively.

No rule here reads `Div`, `tick`, `iterate`, `div_fuel` or `reify`. The elaboration produces none
of them yet (they are §14's kernel `Div`, elaborated by the `Div` work parked on #646), so they
stay outside the fragment.

### The law for the runtime's drive of `reify`

`Core/DivDrive.lean` proves the steps of the runtime's drive of a loop written as
`reify_res t`. A segment that reaches a tick is resumed with *next* in place
(`drive_reify_tick`, from `reify_seg_tick` and `reify_next_resumes`). A segment that ends with
`inl b` ends the drive with `inl b` (`drive_reify_done`). One that ends with `inr r` leaves a
loop that every observation skips, so the drive does not finish (`drive_reify_closed`). The first
segment has its own lemmas (`reify_start`, `reify_first_tick`, `reify_first_done`,
`drive_first_tick`, `drive_first_done`). These lemmas are over Core's existing `reify`, `driveE`
and machine, and their axioms are within the standard three (`scripts/AxiomCheck.lean`). This is
the law a rule running such a loop in place will read once the elaboration produces `reify`; no
rule of the new backend reads it yet.

### Programs

316 corpus programs at their goldens at the LIR interpreter, the word IR, Wasm and natively (272
before). The 44 new ones are every program whose only node outside the fragment was
`bounded_fix`. Each has `indirect 0`, and their counts and erasure lines are pinned in
`corpus/counts-backend2.expected` and `corpus/erasure-backend2.expected`. Their allocations
equal the old backend's except in four programs (`list-generic` 32/27, `parse-recover` 259/246,
`rec-generic-mutual` 11/8, `rec-parser` 22/17). Those are the boxed `μ` fields of §43's layouts
(§35), the same difference §47 reported for `effects-fail-list`; `genFix` allocates nothing. The
272 earlier programs keep their counts.

The 64 still outside the fragment are N3 (`stored` or `once` clauses, and a `perform` with no
direct call), `tail+state`, `resume-or-cancel`, or a tail clause whose direct call is not licensed
(§47 *Open*).

### Baseline

No change to `CDerives`, the relation, the machine, the checker, the elaboration, the old backend
(still `bcc`'s default) or a kernel program. `Core/` gains `Core/DivDrive.lean`: lemmas over
existing definitions, with no rule. `bcc compile --backend new --timings` prints the new
backend's stages; the gate's compile-time guard is unchanged. `corpus/counts.expected` and
`kernel-counts.expected` are unchanged.

### Open

- **A loop that may diverge runs one turn per observation.** On this baseline a div body is one
  state machine (§14, *One state machine per body*). A callee's loop that a body runs in direct
  style is a state of the caller's machine, so the runtime advances the innermost loop one
  observation at a time through every enclosing machine. The new backend compiles each machine's
  `unfold` and the drive as given. A native loop per source loop needs a node per loop (§14's
  `iterate` under the runtime, which reads `Core/DivDrive.lean`). A rule that drove an inner
  loop in place from the shape of its caller's step would be a recogniser. `bench/sieve` runs at
  about 4.2× Rust for this reason.
- **`div_fuel`'s counter test**: the checker has no producer of `divFuel`, so the rule is not
  built.
- A `selfCall`'s fact (§21) is not read: the call is direct by the 0-CFA, not by the node.

## 49. Entry 48 — the new backend: state machines at stored-continuation sites (N3)

### Motivation

Unit N3 (`docs/compiler.md` §6.1, #657) compiles the `handle` nodes that §47's rules leave: a
clause that keeps `κ` (`stored`: a stored generator, a task), resumes it before it answers
(`once`), resumes or cancels it (`resume-or-cancel`, the decided RC-0 of #647), keeps a state
(`tail+state`), or is tail-resumptive at a node whose direct call the facts do not license. After
§48 these left 64 programs outside the new backend. Each is now a state machine, as §19
*Lowering* describes the old backend's, built on the typed term: the state at a resumption point
is its live variables at their types, a suspended computation is one code per machine, and a task
body is one code.

### Language

No change: no type, rule, term, typing, elaboration or semantics.

### Lowering

`Backend2/`, read from the typed term and from the layouts of the LIR it converts to.

- **Machine operations** (`Backend2/Driver.lean`, `machineOps`): each control operation `(n, j)`
  whose clause at some `handle` node of `n` is neither `abortive` nor `tail` with its direct call
  licensed (§47, `directFacts`), read off the nodes' kinds (`ks`, `classifyHandler_sound`).
  Every other operation is lowered by §47.
- **The outcome** (`Backend2/Types.lean`, `outcomeTy`): `F_Σ R` at a row with machine operations
  answers `μY. R ⊕ (P ⊕ S)`, `P` the payload of `Σ`'s abortive operations (§47) and `S` one
  summand per machine operation `A ↠ B` of `Σ`, in the row's order: its argument and the
  suspended computation `k : U((B ⊸ F Y) & K)`. At a capturable (cancellable) operation (`capB`),
  `K = F C`, `C` what its cancel answers, `1 ⊕` the payload of the operation's cancel row (`fin`,
  §27; `1` at `⊤`). At a must-resume operation `K = ⊤`: the kernel never cancels a `lin`
  continuation (`kTy .lin`, `kappaC_cancel_lin`), so Backend2 builds no cancel entry there, only
  an `unreachable` trap, which no run reaches; that it is never entered is stated `UNPROVED:` at
  `genMach`. `k` is the continuation `[op]` captures, as §19's `κ` is: its first component resumes
  it, its second cancels it.
- **A machine** (`convK`) is a function whose answer is an outcome, with the joins and steps its
  conversion makes. A computation is converted with its continuation inside the machine (the
  frames to the machine's answer): a `[let]` or `[then]` at an outcome makes its body a join and
  pushes its frame, so the frames of a resumption point are flat in the machine's state, never
  nested; the arms of a `case`, `(λx. N) V` and a premise that cannot suspend take the frames in
  place. At a node:
  - `perform` of a machine operation suspends the machine (`performK`): its state the frames'
    variables, its `k` the machine's own (`[op]`);
  - `raise` unwinds the frames: each `[then]`'s finaliser runs, its own abort superseding
    (`then_fin`, `unwind_prefix`), then the machine answers the abort (`catch_abort` at its
    drive);
  - any other computation at an outcome (a call, a drive) is a **call point** (`pointK`): its
    outcome is taken apart by a step, its value to the frames, its abort through them, its
    suspension a suspension of the machine whose state holds the callee's `k` and the frames'
    variables. Suspension through calls nests (§19 *Lowering*).
- **The machine's codes** (`genMach`), per operation: the state, one variant per point of the
  operation; the `&` code of `k` over it, whose resume entry switches on the state and continues
  at the point (a call point resumes its callee's `k` and steps again; `kappa_resume_steps`), and
  whose cancel entry cancels the callee's `k` first, then runs the point's frames' finalisers
  innermost first, keeping the first error (§19 *Cancels*, `[cfin-raise]`, `cancel_prefix`,
  `kappa_cancel_steps`). A finaliser that may suspend, and a cancel row with a machine operation,
  are lowered by §69.
- **A `handle` node as a drive** (`convDrive`), when its handled computation's row has a machine
  operation (of its own name, or of `Σ`). The handled computation is a machine of its own. The
  drive takes its outcome apart, read from the node: a value to `h_ret` (`[ret]`, `catch_ret`), an
  abort of one of the node's operations to its clause (`catch_abort`), one of `Σ`'s outward
  (`fwd_abort`); a suspension at operation `j` of the node runs clause `j` on the argument and
  `κ` (`[op]`), `κ` at the node's qualifier (`kTy`, `cancelTy` at `fs j`): a closure over the
  handled computation's `k` and the handler's values, whose resume entry resumes `k` and drives
  its outcome again (the handler is deep, `[op]`'s `hnd (n, H) K[y]`), and whose cancel entry
  cancels `k`, every frame of the region unwound and no clause of its handlers run (the region's
  handlers are dead, §19 *Cancels*). A must-resume `κ`'s cancel branch is `⊤` and never run. A
  suspension at one of `Σ`'s machine operations suspends the drive (forwarding): resumed, it
  resumes `k` and drives again. The clauses run in the drive's machine.
- **Frame access by evidence (E, #647).** The handler's frame is what the node's clauses capture
  and its own context's parts. They are the drive's parameters, and `κ`'s environment holds them:
  a stored `κ` is resumed after the node's activation has ended, so its evidence is carried with
  it as values, as the machine's `κ` holds `H`. No machine reads a handler's frame otherwise: a
  suspension returns to its drive. No global slot per name (G) is used.
- **Tail calls.** A call in tail position at the machine's own outcome is a point, so a machine's
  `k` is one code. A machine whose only point is one such call passes its callee's outcome on (a
  wrapper). A call whose callee's suspended computations may be the machine's own (the layouts'
  class of the callee's `k` holds one of the machine's codes: a recursion's next turn through
  `bounded_fix`'s self-reference, §48; a drive's clause resuming `κ` in tail position) closes a
  loop of tail calls and passes its outcome on (`tailPass`): such a loop runs in constant space.
- **State cells.** A machine operation whose `k`'s class holds itself (the layouts' recursive
  classes, §35: a recursion through a resumption point, a clause that resumes `κ` before it
  answers) keeps its state in a cell (`cellPass`), allocated when the machine first suspends
  there and written in place each time it suspends again at the operation (`Op.release` frees it
  when it does not); its `k` is then a word. One object per level of a recursion, as Rust's
  `Box::pin`. At `unr` the state stays in the environment, since that `κ` may be copied.
- **One code per task body.** The closures of the handler's answer type that a stored-continuation
  site's clauses build (a task's or stored generator's value: finished, or pending on `κ`), and
  the closure whose observation runs the site (a stored generator before its first observation),
  are variants of one code (`genMerges`), keyed by the site's handler (`HSite.handler`) and its
  handled computation's task body: the keys of the `def`s it uses (`use` nodes, `DefKey.body`,
  which copies of one `def` at several sites share). A value of the closure type is then one code,
  as a coroutine of one body is one type. Tasks of different bodies in one queue keep their
  codes, and a resume dispatches among them (class (a) of `docs/effect-lowering.md` §1.4, as
  Rust's `dyn Future`).
- **Work at a machine row.** A tail-resumptive clause called where it is performed (§47) whose
  handler's outer row has a machine operation is a machine of its own (`convWorkK`), its resumes
  its answer, and the `perform` a call point of it.
- **`lendR`** (§29): the unwinding borrow at a resuming row, converted in its machine: the owner
  lent as the callback's view, `(r, b)` at the callback's value, the owner's finaliser `d` at a
  cancel inside the callback. The owner's cell stays where it is, and the machine's state holds
  its location (§29 *Lowering*). `nilDead` is its term at the empty context.

### The postcondition

The LIR has no `handle` and no `perform` former. `bcc lir --erasure` prints, for a program with
machines, `machines M suspends P` after §47's counts: the `handle` nodes converted as drives and
the `perform`s converted as suspensions (each `use` body once per key), then `left 0 0`.
`scripts/compile-backend2.sh` pins the line in `corpus/erasure-backend2.expected`.

### Facts read

The nodes' clause kinds and qualifiers (`ks`, `E`), the direct calls' facts (`directFacts`), each
row's operations with their signatures and cancel rows (`OpSig.fin`), the handler's answer type
`R`, `HSite.handler`, and the `use` keys of a handled computation; and, after conversion, the
layouts' closure classes (§35) for the tail calls and the state cells. Nothing is recognised from
a term's shape.

### Programs

380 corpus programs at their goldens at the LIR interpreter, the word IR, Wasm and natively (316
before): the 64 programs that §48 left outside, among them every async and generator program, the
RC-0 programs (`async-r1-cancel-finaliser-writes`, `capture-take-hand`, `core-yield-loop`,
`state-machine`, `div-infer`, `effects-cancel-two-sites`,
`leetcode/trees/0230-kth-smallest-element-in-a-bst`) and the `tail+state` programs
(`hygiene-handler-state`, `answers-two-types`, `clause-captures`, `reconcile-clock`). Their
counts and erasure lines are pinned; the 316 earlier programs keep theirs.

Against the old backend (`corpus/counts.expected`): `indirect` falls to 0 in every class-(c)
program of `docs/effect-lowering.md` §1.4 but the seven with a handler state (`answers-two-types`
2, `clause-captures` 3, `div-infer` 4, `effects-cancel-two-sites` 4, `hygiene-handler-state` 2,
`reconcile-chain` 3, `reconcile-clock` 8, as the old backend's: the state-passing answer's
dispatch, §19 *Handler state*; `binder-copies`, whose `two(base)` is such a handler, keeps its 2
too), and stays at the old backend's in class (a) (`async-timers` 5,
`io-task` 7, `sched-a-div` 5, `sched-a` 18, `sched-b` 18). `allocs` is no higher except in
`rec-emit` (16 against 6): a level's state cell is allocated again after each of its own
`perform`s, where the old backend kept one object per level.

### Baseline

No change to `CDerives`, the relation, the machine, `Core/`, the checker, the elaboration, the
old backend (still `bcc`'s default) or a kernel program. `corpus/counts.expected` and
`kernel-counts.expected` are unchanged. The LIR gains `Op.release` (a cell freed whose contents
were taken), at the LIR interpreter, the word IR, Wasm and natively.

### Open

- The `tail+state` and `resume-or-cancel` direct rules (#647, `hnd_state_cell`,
  `resume_or_cancel_direct`): the handler-state programs above compile as machines, with the old
  backend's dispatches; their rules would make them zero cost.
- A level's state cell passed on to the machine's next point, so that a recursion's levels keep
  one object each across their own suspensions (`rec-emit`): built in §50.
- A loop that may diverge (§14's one machine per body): `chain-yield` stays at the old backend's
  time until `iterate` (B2, parked).
- An evidence slot for the direct-call rules (E's slot for `tail+state` and RC-3): N3's drives
  carry the handler's values with `κ` and need none.

---

## 50. Entry 49 — the new backend: target facts (N5)

### Motivation

Unit N5 (`docs/compiler.md` §6.1, #661) gives the native target what the checker establishes
about addresses, which §40 left out: every word an `i64` and every address `inttoptr` of integer
arithmetic, no attribute on any parameter (§40 *Not provided*), and so no vectorised loop over an
array (#537 fix 5). It also carries two items N3 left (§49 *Open*): a level's state cell passed
on to its machine's next point, and an aggregate `phi` LLVM does not thread (sieve).

Everything here is backend: no change to the language, `CDerives`, the relation, `Core/`, the
checker or the old backend's output. `bcc` gains `--no-facts` (the native build without the
facts), `bcc lir --frames` and `bcc-counts --frames`.

### Lowering

- **Typed pointers.** Which words of a value hold an address is read off its layout node, which
  is its type (§35, `Backend2/Lower.lean`, `addrKinds`): a cell's or a borrow's word, a family's
  base and a boxed field's pointer do; a sum's payload word does where its arms agree (padding
  agrees with either); a closure's captured word where its class's codes agree; a heap class's
  word (`2t + 1` or an address) does not. A local is a pointer when every variable's layout that
  places it says so (`Fn.ptrs`). The word IR's address arithmetic is `Exp.gep base off`, a word
  `base + off` in Wasm and at the word IR's interpreter. Natively (the emitter's typed mode, the
  new backend's only) a pointer local is a `ptr`, an address is a `getelementptr` from its base,
  the frame's slots and the data are `getelementptr`s of their `alloca` and global, and a
  parameter is a `ptr` where every function of its tail-call class holds an address there
  (`classPtrs`), since `musttail` asks a class's prototypes to agree. `inttoptr` and `ptrtoint`
  are left where an address passes through a word that is not one everywhere: a mixed sum's
  payload, a heap class's word, a result.
- **Facts.** Each parameter word's facts are read off the parameter's type (its `LTy`; a layout
  node may be shared by an owner and its borrows, so a node's shape does not give the mode), and
  emitted as LLVM attributes where the parameter is a `ptr`, each cited in a comment above the
  definition:

  | parameter word | attributes | the guarantee it cites |
  |---|---|---|
  | a `mut` borrow of a cell with words | `noalias nonnull dereferenceable(b)` | a `mut` lend is unique: `●` is defined where `▶◀` holds (`CellU.CompS.compat`) and `▶◀` relates `imm` cells only (`CellU.CompatS.kinds`, `Support/Model/Composition.lean`); a live borrow points at a live cell: no run is stuck (`adequacyD`; `adequacyD_pin` under `PinLaw` at a relaxed lend, as `bcc trusted`'s typing line reports; `externs_every_run` or `io_every_run` with externs, §13), so a load through it succeeds, and the cell was allocated at its width class's widest bytes (`WidthClass`, `bcc trusted`) |
  | an `imm` borrow of a cell with words | `noalias readonly nonnull dereferenceable(b)` | an `imm` lend is not written while live: `▶◀` relates `imm` cells at one value (`CellU.CompatS`), and the LIR's writes (`put`, `swap`, `slotPut`, `replace`) take a `mut` borrow or the owner; a live borrow points at a live cell, as above |
  | the base of a borrowed family | `noalias`, and `readonly` at `imm` leaves | its leaves' mode, as above; the base is `0` for an empty family or in the program's data, so it is neither `nonnull` nor `dereferenceable` |

  `b` is the cell's bytes (its class's widest, §35), which rests on the width-class assumption
  marked UNPROVED at `Low`'s `.alloc` (`WidthClass`, listed by `bcc trusted`). A cell of no words
  (its borrow is `0`) gets none. A pair's fields are its words in order; a sum's depend on its
  arm and get none. These attributes are **informational, relied on for now, improvement
  candidates** (*Improvement candidates* below): LLVM may use them and is not made to, and what
  a target or count gains from them is to be moved into our compiler or forced where gains remain
  (`docs/compiler.md` choice 6; measured in `docs/scope/760-native-facts.md` §7).
- **The lend encloses the function.** The kernel's facts hold while the lend is live; LLVM's
  attributes speak of the whole of the function's execution (`noalias`: no access during it to
  memory modified through the pointer except through pointers based on it). The step between
  them is that the borrow's lend is open from the function's entry to its return, and that the
  function reaches the cell only through borrows of that lend: its owner is not among the
  parameters. It holds at a source function, the code of a source `λ`, thunk or `&`: the source
  term forces or applies its closure inside every lend whose borrow it receives, and the lend's
  owner is not in the source term's context there. It does not hold at the functions the machine
  conversion makes (§49): a cancel step, a call point's step, a join, a resume, a finaliser or a
  stack-machine function can take a borrow beside its owner, and a cancel step ends the lend and
  frees the cell. So:
  - **The rule.** Each LIR function carries one bit per parameter (`Fn.lendEncl`): its lends
    enclose the function. The bit is set where the function is made, at a source `λ`, thunk or
    `&` (`Convert.mkClos`, `Convert.mkAmp` with `source`, `Convert.sourceEncl`); every other
    function the conversion makes leaves it empty, and a missing bit is a cleared one, so a
    function added later carries no fact unless its maker sets the bit. `paramFacts` emits a
    parameter's facts only when its bit is set, and every fact's cite names the step.
  - **The step is an assumption,** `Backend2.LendEnclosesFn` (`Backend2/Driver.lean`), over the LIR
    interpreter's configurations: at every call a run makes, a borrow at a parameter whose bit is
    set is not beside its cell's owner among the parameters (the same parameter included), nor
    beside another borrow of the cell unless both are `imm`, and its cell is live at every
    configuration the call reaches. The LIR's types carry no lifetimes, so the LIR does not show
    it. The LIR interpreter checks it at every call of every run (`enclosesB`, sound for
    `EnclosesAt`, and the cell at the return); `Backend2/LintTests.lean` gives a program `Lint`
    accepts whose run fails it at a set bit. An owner reached other than as a parameter's word
    (in a closure's environment, in a cell), which `noalias` also forbids, is part of the
    assumption but not of its statement; the interpreter sees it only through the cell's liveness
    at the call's return. `bcc trusted` lists `LendEnclosesFn` at every function with
    a borrow fact, read off the word IR's `Fn.facts`.
- **`willreturn` and `mustprogress`** on the functions of the *willreturn class*
  (`Low.willreturnClass`, `Flat.Fn.willreturn`, with the facts only). LangRef: "a call of this
  function will either exhibit undefined behavior or comes back and continues execution at a
  point in the existing call stack that includes the current invocation", and `willreturn`
  implies `mustprogress`. The class is held to the bar the borrow facts meet: a kernel fact plus
  the lowering's faithfulness.
  - **The empty-row bit.** Each LIR function carries `Fn.emptyRow`, set where the function is made
    from the checked type: at a source `λ` whose body is at `F B` (`CTy.atEmptyRow`), a dead `λ`
    at the empty row, a thunk (its body is at `F A`), and each `F B` component of a source `&`.
    Every function the conversion makes for itself leaves it cleared; a cleared bit keeps a
    function out of the class.
  - **The class** is the greatest set of word-IR functions with the bit set whose bodies call no
    runtime function but `bc_free` and call only functions of the set. So a function in it
    reaches no allocation (`bc_alloc` aborts when `malloc` fails, which does not return), no
    read or write (`bc_getc`, `bc_getv`, `bc_putc`, `bc_putv`: each may block without end, and a
    capability is a `mut` argument, and `print_lit`'s writes take none, so the row does not
    exclude them), no sleep, no clock and no exit status. Until allocation is tracked in rows
    (#763), the body's calls stand in for it: the class grows when the row says it.
  - **The citation.** At related arguments a computation at the empty row returns under every
    allocator: `total_open` (`Core/Totality.lean`, §14), or `total_open_pin` under `PinLaw`
    (`Core/PinFundamental.lean`). That the native call is the LIR's call is the lowering's
    faithfulness, which every native fact rests on. That a call a run reaches is at related
    arguments, at a tagged typed world the memory lowers, is `total_open`'s premise and is not
    faithfulness: it is proved for a closed `CDerives` program at a plain context
    (`total_subrun`, which needs no relation premise), and is the named assumption
    `CallRelated` otherwise (under a handler or catch frame, under `PinLaw`, with externs, for a
    `main` that loops). The machine stack does not overflow in such a call: the named host
    assumption `HostStack`. `bcc trusted` lists both at each function of the class, read off the
    word IR's `Fn.willreturn`. A `trap` block in such a
    function is unreachable by `adequacyD` and faithfulness, as everywhere; LLVM may now treat it
    as such.
- **`nounwind`** on every function, as before, now cited: the named assumption `NoUnwind`
  (`Backend2.nativeAssumptions`, `bcc trusted`): no `invoke`, `landingpad` or `resume` is emitted;
  errors and cancels are branches (§47); every extern is a C function of
  `Target/Native/Runtime.lean`, C does not unwind, and the runtime cancels no thread. `abort` and
  `llvm.trap` are traps, which LangRef's `nounwind` permits.
- **`musttail`** on every tail call, as §40; LLVM's verifier rejects one it cannot honour, and the
  native stage of `scripts/compile-backend2.sh` builds every program.
- **`alwaysinline`** where the LIR asks for it (`Fn.inline`, with its reason): a call point's
  step (§49), which is its machine's code after the call, a function only so that the resume
  entry can enter it again.
- **One exit block.** A function that returns by value stores its result words in slots and
  branches to one `ret`, so where returns join after inlining each word is a scalar `phi`, not a
  `phi` of the aggregate, which LLVM does not split (sieve's inner loop).
- **Frame slots by rule** (§35, as built in N1, `Backend2/Frames.lean`): a cell allocated for one
  lend (`lendCell`, `withbor (alloc v) cb`) is a slot of its function's frame when its owner's one
  consumer, followed through the LIR's moves (each variable consumed once, from the masks), is a
  `free` in that function. `bcc lir --frames` counts the sites; `bcc-counts --frames` counts the
  slots a run starts.
- **A level's state cell passed on** (§49 *Open*). A machine whose state is a cell (its suspended
  computation's class holds itself) and whose body takes its continuation, with no call in tail
  position and its points at one operation, is converted again with the level's cell as the
  bottom frame of its continuation (`Frame.cellF`): `inl ()` until the level first suspends, then
  the cell, which each later suspension writes in place and the level's answer, abort or cancel
  releases. The machines are read off the first conversion's layouts, as `cellPass` reads them
  (`threadedOf`); a program with none is converted once. A recursion's levels keep one object
  each across their own suspensions, as the old backend's did.

### Tests

`scripts/native-facts.sh`, a step of the gate, on every corpus program the new backend compiles:

- **The differential run.** Built at `clang -O2` without the facts (`bcc run --backend new
  --native --no-facts`), each prints its golden output and error and ends with its golden
  status, as `scripts/compile-backend2.sh`'s native stage checks with them.
- **`alwaysinline`.** No call of a function the LIR asks to inline is left in `clang -O2`'s IR
  (52 programs ask).
- **Frame slots.** Where the old backend has a scoped cell, the slots a run starts at the new
  backend's word IR are at least the old backend's (the static sites differ: one `use` body is
  one site of the new backend's and a site per copy of the old's).
- **The lend bits.** Every function with a borrow fact in the word IR's `Fn.facts` (`bcc
  trusted`), not in the emitted attributes, which `classPtrs` filters, is a source function
  (`lam`, `thunk`, `with`). The regression pair, `corpus/async-r1-cancel-finaliser-writes.bc`
  (the cancel step `cancel 1.0`) and `corpus/async-r1-step-lend.bc` (a relaxed lend whose
  callback calls a yielding function: the call point's `step`), each has a function the
  conversion makes that takes a `mut` borrow beside its owner, and it has no fact.
- **The willreturn class.** The functions of the word IR's `Fn.willreturn` (`bcc trusted`'s
  `CallRelated and HostStack` lines) are source functions, and exactly the functions the emitted IR marks
  `willreturn mustprogress`; each marked function calls no runtime function but `bc_free` and
  only marked functions, checked on the emitted IR. `corpus/native-willreturn.bc` keeps the pair,
  by function: a source `λ` in the class that adds (`twice`), a source `λ` outside it that calls
  `bc_alloc` (`through`), and a source `λ` outside it that calls a writer (the library's
  closures), and `corpus/trusted/native-willreturn.txt` pins the class. The empty-row bit itself
  is checked only through the class it starts: a bit set at an `F_Σ` body that calls no runtime
  function would pass the script and change the trusted goldens.

### Facts read

Each parameter's type (the borrow modes of `imm`, `mut` and a family's leaves) and lend bit
(`Fn.lendEncl`, set where the function is made), each function's empty-row bit (`Fn.emptyRow`,
from the checked type where it is made) and its word-IR body's calls, the layouts (an
address's words, a cell's bytes, a class's agreement), the LIR's step functions, and a first
conversion's machines and layouts for the levels' cells.

### Programs

The 380 programs of §49 at their goldens with the facts and without. `corpus/counts-backend2.expected`
changes in `allocs` only: `rec-emit` 16 → 6 (the old backend's 6), `async-map` 29 → 27 and
`async-mapreduce` 57 → 54 (the old backend's 29 and 57). `corpus/erasure-backend2.expected`,
`corpus/counts.expected` and `kernel-counts.expected` are unchanged.

### Baseline

No change to `CDerives`, the relation, the machine, `Core/`, `Paper/`, `Support/`, the checker,
the elaboration or a kernel program. The word IR gains `Exp.gep`, `Fn.ptrs`, `Fn.facts` and
`Fn.inline`, which the old backend does not produce; its native emission is unchanged. The word
IR's interpreter counts the frame slots a run starts.

### Open

- **One object per task.** A recursive task's levels are one cell each (one per level active at
  a suspension), not one object for the task: a recursion of unbounded depth needs a stack the
  task owns, which N5 does not build.
- **Handler state in a register (#537 fix 9).** handlers-di's clock is kept in a register only
  with the facts: without them its cell is stored at every step. Under choice 6 that does not
  count; the state as a local of the LIR remains.
- **The box lifetime of `effHandleVB`** is not read. No storage of the new backend depends on it:
  `κ`'s environment is by value, and a level's cell lives as long as its level. It would matter
  where a box's contents are allocated, to place them in the scope the lifetime names.
- **`!noalias` and `!alias.scope`** (#531), where a parameter attribute is too coarse; Alive2.
- **The lend bits of the helpers.** The helpers the conversion makes (`extern`, `consume leaf`,
  `count_fold`, `count_try`, `observe`, `unfold`, `const`, `fold`) are entered as direct calls,
  and with every function's bits set the interpreter refused no helper on the corpus (it refused
  a machine's `suspend` in 9 programs), but their bits are cleared: each needs the step stated for
  it before it is set. Clearing the bits takes the facts from 2850 of the 6852 attributed
  parameter words of the corpus's native builds: the functions that lose them are `extern` 1183,
  `consume leaf` 679, `count_fold` 430, `count_try` 88, `observe`, `unfold` and `const` 25, and the
  machines' functions 65.
- **`LendEnclosesFn` proved** needs lifetimes in the LIR's types (#760's scope, §3a).

### Improvement candidates

The informational attributes are relied on for now. Each place a target or count leans on one,
or a fact left unemitted, is a candidate, to be moved into our compiler or forced where gains
remain (measured: `docs/scope/760-native-facts.md` §7):

- **#537's vectorised walk.** A counted walk over a borrowed family as vector operations from our
  lowering; `llvm.loop.vectorize.enable` is a hint, not forcing.
- **Handler state as an LIR local** (#537 fix 9), so that handlers-di's clock is SSA from our
  lowering rather than from LLVM's use of the borrow facts.
- **SSA emitted directly.** Every local is an `alloca` that SROA/mem2reg recovers; emitting `phi`s
  from the LIR removes the reliance.
- **The conversion helpers' lend bits** (*Open*, above): the facts of `extern`, `consume leaf`,
  `count_fold`, `count_try` and the others, each once its step is stated.
- **`memory(...)`** once allocation is in rows (#763): a function's parameter types and row then
  license `memory(argmem: read)` and `memory(none)`.
- **The willreturn class widened**: from the row once #763 tracks allocation; to the helpers the
  conversion makes, each with its own termination stated; and through closure calls, whose
  `apply` is outside the class today.

---

## 51. Entry 50 — `[handle-last]`: a clause that uses `κ` once, last (#564, R-1)

### Motivation

Decision 68 types `[handle]` of another name around a computation that ticks only at clauses that
resume `κ` in tail position (`effHandleT`, §14). B2's three blockers (#644: `break`/`return`
around a looping generator; a `for` body that yields, raises or calls a delegating generator;
adapters over a source computation) are one class of clause beyond it (#564's design, comment
6331907320; the user's decision R-1a): the clause works on the operation's argument, then resumes
`κ` in tail position or cancels it and leaves, and while it works `κ`'s cancel is its unwind
finaliser.

    λ(x, κ).  (w x)  then r. case r { inl y → κ.1 y  |  inr z → κ.2 (); nf z }  unwind κ.2 ()

`κ.2 ()` is the consume decision 56 says a cancellable continuation lacks: a raise from `w`, or a
cancel of an outer continuation captured inside `w`, first cancels `κ`, and so runs the
handled computation's finalisers.

### Language

One kernel rule, `effHandleL` (`CDerives`, `CDerivesAt`, `CDerivesP`; `Core/DivHandleLast.lean`).
Its clauses are written by the rule (R-1a), as `effHandleT`'s are, from two tuples: works
`ws` and exits `nfs` (`lastTuple`). `κ`'s type never appears in a program, and no type, typing rule
of another former, effect equation, machine step or `𝒱⟦·⟧` clause changes.

    Γ₁ dead, (h_ret, (ws, nfs)) a value form over Γ₁
    Γ₁ ⊢ (h_ret, (ws, nfs)) : (A ⊸ F_Σ R) ⊗ (⊗_j W_j ⊗ ⊗_j !U(X_j ⊸ F_Σ R))
    Γ₂ ⊢ e : F_{n:E[fs] ⊕ Σ} A          n ∉ Σ, n ≠ 0, n ≠ Div
    each operation of E cancellable or abortive         Σ_W ≤ Σ       Σ.NZ        ¬ Σ.UnrD
    each j: LastFinOK Σ Σ_W (fs j) X_j
    ──────────────────────────────────────────────────────────────────────── [handle-last]
    Γ ⊢ handle_n e with (h_ret, lastTuple(ws, nfs)) : F_Σ R

- **The works**: `W_j = !U(A_j ⊸ F_{Σ_W}(B_j ⊕ X_j))` at a non-abortive operation `A_j ↠ B_j`, and
  `!U(A_j ⊸ F_Σ R)` at an abortive one, whose clause is the work itself (`effHandleT`'s abortive
  clause). A work does not mention `κ`; it may tick, raise, and perform the cancellable operations
  of `Σ_W`.
- **The clause** of a non-abortive operation is the one displayed above (`lastClause`): the work's
  answer `inl y` resumes `κ` at `y` in tail position, `inr z` cancels `κ` and runs the exit at `z`.
- **The operations are cancellable or abortive.** A must-resume operation's `κ` has no cancel; it
  stays `effHandleT`'s.
- **`¬ Σ.UnrD`** is `[then]`'s `hU` (§27): `κ` is not persistent, so no unrestricted operation may
  capture the frame that holds it. Decision 63 makes this a restriction, not a cost.
- **`Σ.NZ`** is `[then]`'s: the frame's `[finalise]` step asks the raise's name not to be `0`.
- **The cancel rows** (`LastFinOK`): for each operation, its cancel row `F = fs j` is not `⊤`, is
  below `Σ` (D3) and does not hold `Div` (decision 69: `κ.2 ()` is the clause's finaliser); each
  capturable operation of `Σ_W` has a cancel row above its own `⋈ F` (`[then]`'s `hfin`); the errors
  pending at the finaliser are persistent where `F` has an unrestricted operation (`[then]`'s
  `hP`); and `X_j` holds no owned cell where `F` has a cancellable or unrestricted operation
  (`[let]`'s `hW`, at `Row.Cancels`: `z : X_j` is
  held across `κ.2 ()`, which may raise or be captured and cancelled). At the empty cancel rows
  the checker emits (§27 *Baseline*), `LastFinOK` is `[then]`'s `hfin` at the empty finaliser row
  (`lastFinOK_nil`), which holds where `Σ_W` finds what `Σ` finds (`lastFinOK_nil_of_find`).
- **The handled row may hold `Div`.** The handler forwards `tick`, as `effHandleT`'s does.

**`κ`'s cancel branch.** The proof gives `κ.2` the table of the operation's own cancel row `fs j`
(`lastTc`), which `ewp_handle_or`'s `hTc` permits: it asks only that the table be above the
entry's cancel obligation. `κ`'s type at a clause the program writes, `cancelTy Σ F = F_{F ⊕ Σ} 1`,
holds `Div` whenever `Σ` does, and as a finaliser it makes the cancel row of every capturable
operation of `Σ` beneath it find that operation's own key (`kappaFinSelf`). A rule-written clause
avoids both.

### The proof

`handleL_compatC` is the rule's compatibility lemma.

- **At a row holding `Div`** (`cwp_handle_last`), by coinduction, as `cwp_handle_tail`: the
  candidate `lastY` is the least fixed point of the handled computations under the handler, the
  finaliser frame around a work with `κ` in the frame resumed into one segment of the candidate
  (`lastW₂`), and `cwp`. `κ`'s relation is `KapRelT` at one segment of the candidate, the relation
  `cwp_handle_tail` gives it, with its cancel at `fs j`'s table.
- **The finaliser frame at a candidate** (`cwpF_frame_then`, T-A1): `[then]` around a computation
  of `cwp`, one segment, at a parameter candidate `Y`; `cwp_then` is now its instance. A tick
  inside the frame owes the frame around its continuation to `Y` and to `Closing`
  (`closing_then`); `κ`'s capture cell is in the frame's resource, carried along the list
  (`KapRelT.same`, `KapRelT.ext`).
- **The frame's answer** (`last_cont`): `inl y` resumes `κ`; `inr z` cancels `κ` at its cancel
  row's table beside `z` (`ewp_frame_plain_or`), then runs the exit.
- **`Closing`** (`last_closing`) is `ewp_handle` at the closing tables, the work under the frame
  by `closing_then`.
- **Elsewhere** (`ewp_handle_last`) it is Core's `ewp_handle` with the frame `ewp_frame_then`.
- The Fundamental Property is applied to `h_ret`, the works, the exits and `e`, never to a term
  that mentions `κ`. The relation, `𝒱⟦·⟧` and `CDerives`' indices are unchanged; no step index.

### Baseline

`fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`, `fundamentalC_pin`, `total_every_run`
and every borrow guarantee keep their statements and cover the new rule. The handler inversions
(`der_hnd`, `der_hndJ`, `HndBase`) read a third form, `lastTuple`'s; `der_hndJ₁` asks a clause
tuple to be neither `tailTuple`'s nor `lastTuple`'s (`not_tail` proves both). The typed term
(`TExpr`, `TDerivesAt`, `TDerivesP`) gains the node `effHandleL`, generated (`scripts/gen-pin.py`);
the checker emits no such node, and its absorption places none at a wider context, as
`effHandleT`'s. No change to the checker's output, the elaboration, `Backend/`, `Backend2/`, the
corpus or a golden.

### Open

- **The erasure laws** (`Core/HandleLastErase.lean`, #918) are proved at the direct call `hnd H
  K[case (w v) {inl y → y | inr z → X}]` (`directK`) of a work whose direct run leaves κ's cell free
  (`StepsOff`; `StepsOff.upd` runs it beside the cell). T-B1 `last_resume_direct`: both runs reach
  `K₀[hnd H K[y]]`. T-B1′ `last_cancel_direct`: the perform reaches `K₀[(λ_. nf z)(ccatch K†[raise
  ⊥])]`, `K`'s cancel then the exit (`last_cancel_exit`), and the direct call reaches its `inr` arm.
  T-B2 `last_perform_direct`: a work whose performs are answered in place by handlers outside the
  node (`WorkRun`), of names other than `n` and unhandled in `K`, by the two-run lemma
  `work_run_ctx`. Outer handlers that answer in place: `answers_in_place`, from
  `tail_clause_answers` and `last_clause_answers` (nested `[handle-last]`, pipe fusion's normal
  path). Each law is a forward correspondence on the machine: given the work's run when called
  directly, which leaves κ's cell free (`StepsOff`), the handled program and the direct program
  reach the same configuration at the same memory, in any outer context `K₀` and handler-free `K`.
  T-B2 matches the two runs segment by segment, under `WorkRun`'s `hans`: the outer handler answers
  the same whatever continuation it captures. Open: runs the hypothesis does not give (a work that
  diverges or does not leave κ's cell free); T-B2 when an outer handler stores or cancels the
  captured κ, or a raise or cancel crosses the active frame (an early stop, `stop()`, a raise across
  a fused stage), not derived and not refuted (a whole-run simulation); a Core term for the in-place
  cancel-mode unwind (Core expresses it only through κ's `ccatch K†`); the laws are stated on
  machine values, not on typed `lastH`.
- **The elaboration** of `for` with `break`/`return` and a body that performs, and the adapters
  over a source computation (R-1's frontend): it needs a checker producer for the node
  (`TTied`'s builder, the clause kinds of the node, `Frontend/Check/Kinds.lean`, and its handled
  names), and the works' and exits' tuples written by the elaborator.
- **Handler state** (R-2, `effHandleLS`).
- **Finalisers are total, as a theorem** (decision 69, §14 *Open*): a work, like `effHandleT`'s
  answering function, may tick without end.

---

## 52. Entry 51 — the new backend: a stack each task owns (#664, option B)

### Motivation

#664's investigation measured two costs of the new backend's async programs (§49, §50).
`async-tree`, a recursive task, resumes by entering every suspended level: a level's state holds
its callee's `k`, so a resume is a chain of non-tail calls as deep as the recursion, and each
level's state is a cell of its own (72% of the run in one resume code, one allocation per level).
`async-tree-iter`, a task of constant depth, spends its time in the scheduler: a task is its
continuation by value (26 words there), copied into two new list nodes at every `await`. The
user's decision (#664, comment 6339030614) is option B: each task owns a stack of first-order
frames, so a suspended task is small and the queue holds it with no list node per `await`. The
corpus's counts (`corpus/counts-backend2.expected`) are not to rise for it.

Decision 25 holds: every lowering is stackless and portable, and no native stack is switched. The
stack is a heap record of frames, as §20's `deep` driver's buffer is.

### Language

No change: no type, rule, term, typing, elaboration or semantics. `lib/async.bc`'s scheduler
changes its representation, not its meaning (*The scheduler*, below).

### Lowering

`Backend2/`, read from the typed term, the nodes' kinds and the layouts of a first conversion.
One rule per construct:

| construct | rule | law |
|---|---|---|
| a BOXED-κ site's `κ`, where the site has a stack | its environment is the stack's `κ` region, written in place; `κ` is the stack | `[op]`, `kappa_resume_steps` |
| a stack machine's level | its state is a frame on the current task stack, reserved when the level starts; a call point's state leaves the callee's `k` out | `kappa_resume_steps`, the nesting kept as positions |
| a stack machine's `k` | its frame's address; resumed from the top of the stack down to it | `kappa_resume_steps` |
| a stack machine's cancel | the frames from the top down to it, innermost first | `kappa_cancel_steps`, `cancel_prefix` |
| a BOXED-κ site | runs its handled computation on a stack of its own, made current around each run | one owner (BOXED-κ, §28) |

- **`κ` in the site's stack** (`convDrive`, `genKap`). At a site that has a stack (*The task
  stack*, below), the first operation whose clause is `stored` (`ks`, `classifyHandler_sound`) and
  whose qualifier is not `unr` keeps `κ`'s environment, the handled computation's `k` and the
  handler's values (§49 *A `handle` node as a drive*), in the stack's `κ` region, and `κ`'s own
  environment is the stack alone. The site makes the stack at the computation's first run, the
  region inside its one allocation (`Op.stackNew`). A suspension there writes the region
  (`Op.kappaPut`) and answers `κ`; `κ`'s resume entry takes it out (`Op.kappaTake`). By `[op]`,
  `κ` is the closure over `(k, H)` and `resume κ y` drives `resume k y` again, so the region's
  contents before and after a resume are the old and the new `κ`'s environments. The stack's free
  ends it, where the computation answers, aborts or is cancelled. The task's value, the closure of
  its body's one code (§49 *One code per task body*), is then its variant's tag and one word, and
  the task owns one allocation: its stack. One operation a site: a region shared by two would join
  their computations' classes, and a resume would dispatch between them. At a site with no stack,
  `κ`'s environment stays by value (§49): a cell there would be an allocation a task did not make
  before.
- **Stack machines** (`stackedOf`, `genStackMach`). A machine is a stack machine when its level's
  cell is passed on (§50: its suspended computation's class holds itself, its points at one
  operation, no call in tail position, not `unr`), every call point of it calls a level of itself
  (the layouts' classes of the callee's suspended computations are its own code, `suspCodes`), and
  every `handle` node of its operation is a BOXED-κ site whose clause is `stored`, with no operation
  of the node at `unr` (`stackOps`).
  Each level reserves its frame on the current stack when it starts (`Op.framePush`; the bottom of
  its continuation is `Frame.stackF`, the frame and its address) and pops it where it answers,
  aborts or is cancelled (`Op.framePop`), so a level's frame is directly above its caller's. A
  point's state is first order, its continuation's variables: at a call point the callee's `k`,
  which stands for the frames above, is left out. A point's `mk` writes the state into the frame
  (`Op.framePut`), which stays on the stack, and answers the level's `k`: a closure of one code
  whose environment is the frame's address.
  - *Resume.* `kappa_resume_steps`: `resume (point_i k) y = step_i (resume k y)` and
    `step_i (susp (p, k')) = susp (p, point_i k')`. With `k'` the frames above `point_i`'s frame
    and `point_i`'s frame in place, the outer steps of a suspension that leaves the frames below
    as they were are the identity: a level's step that receives a suspension writes its own state
    and answers its own `k`, and nothing below it is entered again. `k`'s resume entry is a loop
    from the top of the stack down to `k`'s frame, the base (`stack resume`, `stack step`): the top
    frame's level continues at its `perform` with the answer (`stack continue`); a level that
    answers has popped its frame, and the frame below, at its call of that level, continues with
    the value (`stack return`, `step_i`'s value arm, `[ret]` of the frame's continuation) or with
    the abort (`stack unwind`, its abort arm, `then_fin`, `unwind_prefix`); any level's suspension
    suspends `k` again at the base. When the base's level answers, its answer is `k`'s. The loop
    is a tail call, so a resume runs in constant native stack.
  - *Cancel.* `kappa_cancel_steps`, `cancel_prefix`: `k`'s cancel entry pops the frames from the
    top down to the base, each frame's continuation unwound under the cancel (§19 *Cancels*,
    `cancelK`), the first error kept: innermost first.
  - *Unreachable arms.* The top frame is at a `perform` and a frame below a level that answered is
    at its call of that level: the other arms of `stack continue` and `stack return` are
    `Op.unreachable` (a trap; the LIR lint reads a path that reaches it as one that ends at
    `absurd`).
- **The task stack** (`convDrive`, `genKap`, `MPoint.swapAt`). Where the program has a stack
  machine, each stored BOXED-κ site runs its handled computation on a stack of its own. A static
  word of the program's data holds the current stack (`Op.stackSwap`, `CState.stackReg`): the
  site swaps its stack in around every run of the computation — its first run, `κ`'s resume and
  cancel, a forwarding point's resume and cancel of the computation's `k` — and swaps the one it
  displaced back after. The site's stack is a drive parameter after the handler's values, `κ`'s
  last value, and part of a forwarding point's state (`Frame.stackH`); it is `0` until the first
  frame is reserved, which makes it, and it is freed where the computation answers, aborts or is
  cancelled (`Op.stackFree`). With a `κ` region the site makes the stack at the first run; without
  one the first frame reserved makes it.
  - *No `unr` site.* A site switches stacks only when no operation of its node is `unr`: a `κ`
    that may be copied would hold the stack twice, and a second resume would swap in a stack the
    first had freed. `corpus/async-unr-site.bc` is such a site in a program with a stack machine
    (a `multi ctl` operation whose clause resumes two copies of `κ`): it does not switch.
  - *One owner, frames in order* (the invariant the native code relies on). Only stack machines
    reserve frames. Their levels call only themselves, so a stack holds one recursion's frames at
    a time, contiguous at its top, nested as the calls are. They suspend only at an operation
    every node of which is a stored BOXED-κ site, so the suspension reaches the site through
    drives that pass it on (forwarding) and run no code of the program meanwhile; the site's `κ`,
    cancellable or must-resume, holds the stack, and every resume or cancel of it goes through the
    site's own entries, which make the stack current. So frames are pushed and popped in order on
    the stack they were reserved on, and a resume finds its frames at the top.
  - *The stack* (`Backend2/Lower.lean`, `stack push`, `stack pop`): a header (the next free word,
    the chunk's end, the chunk) and a first chunk of 256 words, one allocation; a frame that does
    not fit opens a chunk of 4096 words or its own size, linked to the one before, and freed when
    its first frame is popped. The top frame is the free word less the frame's words: one
    recursion's frames are one machine's, of one size.
- **The scheduler** (`lib/async.bc`). `run_until_empty` moves the queue's slots, a list the last
  queued first, into an array in queued order once, and each round resumes each pending task in
  its slot in place (`array_replace`): no list node per `await`, and a queue slot is a task's two
  words. `push`, `queue` and the types are unchanged; `run_logged` and `run_in` keep their lists.
  The old backend's `array_replace` (`Core/Arrays.lean`, `replaceV`: `(λold. store c x; old)
  (load c)`) is a swap at the slot, its copy and consume cancelled as the axiom `swap`'s are
  (`Backend/Clos/Convert.lean`, `Op.swapSlot`, whose contents keep their type).
- **Frame pointers.** The native target's typed mode marks each function `"frame-pointer"="all"`,
  so a profiler's backtraces reach past `bc_entry` (#664's method note). On the three async
  benchmarks it costs nothing measurable (CPU time, median of 9: 302.7 against 303.4 ms, 105.2
  against 105.5, 45.7 against 46.7).

### The hand-over

A level's `k` is `clos kc [a]`, a closure of the machine's code over its frame's address `a`. Two
nodes consume one, each for `clos kc [base]`, a `k` lower on the stack: the step, at a suspension of
the level at `a`, for the machine's own `k` over the base; a call point's `mk`, the callee's `k`
for the level's own over its frame. The consume is the rule `stackK`, and its body binds the `k` that
takes over first:

    consume x (stack k); let k₂ = clos kc [base] in …

No type licenses it: the consumed value is a closure, and the kernel does not see the task stack.
It rests on one named assertion, `UNPROVED:` (`Backend2.StackKHandOver`, `Backend2/Driver.lean`):
at every configuration of the LIR interpreter that a run of a converted program reaches at a
`stackK` consume (`Visits`), `x` is `clos kc [a]` and `base` is at or below `a` on the current task
stack, the frames from the top down to `a` written (`HandOver`, `TakesOver`). That `k₂`, resumed
or cancelled as its type requires, then releases the frames the consumed `k` stood for, so that the
consume leaks nothing, is part of the assumption. Proved beside it, and only this: `k₂`'s frame range
contains the consumed `k`'s (`TakesOver.suffix`), and a `stackK` consume's step, as every consume's,
touches no heap (`enter_stackK_keeps`). #755 (task stacks in the kernel) is the route to proving
it.

- **Lint** checks the premise the node shows (`Lint.handsOver`): the body binds `clos kc [base]`
  first, `kc` is a `&` code each of whose functions takes one address, `x` and `k₂` are of `kc`'s
  closure type, and `base` is an address. It reads no list of variables.
- **The LIR interpreter** checks the hand-over at every `stackK` consume of every run
  (`handOverB`, sound for `HandOver`: `handOverB_sound`), so the gate checks it on every program
  the new backend runs.
- **Its scope is the code `Convert` generates.** `Backend2/LintTests.lean` has a program `Lint`
  accepts whose consume is not a hand-over; the interpreter refuses its run.
- **`bcc trusted`** lists `StackKHandOver` at each function of a program's LIR with a `stackK`
  consume.

### Checked, tested, trusted

- **Checked** in the conversion's facts: one recursion's machine per stack (`stackedOf`: every call
  point's callee classes non-empty and the machine's own), one owner (`stackOps`: every node of
  the operation a stored BOXED-κ site, none `unr`; `κ` cancellable or must-resume by the kernel's
  typing), and the frame's state type against the first conversion's. Checked at run time by the LIR
  interpreter (`Backend2/Interp.lean`), on every program the new backend compiles at the gate:
  a stack swapped in is a live stack; a frame is pushed on the current stack and popped only as
  its top and unwritten; `framePut` writes only an unwritten frame; `frameTop` takes the top of a
  non-empty current stack; a `κ` region is written only when empty and taken only when written; a
  stack is freed only when it holds no frame and an empty region and is not current.
- **Tested** at the LIR interpreter, the word IR, Wasm and natively, against the reference
  interpreter's goldens: the async corpus, and stress programs for the stack —
  `async-stack-deep` (two linear recursions 1200 and 150 deep, awaiting on the way down and back,
  growing into new chunks and out of them, interleaved with a tree task in one queue),
  `async-stack-cancel` (a task cancelled 400 levels deep, each level owning a cell its consume glue
  frees, and one cancelled at its first `await`), `async-stack-nested` (a recursive task that
  spawns and drives a recursive task at each level, two stacks switched at different depths) and
  `async-unr-site` (above).
- **Trusted**: the hand-over at each `stackK` consume (`StackKHandOver`, *The hand-over*). The
  native and Wasm code does not check the frame stack at run time. That every
  frame it touches is live, of the right machine, and taken by the `k` it belongs to rests on the
  conversion emitting code with the shape the invariant above assumes, as the rest of the backend's
  lowering is trusted (no compiler proof, decision #15). A proof of the invariant over an abstract
  model of the stack operations is assessed in #664 (tractable as a design proof; linking it to the
  emitted code is the compiler proof the project does not build).
- **Not leak-free.** Core's `adequacyC` proves the elaborated term leak-free, but this lowering
  does not keep that. A task that is consumed rather than cancelled leaks its continuation's cell
  and its stack, as §49's state cells already do on a consumed suspension. Nothing checks or tests
  for this: the LIR interpreter's checks cover use, not eventual release, and no corpus program
  consumes a task. Whether a kernel-typed program can reach it is open (#671).

### Facts read

The nodes' former (`effHandleVB`), clause kinds (`ks`) and qualifiers (`E`); the machine
operations (§49); and, after a first conversion, the layouts' recursive classes (§35), each call
point's callee's suspended computations' classes (`MPoint.outVar`, `suspCodes`) and the machines
whose cell is passed on (§50, `threadedOf`). The backend guesses neither the frames' owner (the
BOXED-κ site's `κ`, its one owner) nor the frame set (one machine's levels, by the layouts).

### Programs

The 380 programs of §49 at their goldens at the LIR interpreter, the word IR, Wasm and natively.
`async-tree` and `async-mapreduce` are the corpus's and benchmarks' programs with a stack machine.
The bench rows, the new backend natively (CPU time, median of 7, interleaved, the benchmarks'
arguments; #664's method):

| benchmark (`args`) | before: ms, ns per `await`, allocations per `await` | after | Rust | after / Rust |
|---|---|---|---|---|
| `async-tree` (`1048576 28`) | 1504, 51.2, 3.0 | 254, 8.7, 0 (87 in all) | 111 (its walk iterative) | 2.30× |
| `async-tree-iter` (`1048576 28`) | 722, 24.6, 2.0 | 155, 5.3, 0 (115 in all) | 109 | 1.42× |
| `async-tree-boxed` (`1048576 4`) | 251, 59.9, 3.0 | 42, 9.9, 0 (15 in all) | 314 (`Box::pin` a level) | 0.13× |

`async-tree-iter` has no stack machine, so its task keeps `κ` by value (26 words) and the
scheduler moves it into and out of its slot; with `κ` in a cell of its own it ran at 0.95×, one
allocation per task more. The old backend, with the array scheduler and `Op.swapSlot`:
`async-tree` 1625 → 1263 ms, `async-tree-iter` 916 → 199, `async-tree-boxed` 251 → 211.

Counts. `corpus/counts-backend2.expected` rises in the six programs that run `run_until_empty`
and nowhere else; each row's note says why:

| program | main (allocs indirect copies loads stores bounds) | now |
|---|---|---|
| `async-bank-inbox` | 26 0 0 396 388 0 | 11 0 0 450 442 16 |
| `async-cancel` | 10 0 0 113 110 0 | 5 0 0 137 134 6 |
| `async-lend-slots` | 22 0 0 294 282 0 | 7 0 0 334 322 16 |
| `async-map` | 27 0 0 245 222 0 | 18 0 0 251 228 10 |
| `async-mapreduce` | 54 0 1 498 480 0 | 22 0 1 489 435 30 |
| `async-scheduler` | 24 0 0 398 392 0 | 5 0 0 446 440 20 |

`bounds` rises by a check per slot visit: `array_replace` tests its index, and no checked fact
puts a counted loop's index in range of an array the loop moves elements of (§46 covers a read
through a view, and at a unique view the split's own test stays): *Open*. `loads` and `stores`
rise where the task is held by value: the array's fill and the passes into and out of it cost a
pass more than the list's, and a round moves each task as the list did. `corpus/counts.expected`
(the old backend) rises in the same six, with notes. `kernel-counts.expected` and
`corpus/erasure-backend2.expected` are unchanged.

### Baseline

No change to `CDerives`, the relation, the machine, `Core/`, `Paper/`, `Support/`, the checker, the
elaboration or a kernel program. The LIR gains `Op.stackSwap`, `stackFree`, `framePush`,
`frameTop`, `framePut`, `framePop`, `stackNew`, `kappaPut`, `kappaTake` and `unreachable`, at the LIR interpreter, the word IR, Wasm and
natively; the old backend's closure IR gains `Op.swapSlot`. Every output, golden and exit status is
unchanged on both backends.

### Open

- **The in-range fact for a moving walk.** A counted loop over an array's length that moves each
  slot out and back (`array_replace`, or a unique view's split) keeps its index test: the fact
  that the index is below the array's length at a unique view (§46's `n − i`) is not proved. Until
  it is, the array scheduler's `bounds` count stays up.
- **`κ` by value at a site with no stack.** A non-recursive task is its continuation by value
  (`async-tree-iter`: 26 words moved per slot visit); a cell of its own would be one allocation per
  task.
- **A leaf level reserves its frame.** A level that answers without a call or a `perform` still
  pushes and pops its frame; reserving it at the level's first point needs §50's slot.
- **Other recursions keep cells** (§49, §50): a recursion through several machines, one whose
  levels call other machines, one at an operation that a site does not keep boxed (a generator).
- **The register is one word.** With threads (decision: threads are required) the current stack is
  per thread.
- **A task consumed without its cancel leaks**: its cell and its stack, as §49's state cells
  do. See *Checked, tested, trusted* and #671. Under the finaliser algebra, consuming a suspension
  that holds resources would have to run its cancel path, which makes `drop` control flow that can
  raise. That is a decision for where the kernel types the consumed value, not a backend patch.
- **The array scheduler's bounds checks.** `array_replace` checks its index; no fact puts a counted
  loop's index in range of an array it does not read through a view (§46).
- `run_logged` and `run_in` still build list nodes per round.
- **A chunk boundary.** A recursion that goes back and forth across the end of a chunk allocates
  and frees the next chunk each time it crosses; a spare chunk kept on the stack would end it.

## 53. Entry 52 — lowering under the semantic relation: the statements (#699, U0 of #698)

### Retired

This entry stated the obligations of a lowering proved in the semantic relation (the low subset of
`Expr`, `LowerSem`, the print's simulation and its transfer to the LIR). The route was consumed
(user, 2026-10-28): lowering by simulation in `SemC` moves the hard parts into the relation's
definitions, and a safety relation would still accept a wrong answer. The `Lowering/` library and
its corpus check are removed. Backend2 is the backend, and it reads the kernel's facts instead
(#713, #715; CLAUDE.md, *Later stages read the kernel's facts*).

---

## 54. Entry 53 — lowering under the semantic relation: explicit ownership, `own` (#700, U1 of #698)

### Retired

This entry gave `own`, a lowering that wrote every copy and consume the kernel leaves implicit, proved
in the relation and in §53's low subset on the pure fragment. The route was consumed (user,
2026-10-28): lowering by simulation in `SemC` moves the hard parts into the relation's definitions,
and a safety relation would still accept a wrong answer. The `Lowering/` library and its corpus
check are removed. Backend2 is the backend, and it reads the kernel's facts instead (#713, #715;
CLAUDE.md, *Later stages read the kernel's facts*).

---

## 55. Entry 54 — a split's masks cover its parts (#701, U2 of #698)

### Motivation

Coverage says every slot a split's part reads is one its mask holds, so a stage that gives a part
the live slots its mask holds gives it every slot it reads. The checker builds each mask as its
part's uses (`Fam.split`), so its terms have that, but the typed split rules did not say so:
`SplitMasks` asks only that a slot a mask holds be live in the part's context, and a part's context
may hold a live slot its mask does not (a persistent slot a leaf consumes, or reads). The user decided
(#701, option 1): the typed split rules carry the condition, every derivation has it, and the
checker is proved to meet it. It is a fact of the typed term, which later stages may read.

### Language

The typed derivations (`TDerivesAt`, `TDerivesP`, `Frontend/Check/TDerives.lean`) change: every
rule at a split has one premise more. `CDerives`, `CDerivesAt`, `CDerivesP`, the relation, the
machine, the checker's output and every backend are unchanged; the projections to `CDerivesAt`
and `CDerivesP` consume the premise as they consume `SplitMasks`.

### Statements

- **Coverage** (`Covers u n e`, `Frontend/Check/Masks.lean`): every slot the term `e` mentions,
  under the `n` binders its premise pushes, is one the mask `u` holds. Each typed split rule has
  the premise `hcv`: each part's term, at the binders its premise pushes, is covered by its part's
  mask; `M x`'s second part is its argument `x`. Generated with the rules (`scripts/gen-pin.py`,
  `cov_premise`): `tensorI`, `bind`, `app`, `unitE`, `tensorE`, `sumE`, `zeroE`, `lolliE`,
  `effLet`, `effThen`, `effHandleV`, `effHandleVB`, `effHandleT`, `effHandleL`. It names the slots
  a part's term mentions, not its context's liveness, so the checker's masks are unchanged.
- **A typed term mentions only live slots** (`CDerivesP.mentions_live`, `Core/Mentions.lean`): a
  term `CDerivesP` types at `Γ` mentions only slots live in `Γ`. Induction on `CDerivesP`, as
  `closedAt_of_derives`; `[let-poly]` by `mentions_fill`, the clauses of `[handle]`'s tail and last
  forms by `mentions_tailTuple`, `mentions_lastTuple`.
- **The checker meets it** (`Frontend/Check/Rules.lean`): a family of derivations holds at every
  liveness between its uses and its absorption, so at its uses alone (`btw_self`), where every slot
  it does not use is dead; so its term is covered by its uses (`Fam.covers`, `Res.covers`,
  `TTied.covers`). Every split builder passes its parts' coverage to the typed rule, and
  `TTied.consume` and `TTied.shorten` their nodes'.
- **Weakening keeps it** (`Frontend/Check/Weaken.lean`): a part's term shifted past inserted slots
  is covered by its mask with the slots inserted (`Covers.ins`); `TExpr.reAb` keeps the erasure.
- **Non-vacuity**: every checked program carries its typed derivation (`Checked.tied`), so its
  typed term has the premise at each of its splits.

### Baseline

The fundamental property, adequacy and every borrow guarantee are unchanged: they are stated over
`CDerives`/`CDerivesP` and the typed derivations' projections, which are unchanged. The checker's
masks, its typed terms and every output, golden and count are unchanged.

---

## 56. Entry 55 — the print to the LIR, simulated with the source's memory (#701, U2 of #698)

### Retired

This entry gave a print of `own`'s output to Backend2's LIR and its simulation with the source's
memory. The route was consumed (user, 2026-10-28): lowering by simulation in `SemC` moves the hard
parts into the relation's definitions, and a safety relation would still accept a wrong answer. The
`Lowering/` library, its corpus check and the LIR's operations on the source's memory are removed.
Backend2 is the backend, and it reads the kernel's facts instead (#713, #715; CLAUDE.md, *Later
stages read the kernel's facts*).

---

## 57. Entry 56 — the facts Backend2 rebuilt, as derived nodes (#712, part B)

### Motivation

Backend2 rebuilt from its own IR facts the typed term has or could have, and five checked
programs miscompile there (`docs/compiler.md` §10). This entry puts the missing facts in the typed
term as derived nodes (as `lendCell` and `walk` are), each fixed by its typed rule, so that a
backend reads them. Backend2 does not read them yet (#712, part C).

### Language

No change to a type, rule of `CDerives`, term, typing, semantics or erasure. The typed
derivations (`TDerivesAt`, `TDerivesP`) gain three derived nodes and one premise; each projects to
its child's derivation, so `TDerivesAt.erase`, `TDerivesP.erase` and every theorem over them are
unchanged. The elaborator marks one more scheme (`SchemeMark.litView`).

### The facts

- **A lend's kind** (`lendKindB`, `Frontend/Check/FactNodes.lean`): the `lendCell` rule has the
  premise that its `m` is the kind of the borrow constant at its term's head (`withbor2` and
  `withbor2U` `mut`, `withbor1` and `withbor1U` `imm`). The erasure cannot say it. The checker
  checks the elaborator's mark against it (`rMarked`).
- **A lent cell's free** (`TExpr.lendScope`, `lendScopeT`, `lendRelT`): the checker builds the
  node over `[⊗E]` of a `lendCell` node, or `[let]` of `return` of one whose body is `[⊗E]` of its
  variable (`rScope`), and its rule fixes `rel`: on every path of the code after the pair is taken
  apart, the owner's slot, passed to one part at each split by the split's masks, reaches `free`
  or a cell's consume and nothing else; a `case` passes it to both arms (`relT`). This covers
  the `case` whose arms consume the owner differently (`t4`, `t18`): `rel` is `false` there.
- **A literal's view** (`TExpr.litView`, `litViewT`): the elaboration of `borrow imm "…" { v -> S }`
  is marked, and its rule fixes the scheme: the place's table tabulated into an array
  (`array_new`), the array lent by `slice_borrow_imm`, and the array the lend hands back given
  straight to its consume.
- **`unfold step`** (`TExpr.unfoldStep`, `unfoldAppT`): the checker builds the node over the bound
  computation of a `[let]` that is the `unfoldN` constant applied to a step (`rUnfoldStep`), so
  the `bind` binds `unfold step` (SPEC §45's `nuEta` reads its `f` there).
- **An allocation's width class** (`Checked.classAt`, `Frontend/Check/Program.lean`): the cell
  class rooted at the type an `alloc` node allocates at; `Checked.classAt_alloc`: it exists, holds
  the type and is closed under every `swap` of the term. Backend2's `Driver.cellsRooted` keeps the
  roots that `cellsOf` consumed. A cell's width class takes a fixed former where its types' layouts
  mix them: an opaque value over an integer, a `ref` over a `mut` over an `imm`. The width depends on the types alone, not
  on the order Backend2's layout joins them.

Each rule's premise is of the node's own typed term and is kept by the moves to a wider context
(`relT_shift`, `lendRelT_shift`, `lendScopeT_shift`, `lendKindB_shift`, `litViewT_shift`,
`unfoldAppT_shift`) and to a larger lifetime context (the `_reAb` lemmas, `Frontend/Check/TLife.lean`).
`TDerivesAt.lendCell_kind`, `TDerivesAt.lendScope_rel`, `TDerivesAt.litView_shape` and
`TDerivesAt.unfoldStep_shape` state that a derivation fixes each.

What is not pinned is stated in `Frontend/Check/TFacts.lean`: that the cell is freed at run time
where `rel` says; whether a resumption point lies between a lend and its release; that a literal
view's table is a literal's bytes; an `f` that reaches a `nuEta` node other than from such a
`bind`; that a location holds only its class's types at run time, and which allocation a `swap`
node's location comes from.

### Consumers

The checker's other readers see through the new nodes where they read the node under them: the
clause classifier's paths (`onPaths`, with `onPaths_sound`) and Backend2's conversion
(`transparent?`, `machNode`, `convK`, `convWork`, `convWorkK`).

### Baseline

`CDerives`, the relation, FP, adequacy and every borrow guarantee are unchanged. Every program's
erasure and Backend2's LIR are byte-identical on the corpus; every golden and count is unchanged.

### Open

- Backend2 reads the facts (#712, part C): frame slots from `rel`, the lend's kind on `Op.lend`,
  literal views from `litView`, widths from the allocation's class carried with the location,
  `nuEta` from the binder's `unfoldStep`.

---

## 58. Entry 57 — Backend2 reads the facts (#712, part C)

### Motivation

§57 put in the typed term the facts Backend2 rebuilt from its LIR. This entry makes Backend2 read
them and deletes the passes that rebuilt them (`Backend2/Frames.lean`, `Backend2/LitViews.lean`),
which miscompiled five checked programs (`docs/compiler.md` §10).

### Language

No change to a type, rule, term, typing, elaboration, semantics or erasure. Backend2's LIR
changes (`Backend2/Syntax.lean`): `Op.alloc cls` and `Op.allocLent s cls` carry their width
class, `allocLent` its lend scope `s`, `Op.lend m` its kind; a program carries its static cells'
classes, the literal tables' code and its frame slots (`Prog.statics`, `lits`, `slots`).

### The reading

- **Frame slots.** A `lendScope` node whose `rel` holds numbers its scope; its cell's
  `allocLent` carries the number, and the `letpair` that takes the lend's pair apart marks its
  owner (`withScope`, `markOwner`, `Backend2/Convert.lean`). The conversion places parts of a
  scope's code in functions of their own (closures, joins, a machine's points), so the cell is a
  frame slot where the function that allocates it binds the owner and uses it only as the operand
  of `free` (`slotsOf`, `Backend2/Driver.lean`): every path of that function frees it there, the
  LIR consuming each variable once on every path, which `Lint.lint` now checks of every program it
  compiles (`flatOf`). `Lower` places the cell in the frame and ends the slot at that `free` (by
  the owner's variable, `Prog.slots`), and nowhere else.
- **Widths.** A value in a cell takes the bytes of its own type (a byte at `u8`, four at `i32`
  and `f32`, else its words), so a cell is read and written by its contents' type wherever it is
  reached. An allocation reserves the most bytes of its width class (`Checked.classAt`, written
  by `Convert` on `Op.alloc`); a capability's cell, which no `alloc` node allocates, gets the class
  the checker's construction gives its contents (`cellClasses`, checked closed by `cellsOkB`). An
  allocation of no bytes is the address `0`, which every target's `free` skips (the flat IR's
  interpreter now too). No width is chosen by a class lookup at a pointer.
- **Literal views.** A `litView` node's tabulation is `Op.tabLit`; `Lower` points it at the
  literal's bytes where the closure flow finds the tabulator to be the literal tables' code alone
  (`Prog.lits`), and reads the environment of that code.
- **Lend kinds.** `Op.lend m` is the borrow constant's kind; `Lint` checks the borrow it answers
  is of that kind.
- **`unfold step`.** A `bind` marks its variable where its bound computation is an `unfoldStep`
  node; the mark goes with the slot's variable as the conversion renames it.

### Programs

`corpus/lend-owner-returned.bc`, `swap-cell-width.bc`, `literal-array-written.bc`,
`capability-swap-width.bc` and `lend-owner-joined.bc` (#712's `t4`, `t7`, `t13`, `t17`, `t18`)
agree with the source at the LIR, the word IR, Wasm and natively. The old backend refuses
`capability-swap-width.bc`, which is marked so (`-- check: old-backend-refuses`,
`scripts/compile-corpus.sh`).

### Baseline

No change to `CDerives`, the relation, the checker or the old backend's output. Every golden is
unchanged; Backend2's counts are unchanged.

### Open

- `!` is not on the LIR's types: `Lint` cannot check that a copied variable is persistent. Closed
  by §59.
- That a location holds only its class's types at run time is not proved (`TFacts.lean`).

---

## 59. Entry 58 — `!` on the LIR types (#714)

### Motivation

`Types.ofV` erased `!`, so `Lint` could not check that a copied variable is persistent, and
`Layout`'s `trivial` (copying or consuming a cell, a borrow or a family is its words alone) rested
on the conversion's copies and consumes alone (`docs/compiler.md` §10). `!` is a fact of the checked
type; this entry carries it to the LIR and has `Lint` read it.

### Language

No change to a type, rule, term, typing, elaboration, semantics or erasure. Backend2's LIR
changes (`Backend2/Types.lean`, `Syntax.lean`): `LTy` gains `bang`, `!A`, which `ofV` keeps
(`ofV_bang`).

### The reading

- **Representation.** `!A` is represented as `A`. Every decision about a value's representation
  reads its type through `LTy.peel` (its top-level `!`s removed): its layout, its words, which
  closure it is, the conversion's taking apart of a pair, a sum or a closure type. Where the
  conversion compares two types (an outcome's, a machine's state, a site's closure types, a width
  class's keys), it compares them with every `!` erased (`LTy.sameRep`, `LTy.unbang`;
  `sameRep_iff`, `sameRep_bang_left`, `sameRep_bang_right`). A `use` body's and a consume's
  keys keep `!`: a key fixes the LIR types of what it converts.
- **Copies.** Every `copy` carries its rule (`CopyRule`), and `Lint.copiesAt` checks its premise:
  a split's `dup` at a persistent LIR type (`LTy.persistent`, `VTy.persistent`'s image, and what
  `clone` copies); the `copy` and `array_copy` constants and the derived copy (`copy_derives`) at
  an `imm` borrow or a family of them. `ofV_persistent`: a persistent type's LIR type is
  persistent, so a slot the masks duplicate passes (`Lint.copyable_ofV`).
- **Consumes.** Every `consume` carries its rule (`ConsumeRule`), and `Lint.consumesAt` checks its premise
  (§12, *Every insertion site cites its rule*): weakening at a persistent type
  (`Ctx.DeadP.weaken`); a `release` constant at a borrow, `Unk` or `[Imm A]`; a consume's leaves,
  `[Mut A]` among them (`Consumable.arrayMut`), in a consume function only (`Prog.consumeFns`); a live
  slot no mask holds at a persistent type (the weakening its part applies at its leaves). A
  superseded raise payload is abandoned, not consumed, at a type with no owned cell (`LTy.consumes`,
  `VTy.OwnFree`'s image; `ofV_consumes`). The one exception is a stack machine's consume
  of a level's suspended computation, whose state is on the task stack: a closure, which no type
  lets a term discard, at the rule `stackK`, a hand-over whose premise `Lint` reads from the node
  (§52, *The hand-over*).
- **`trivial`.** A copy or a consume the conversion makes is `Lint`-checked by the variable's type,
  so an owned `Ref` or array is never copied or consumed by `copy`/`consume` outside a `!` (which owns
  nothing, `bang_owns_nothing`) on a program that compiles.

### Programs

`Backend2/LintTests.lean`: `Lint` refuses a copy of an owned cell, a linear closure, a `mut`
borrow, a family that owns its cells and a pair holding a linear closure, and a consume of an owned
cell, a linear closure and such a family; it accepts the same copies and consumes under `!`, of
data, and of borrows. Every corpus program lints.

### Baseline

No change to `CDerives`, the relation, the checker or the old backend's output. Backend2's WAT and
LLVM IR are byte-identical on the corpus, its LIR identical but for `!`; every golden and count is
unchanged.

### Open

- That the LIR type of a variable the conversion makes is the image of its node's checked type is
  by construction, not proved; `Lint` checks each program it compiles, not the conversion.
- A stack machine's consume of a level's suspended computation is not checked by a type (§52, *The
  hand-over*).

---

## 60. Entry 59 — the `fold` block: arms whose recursive fields arrive folded (#718)

### Motivation

`docs/data-declarations.md` §11.1 A2, decided 2026-10-20. A declared recursive type (§42) is
taken apart by `match`, and a recursion over it through a borrow is §6's fold, `fold_imm`, whose
bracket arguments (the shape, the result) and algebra type (`A_R`) the program writes by hand,
its algebra a `case` on `inl`/`inr`. The `fold` block writes the algebra as arms with the
declaration's constructor patterns, in which each recursive field is already the fold's result
on it. The spelling is typed elaboration §5.3's and §6.2's (draft 0's fold block,
`docs/surface-cbpv.md` §2.7). Every rule is sugar into §6's three constants: no type former, rule,
constant or derived form is added, so `fundamentalC` and `adequacyC` cover every program a fold
block elaborates to (§42's argument).

### The form

    fold_imm e { p₁ -> M₁ | … | pₙ -> Mₙ }      fold_own e { … }      fold_reuse e { … }

A value. The patterns are §42's. `fold_imm[…]`, `fold_own[…]` and `fold_reuse[…]` with brackets
are the constants, unchanged: the parser reads the block when no `[` follows the keyword.

### F1: the fold

Let the arms' constructors be of the declaration `N` (the first constructor pattern at the top
of an arm names it; arms with none, over a `μ` written in core, are the algebra's own `case`s on
`inl`/`inr`, compiled as §42's draft-0 patterns are). `N` must be the root of a recursive group: a member that is not is refused,
"`fold_k` folds the root of a recursive group, and `N` is not its group's root `R` (the
single-root rule): fold `R`", and a declaration that is not recursive, "`N` is not recursive, so
it has no fold: match it". Then, with `x` fresh,

    fold_imm e { … }   =  (unbang fold_imm[T, 'y, top, R] (!thunkv Fun 'y < top.
                             return (thunkv fun (x : A_R) -> M))) ['a] e        e : imm 'a (μX. T)
    fold_own e { … }   =  (unbang fold_own[T, R] (!thunkv fun (x : A′_R) -> M)) e     e : μX. T
    fold_reuse e { … } =  (unbang fold_reuse[T, R] (!thunkv fun (x : A″_R) -> M)) e   e : μX. T

- `e` is of `N`'s type: a value of another type is refused, "the arms of this `fold_k` block are
  `N`'s constructors, but it folds a value of type `T`" (`e`'s type matched against `N`'s, its
  parameters placeholders, as a field's receiver is, §42 *Fields*).
- `T` is the body of `e`'s `μ`, its variable `X`; `R` is the type expected of the block. A block
  whose type nothing gives is refused, "the type of the `fold_k` block's result is not determined
  here: ascribe it", as a closure's parameter is (§42 types a block's arms by its result, not its
  result by its arms).
- `A_R`, `A′_R` and `A″_R` are §6's, computed by the kernel's own functions of the shape
  (`FShape.res`, `resO`, `resR`).
- `M` is the arms compiled by §42's match compiler (M1–M4) over `x`, with its reports ("this
  `fold_k` block is not exhaustive: …"), except that `x` is the root already unrolled, with the
  recursive positions folded:
  - the root's constructors are tested on `x` as `case x` (not `case (unroll x)`), and nowhere
    else: a constructor of the root below the top of an arm is refused, "in a `fold_k` block a
    recursive field is the fold's result on it, and matching the fold's result with a constructor
    of `N` is not provided: bind it with a name" (also when `R` is `N`'s type, as in a constant
    folding of an expression);
  - below a block of the group (§42, *Recursion*), a recursive field (one whose type is the root)
    is the fold's result, `R`, and in `fold_reuse` the pair `(c, r)` of the emptied cell
    `c : ref 1` and the result; it is matched as a value, not a cell. The block's other fields
    are its cells, `ref A`, in `fold_own` and `fold_reuse`, and their views, `imm 'y A`, in
    `fold_imm`, where a pattern below one is refused ("bind it with a name, and read it with
    `*`");
  - `box C(p, …)` of a block of the group frees the block's cells that are not recursive
    positions and matches their values (`fold_own`, `fold_reuse`; the kernel's fold frees the
    others); in `fold_imm` it is refused, the block being read through views;
  - a variable that binds a constructor's whole value binds it rebuilt from the parts the tests
    took apart, at the type of the occurrence it was taken from, a part of `A_R` (`A′_R`, `A″_R`):
    not rolled or ascribed `N`, but ascribed that type by the typed pass (`VSugar.like`), at the
    root and at any other member of the group (`corpus/data-fold-whole.bc`).
- One arm whose pattern is a variable is the algebra's parameter itself.
- The arms are the body of the algebra, a `!` function, so they assign no enclosing `let mut`
  variable: "the arms of `fold_k` are its algebra, a `!` function: they cannot assign `x`"; and
  they use no variable of the enclosing body whose type is not `!` (§2: `!` promotes only over `!`
  types): "the arms of `fold_k` are its algebra, a `!` function, which holds only `!` values:
  they cannot use `k`, of type `A`; fold to a function that takes it instead". A `!` value, a
  function parameter of type `!(A => B)` say, may be used (`corpus/data-fold-bang.bc`).
- `fold_imm` folds an `imm` borrow and `fold_own`, `fold_reuse` an owned value; the other is
  refused, naming the fold that takes it. A place lent to the fold, `fold_k &x { … }`, is refused
  as not provided (*Open*).

The single-root rule makes the root the group's one `μ`, so a fold over a group is the root's,
and its other members are matched inside the arms as parts of the shape (`corpus/data-fold-forest`,
`corpus/data-fold-group`). A recursion nested in another recursive declaration (B14) has no
`FShape` and is refused at its declaration, as before.

### F2: a block reassembled from its cells

In an arm of a `fold_reuse` block, outside any `fold_imm` or `fold_own` block in it, a block's
constructor written without `box`, `C(e₁, …, eₖ)` or `N { f: e, … }`, is the block reassembled
from the cells `eⱼ`: E1's form, `inj_i (e₁, (…, eₖ))`, rolled when `N` is the root and ascribed
`N` when `N` has no parameters. Nothing is allocated. The typed pass checks that each `eⱼ` whose
type it knows is a cell (`VSugar.cells`), and otherwise refuses with E3's hint: "`C` builds a
block, one cell per field, and this has type `A`: allocate it with `box C(…)`, or reassemble it
from the emptied cells of the `fold_reuse` arm"; the kernel checks that each is a cell of the
field's type. Everywhere else such a constructor is refused by E3, asking for `box`.

### A1

A fold's recursive positions are unordered (§42, *Folds: unordered positions*). The algebra's type
is `!U(A ⊸ F R)` at the empty row, so no arm may perform an effect. As for any `!` closure, an arm
that does is refused by the elaboration of effects (§18: an operation "performed inside a closure
or block that is not run in place") in a declaration reachable from `main`; a declaration that is
not reachable is not elaborated for its effects.

### Programs

| program | what it shows | answer |
|---|---|---|
| `corpus/data-fold-block.bc` | a tree summed through a borrow by a `fold_imm` block | `i32[6]`, `live 0` |
| `corpus/data-fold-list.bc` | a list traversed (`fold_imm`), mapped in place (`fold_reuse`, F2) and consumed (`fold_own`) | `i32[64209]` |
| `corpus/data-fold-tree.bc` | a tree traversed, mapped in place (`fold_reuse`, F2) and consumed with a `box` pattern | `i32[40506]` |
| `corpus/data-fold-forest.bc` | `Rose`/`Forest`, folded at the root `Forest`; `Rose` matched in the arms; mapped in place | `i32[144]` |
| `corpus/data-fold-group.bc` | `Expr`/`Bind`: a block of the group that is not the root, its recursive cells folded | `i32[1714]` |
| `corpus/data-fold-generic.bc` | a fold block over `List[T]` in a generic function | `i32[32]` |
| `corpus/data-fold-whole.bc` | a variable binding a constructor's whole value beside constructor arms, in each fold, at the root and at a member | `i32[2012014]` |
| `corpus/data-fold-bang.bc` | an arm using a `!` parameter of the enclosing function | `i32[6]` |
| `corpus/fail/data-fold-no-box.bc` | a block without `box` in a `fold_own` arm | refused (E3) |
| `corpus/fail/data-fold-not-root.bc` | a fold of a group's member that is not its root | refused |
| `corpus/fail/data-fold-nested.bc` | the root's constructor below the top of an arm | refused |
| `corpus/fail/data-fold-imm-box.bc` | `box` in a `fold_imm` arm | refused |
| `corpus/reject/data-fold-owned.bc` | `fold_imm` of an owned value | refused |
| `corpus/reject/data-fold-untyped.bc` | a fold block whose result type nothing gives | refused |
| `corpus/reject/data-fold-capture.bc` | an arm using an `i32` of the enclosing body | refused |
| `corpus/reject/data-fold-reuse-no-box.bc` | a block without `box` in a `fold_reuse` arm, its fields not cells | refused (E3's hint) |
| `corpus/reject/data-fold-other-decl.bc` | a `List` folded with `Tree`'s constructors | refused |
| `corpus/reject/data-fold-lend.bc` | `fold_imm &l { … }` | refused, not provided |

The fold blocks of the first six programs are written out with the constants beside them
(`corpus/sugar/data-fold-*.lowered.bc`, `scripts/check-sugar.sh`): the two erase to the same term,
so their counts are equal, at both backends.

### Baseline

No change to `CDerives`, `Core/`, `Paper/`, `Support/`, the relation, the machine, the checker or
either backend. Every program that was accepted elaborates as it did (the constants with
brackets parse as before; §42's match compiles as before outside a fold block): every golden,
exit status, `corpus/counts.expected`, `counts-backend2.expected`, `kernel-counts.expected` and
`cells.expected` entry is unchanged; the new programs get rows.

### Open

- **The result from the arms.** `R` is the type expected of the block; it is not synthesized from
  the arms (an arm's type may depend on `R` through the recursive fields).
- **`fold_imm &x { … }`**, a fold through a borrow of an owned place lent to it, as a call's `&x`
  argument is (§11): not provided, and refused as such ("`fold_imm &x { … }`, a fold of a place
  lent to it, is not provided (SPEC §60, Open)"); the fold takes a borrow.
- **Arms that use the enclosing body's values** that are not `!`: refused (F1). Folding to a
  function of them, `R = A => R′`, passes them in.
- The fold exported to clients as an observation the type chooses to give (A2's second half)
  comes with faces (U2); data unfolds (A3) are later.

---

## 61. Entry 60 — the owned fold and the consume at the class `P` (#722, U1 of #595)

### Motivation

§6's folds and §12's consumes are defined for `μ` bodies in the class `FShape`, whose leaves
are closed. A node that owns an array of its children (`μX. array i32 + array X`, AWFY's Storage;
`μX. buf i32 * buf (1 + X)`, a B-tree; `μX. bool * array (1 + X)`, a trie) or a `μ` nested inside
another (`μX. I32 ⊗ Array (μY. 1 ⊕ (Ref X ⊗ Ref Y))`) is outside it, so it is not consumable, and
a program that lets one go unused is refused. The design pass (#595, agreed 2026-10-28; its §4)
gives one class `P`, one owned fold for every body in it, generated by recursion on the type, and
the consume as that fold at results `1`. U0 (#719, `experiments/NestedFold/`) proved the
traversal; this entry is the kernel constant, the consume, the checker, the elaborator's
arrays and both backends.

### The class `P`

`P d A`, at `d` type variables in scope (`Core/FoldClass.lean`):

| form | condition |
|---|---|
| a closed type | a leaf, whatever its former |
| `tvar i` | `i < d` |
| `A ⊗ B`, `A ⊕ B` | both in `P d` |
| `Ref S`, `Array S` (`[Ref S]`) | `S` in `P d` |
| `μB` | `B` in `P (d + 1)`, and its head is not a variable (`Hd`, which passes through `μ`) |

`X` under `Imm`, `Mut`, `!`, `[@a]`, `U` or a family that is not an array is outside it, as
before. `PBody B` (`P 1 B ∧ Hd B`) is decidable (`pBodyB_iff`), and every `FShape` body is in it
(`pBody_of_FShape`). A **key** is a binder the fold calls: each `μ` that is not closed, and each
array whose element type is not closed, keyed by the stack of the bodies above it
(`Bnd.mu`, `Bnd.arr`). `keys B₀` lists `μB₀`'s keys in preorder, the root first.

### The constant

    foldOwnG : Algs ⊸ !U(μX. T ⊸ F R₀)        T in P, any results R

`Algs` is the right-nested `⊗` of one algebra per key, in the order of `keys`
(`FoldP.algsTy`): `!U(T_b⟨R⟩ ⊸ F R_b)` at a `μ` key with body `T_b`, and
`!U(1 ⊕ (R_a ⊗ S⟨R⟩) ⊸ F R_a)` at an array key of element type `S`. `T⟨R⟩` (`FoldP.resO`) is
`T` with each key's result at its positions: a variable's binder's result, an inner `μ`'s result,
an array key's result, and `S⟨R⟩` under a `Ref S` that is not closed (the cell is freed). The
results are a list `Rs`, a key's the entry at its first position (`FoldP.algsOf`). The algebras
are passed at run time.

The term (`Core/FoldOwnGTerm.lean`) is one Z combinator whose body dispatches on the tag of the
key it is called at, Bekič's simultaneous fixed point (decision 59's shape). A key's traversal
is generated by recursion on its body, one action per former: a closed leaf is passed; a
variable or an inner `μ` is the call of its key; `⊗`, `⊕` componentwise; `Ref S` frees the cell
and traverses `S`; an array is a `count` loop (§16) that moves each element out of its slot
(`swap` with `()`), traverses it and steps the array key's algebra, a left fold from
`inj₁ ()`, and then `drop`s the emptied array, its buffer at once.

### Soundness

`foldOwnG_compatX` (`Core/FoldOwnG.lean`) is the rule's semantic typing, the CDerives rule
`foldOwnG` its use (`Core/Fundamental.lean`), mirrored in `CDerivesAt` (`Core/Tied.lean`) and
`CDerivesP` (`Core/PinDerives.lean`), with a case in each induction over them. The proof is
U0's, with the algebras taken out of the tuple: `trav_spec` is induction on the position
`A ∈ P`, one case per former, given every key's call below the measure `(cells, value size,
rank)` lexicographically; `hs_all` is strong induction on that measure; `fold_spec` is the fold
of `μB₀` at every body in `P`. The measure consumes at every call: after `⊗`/`⊕` the value is
smaller (a body's head is not a variable), after a cell or an array slot the resource is
smaller (`dsize_tail_lt`), and at an inner `μ`, at the same value, the body is.

### The consume

`consumeAt true A` is the consume of `A⟨1⟩`, `A` at results `1` (`algE_eqP`). `Consumable.mu`
(`Core/Consume.lean`) is restated at `P`: the body is in `P`, `T⟨1⟩` is consumable, and so has
every key's body (an array key's element type) at `1`. At a body in `FShape` (`fshapeB`) the
consume is `foldOwn` with the algebra `T[1/X]`'s consume, the same term as before, so every
existing program's consume, run and counts are unchanged; at any other body of `P` it is
`foldOwnG`, its algebra at a `μ` key the consume of the key's body at `1` and at an array key
the consume of `1 ⊕ (1 ⊗ S⟨1⟩)` (`keyAlg`, listed by `algsIn` in the order of the keys,
`algsIn_eq`). `consume_wf` types it from the consumes of those types; `Consumable.muF` is the old
constructor's hypotheses. The checker's `consumableAtB` mirrors it (`Frontend/Check/Steps.lean`):
`consumableAtB true A` decides `A⟨1⟩` and every key inside `A` in one recursion (`AlgConsume`,
`consumableAtB_soundA`).

### Declarations

§42: a declaration's recursion is accepted exactly when its `μ` body is in `P`, decided by the
kernel's `FoldP.PB` and `pBodyB` (`Frontend/Elab/Data.lean`, `pClass`), not by a predicate of the
elaborator's own. The body is read with each application of a non-recursive declaration opened to
its structure, and each application of a non-recursive `type` abbreviation to its body, at their
type and lifetime arguments, under every value former (`openX`), and mapped to the kernel type `P`
reads (`pTy`): `X` its index, each former the kernel's, a subterm without `X` the leaf `1`. That
map is marked `UNPROVED:` at the site: it assumes `P` reads no lifetime, that a closed subterm may
stand for any other (`P_of_closed`), and that a type the table does not open, a type parameter, is
closed once elaborated.

The table the parser and the typed elaboration read holds the abbreviations in scope beside the
`data` declarations (`Data.Table`). Both take their abbreviations from one function,
`Parser.tableOf`: those of the modules the program's `include`s name, read in the pass that reads
the declarations, then the program's own, a later abbreviation of a name hiding an earlier one, so
they agree on which constructors are blocks. The prelude's `data` declarations are in the table
and its abbreviations are not (it declares none, which `scripts/check-hygiene.sh`
checks), so a program that includes no module has its abbreviations without
reading the library: the kernel evaluates the cross-checked programs' elaboration
(`Frontend/Check/CrossCheck.lean`, `declTxn_checks`), and cannot read a module, whose source is read
when `bcc` starts (`Sugar.libSources`, an `opaque`). The I/O library the typed elaboration
brings in for a `main` that uses the streams ambiently (§34) is not one the program includes, and
is in neither table.

An abbreviation's body is read through wherever a field's names are: the group of a declaration
is found through the bodies of the abbreviations its fields name (`type JMap = Map[string, Json]`
with `Obj(JMap)` makes `Json` recursive), and an abbreviation that names a member of the group, in its
arguments or its body, is opened at the field before the members are substituted
(`Data.openMembers`), so no `type` or `shape` declaration of the group names one. A `type`
declaration whose body names a `data` declaration written after it is placed after that
declaration's group, in the order written. An abbreviation is
recursive when its body, with the abbreviations it names opened, has a `μ`; one around `X` is
refused before it is opened (U3, below), so the opening substitutes into a body that binds no type
name, and `X` is chosen apart from every name an abbreviation writes, so it neither captures nor is
captured.

So an array is a recursive position with no `box` (data-declarations §6.11): its recursion is
under the array's allocation, and a constructor whose recursion is only under arrays and cells is
not a block. `data Tree = Tip(i32) | Node(i32, array Tree)` is `μX. i32 ⊕ (i32 ⊗ Array X)`;
`data Trie = Trie(bool, Vec[Option[Trie]])` is `μX. bool ⊗ (Array (X ⊕ 1) ⊗ i32)`, Rust's
`Vec<Option<Trie>>`; `Node(array (i32 * T))` is `Array (i32 ⊗ X)`. An abbreviation is read the
same way: `data Json = Null | Num(i32) | Obj(Map[string, Json])`, `Map` the abbreviation of
`lib/map.bc`, is `μX. 1 ⊕ (i32 ⊕ ((Array (1 ⊕ (i32 ⊗ string)) ⊗ Array X) ⊗ i32))`, and `Obj` is not
a block; `Pair[T]`, `type Pair[A] = A * A`, holds `T` bare, and a constructor of it is. A block's
cell may hold the root inside another type (`tail: Option[List]`, `ref (X ⊕ 1)`). `box` is still
asked for where the recursion is bare (a block), which is where a layout would be infinite;
`box C(…)` of a constructor that is not a block is E2's cell holding the value, and where its
value's type is expected the typed elaboration says so. A field outside `P` is refused at the
declaration, the message naming the former that puts it outside (a borrow, `!`, a lifetime box, an
array of borrows). A recursive declaration or abbreviation around the root (`List[T]`,
`type L[A] = mu X. …`, `Queue[T]`) is refused, naming it: its `μ` would mention the enclosing
variable, which the checker refuses (U3).

**The filler** (§17, design §5.4) of a buffer's unused slots is computed structurally
(`Frontend/Sugar.lean`, `fillerOf`), under §6's stack of binders: `0`, `()`, componentwise at `⊗`,
the first summand that has one at `⊕`, the empty view at a borrowed family, **the empty array**
at an owned one, the constant function at `!(A ⇒ B)`, and at `μB` the filler of `B` with the
`μ`'s own variable having none (the least fixed point's first approximant), rolled. The empty
array is the constant `array_empty[A] : Array A` (§9), the empty family `(0, 0)` that
`famEmpty_compatX` already types at every leaf, here at `Ref A`: the CDerives rule `arrEmpty`
(and `CDerivesAt`'s, `CDerivesP`'s, the typed term's), whose soundness is `arrEmpty_compatX`.
`array_new` at length 0 needs a function to an element, so an element type whose only finite
values are built from empty arrays (`data Tree = Tree(i32, Vec[Tree])`, `μX. Array X`) had no
closed term without it. So `Json`'s filler is `Num(0)` whichever constructor is first, the rose
tree's is `Tree(0, [])`, and `box buf[Tree](0)` is an empty buffer that allocates nothing. A type
with no finite value (`μX. i32 ⊗ X`) has none, and the message says so. The filler's typing is
the checker's; that one is found at every type with a finite value whose leaves have fillers is
`UNPROVED:` at the site.

### Lowering

- **Backend2**'s consume was already generated by type (`genConsume`), and it covers `P` as it
  stands: one function per closed `μ` type the value unrolls to (an inner binder, which names the
  outer one, is its own function calling the outer's), and one loop function per array that
  destroys each element and then frees the buffer once. This entry documents it, marks that it is
  read off the `consume` node's type and not compiled from `consumeE`'s term (`UNPROVED:` at the site),
  and gives `foldOwnG` its arity (`constArity`). `array_empty` is the empty family
  (`emptyFam`).
- **The old backend** compiles `consumeE`'s term: the native fixed point whose body is the `case`
  on the key's tag, each key's traversal a code of its own, the array's `count` loop of tail
  calls, the buffer freed once by `drop`. Calls are direct and nothing is allocated. Its closure
  IR's interpreter frees the one cell `tab` places at length 0 only when the base is not null:
  `array_empty`'s `(0, 0)` holds none.

### Programs

| program | what it shows | answer | allocations (Rust's) |
|---|---|---|---|
| `corpus/storage-array.bc` | AWFY Storage in natural form, a tree of arrays, no hand-written consume | `i32[5461]` | 5461 (5461) |
| `corpus/btree-boxed.bc` | a B-tree whose nodes own buffers of keys and children, CLRS insertion of 200 keys | `200 0 4`, `i32[200]` | 77 (77) |
| `corpus/leetcode/trees/0208-implement-trie-boxed.bc` | a trie whose nodes own arrays of their children | the arena form's answers, `i32[4]` | 58 (58) |
| `corpus/data-array-tree.bc` | a `data` tree recursive under an array, with no `box` | `i32[12]` | 4 |
| `corpus/data-json-vec.bc` | `data Json = Num(i32) \| Arr(Vec[Json])`, no `box`; a buffer of `Json` with the filler `Num(0)` | `i32[10]` | 6 |
| `corpus/data-json-map.bc` | `data Json = Null \| Num(i32) \| Obj(Map[string, Json])` through the abbreviation `Map`, no `box`; nested objects, some consumed implicitly | `i32[73]` | 39 |
| `corpus/data-set-rec.bc` | `Node(Set[i32], Map[i32, Tree])`: `Set` left closed, `Map` opened | `i32[453]` | 12 |
| `corpus/data-abbr-nested.bc` | `Node(Bag[T])`, `type Bag[A] = Map[i32, Pair[A]]`: an abbreviation inside an abbreviation | `i32[7]` | 4 |
| `corpus/data-abbr-root.bc` | `type JMap = Map[string, Json]` before `data Json = … \| Obj(JMap)`: the abbreviation's body names the root | `i32[83]` | 39 |
| `corpus/data-abbr-block.bc` | `Node(Pair[T])`, `type Pair[A] = A * A`: bare, a block, with `box` | `i32[15]` | 6 |
| `corpus/reject/data-rec-abbr-list.bc`, `data-rec-abbr-mu.bc`, `data-rec-abbr-nested.bc` | a recursive abbreviation around the root | refused (U3) | — |
| `corpus/reject/data-box-not-block.bc` | `box Obj(m)` where a `Json` is expected | refused: not a block | — |
| `corpus/data-rose.bc` | #32's rose tree, `Rose`/`Forest`, `kids: box Forest` | `i32[16]` | 14 |
| `corpus/data-eval.bc` | #32's `Tm`/`Val`/`Env` evaluator, `ECons(Val, box Env)`, copies by hand | `i32[42]` | 10 |
| `corpus/leetcode/trees/0208-implement-trie-vec.bc` | the trie as Rust's struct, `data Trie = Trie(bool, Vec[Option[Trie]])`, no `box` | the arena form's answers, `i32[4]` | 58 (58) |
| `corpus/data-rose-vec.bc` | `data Tree = Tree(i32, Vec[Tree])` built from empty buffers (filler `Tree(0, [])`); `data J = Arr(Vec[J]) \| Num(i32)`, the array constructor first (filler `Arr([])`) | `i32[19]` | 5 |
| `corpus/data-option-block.bc` | a block whose cell holds the root inside an option, `tail: Option[List]` | `i32[6]` | 12 |
| `corpus/filler-mu.bc` | buffers of `μX. Array X` and `μX. i32 ⊗ Array (Array X)`, filled by `roll []` and `roll (0, [])` | `i32[3]` | 3 |
| `corpus/reject/filler-no-finite-value.bc` | `filler` at `μX. i32 ⊗ X` | refused: no finite value | — |
| kernel program `nested-fold` (`Core/NestedPrograms.lean`) | `μX. I32 ⊗ Array (μY. 1 ⊕ (Ref X ⊗ Ref Y))`, three keys deep: built, summed by `foldOwnG`, consumed implicitly; typed (`nestProg_derives`), run (`nestProg_runs`, `nestProg_eval`) | `i32[34]` | 14 |

Every stage of both backends prints each program's golden and `live 0`. Rust's counts are the
programs ported with the same containers and capacities
(`docs/expressiveness-probes/zero-cost/awfybg/rs/src/bin/storage.rs`, `btree_boxed.rs`,
`trie_boxed.rs`; `run.sh`); `trie_boxed.rs` is the Rust of both trie programs (its
`Vec<Option<Trie>>`). The last two of #32's programs already worked under the single-root
rule.

### Baseline

`fundamentalC` and `adequacyC` cover the new rules (`foldOwnG_compatX`, `arrEmpty_compatX`);
`fundamentalC_pin` likewise. No change to the relation, the machine, `Paper/` or `Support/`. The
consume of a `μ` in `FShape` is the term it was, so every golden, exit status,
`corpus/counts.expected`, `counts-backend2.expected`, `kernel-counts.expected` and
`cells.expected` entry is unchanged; the new programs get rows. The checker accepts a superset of
what it did, and so do declarations: `corpus/reject/data-field-box.bc`'s `tail: Option[List]` is
in `P` and runs (`corpus/data-option-block.bc`); the reject is now a field under a borrow
(`data-field-borrow.bc`).

### Open

- **The borrowed fold** at `P` (U2), the frontend's inner `μ` (U3, B14 and the check that a core
  `μ` type is closed), reuse (U4) and mutual groups with no root (U5).
- **A user-visible `fold_own` at `P`**: the constant is the kernel's and the consumes', not the
  surface's; `fold_own[…]` and the fold block (§60) stay at `FShape`.
- **`FShape`'s constants are not retired** by this entry: the old backend compiles `fold_own`'s
  and `fold_reuse`'s step by pointer reversal, recognizing their term (`Backend/README.md`,
  *Stack*), and the consume of an `FShape` body keeps their term so that its counts and stack
  behaviour stay.
- **Per-key functions in the old backend**: it keeps the dispatch inside one code. A deep
  structure recurses on the native stack there, as a non-linear `fold_own` does.
- **Declarations refused by the checker, not by `P`**: a recursive type under a function type is
  a leaf of `P` (`U C` is closed for it) and the checker refuses the `μ` variable under `U`; a
  recursive declaration or `type` abbreviation around the root is a `μ` mentioning the enclosing
  variable, which the checker refuses (U3): the elaboration refuses it before opening it, naming
  the declaration or abbreviation the field writes. Both refusals name their cause.
- **A filler at a block's cells**: a mutual group through `Vec` whose member is a block
  (`Obj(Vec[Pair])`, `data Pair = Pair(i32, Json)`) has none: a filler of a cell would allocate.
  Mutual groups are U5.
- **The filler's completeness** (`UNPROVED:` at `fillerOf`) and **the declaration check's map to
  the kernel type** (`UNPROVED:` at `pTy`) are not proved; the filler's typing and the class's
  decision are the checker's and the kernel's.

---

## 62. Entry 61 — the new Core: linear resources and borrows across exits and suspensions (#771)

**Status: design, partly built.** This entry is the target of the series #771–#775 (and its later
issues). Each part names the PR that lands it. Nothing here changes `CDerives` until those PRs
land; until then the checker enforces the rules of §14, §19 (T1), §29 and §32 as stated there.
Evidence for each part comes from the #770 spikes and is cited by the name of the Lean result
(`docs/new-core/evidence.md`).

### Motivation

Linear values meeting non-local exits and suspensions broke the language (#769, #743). Closing a
file is the file effect's API in the library, not kernel work (decision 73); what the kernel lacks
is a way for a program to keep such a linear value live across those points and consume it itself:
- `[then]` gives the body and the finaliser disjoint contexts, so a finaliser cannot consume a
  linear value the body holds.
- `[let]`'s side condition `hW` refuses an owned value that is not consumable and is live across
  an abortive point.
- A linear value that is not consumable cannot be a loop's state when the loop is closed early.
- No borrow may be held across a suspension whose handler stores the continuation (T1, §19).

The cause is structural. Core's lifetimes form a single chain and its frames nest last-in-first-out.
A stored continuation, resumed later under frames its handler opened in the meantime, makes the
program's lends nest as a tree (argued). #770's evidence is two configurations at typed worlds
where the single chain's reading fails (`resume_frame_short`, `not_fdFromLifetimeTypes`); neither
is shown reachable from a program.

### The target theorem

For every closed, well-typed program `P`:

> every configuration a run of `P` reaches is a value or steps; a value is reached only at the
> empty memory; every `free` finds its cell.

The theorem sees memory only: a host resource counts as closed only if its handle owns a cell
and its type is linear with `close` its only eliminator. Divergence is allowed, and termination is
not claimed. This is LinearActris's adequacy shape
(Jacobs, Hinrichsen, Krebbers, POPL 2024). It is stated as `OrDiverges`
(`Core/StepsN.lean`), and proved at one branch of the tree world (`topAdequacyT`). Over the chain
relation with Kripke stops it is proved for every closed program typed at `F 1` with its handlers
inside it, under the named assertion `HandlerLawN` (`goal791N`, *The named assertion* below). To be
proved by `fundamentalC` over every typing rule and adequacy, at one step-indexed safety relation. The existing total relation keeps the termination
results (`total_every_run`, `Closing`, `total_open`/`total_call`/`total_subrun`) for derivations
that use none of the new rules.

### Lifetimes ordered as a tree (#773)

Lifetimes form a well-founded cactus. A fresh lifetime is a child of the current branch's
innermost one, and siblings are incomparable. A graft whose capture point is above its resume
point adds order facts and removes none (`graft_mono`), so grafting a stored computation's branch
under a newer lend makes its lifetimes descendants of that lend (for example `graftEx_lt`).
Today's single chain is the case with one branch.

Every use of comparability in the closure scanned by `Tree/ChainUses.lean` (the printed lemmas
#770 asks about, `TW`'s and `TWNC`'s invariants, the relation's resource clauses) falls into one of
five classes (`Tree/Comparability.lean`), each with its Lean evidence:
1. **The carrier: strata and the cell operations.** `○` clause 3 needs one stratum holding both
   cells' strata, which cousins do not have (`cousins_no_common_stratum`); the antichain carrier
   below replaces it. `Res_{⊔ᾱ}` is read as the intersection of the members' strata, and `⊓ᾱ` at
   every member.
2. **A fresh lifetime `↓α`** is read as a covering child (`Cactus.Covers.le_of_lt`).
3. **A lifetime chosen below two bounds** exists on a branch (`exists_below_two`, `fresh_frameT`,
   `wp_I_frameT`).
4. **A lifetime below the whole world** (`TW.reb`'s `StratumLe W β` and its kin) does not exist
   for a world holding two siblings (`no_stratum_below_siblings`). These are replaced by premises
   read at one record (`RebRecLe`, `RebEndRec`, `RebCellLe` of `TWN`/`TWNC`).
5. **`⊓ᾱ ∈ ᾱ` used to get a member**: any member serves, and the use is read unchanged.

No printed lemma ported to the tree carrier (6.1–6.59 but 6.40 and 6.45) needs comparability. *Open*: two
uses outside the scan, neither restated: the interpretation of lifetime terms (row 2.54,
`@b₁ ⊓ @b₂` and `@b₁ ⊔ @b₂` as `max`/`min` on `ℕ`) and `LifeCtx.Models` (row 2.52).

### The carrier (#773)

Strata are indexed by finite sets of lifetimes, and `Res_S` is the intersection of the members'
strata. A combined `mut` cell carries an antichain: `mut(β̄₁) ○ mut(β̄₂) = mut(min(β̄₁ ∪ β̄₂), …)`.
`○`'s laws hold (`compLawsRT`). The chain instance is today's carrier: `chainEquiv` preserves and
reflects strata, `●` and `○`, and along it `✓`, `#` and flattening are the printed ones
(`chain_valid_iff`, `chain_hash_iff`, `chain_flat_iff`). A world valid before a graft is valid,
carried, after it (`ResUT.Valid.graft`).

### Typed worlds with canonical images (#781)

Each reborrow's image is the canonical one for its frame record and lifetime (one template per
record, relabelled in lifetimes only), for root and deep reborrows. Two readers of the same frozen
data then share witnesses. Each route tried that kept the choice (re-entry at the same image,
re-choosing the image, worlds by invariants) was refuted on the chain (`not_rebReentryAgreeN`,
`not_rebRelabelAgreeN`, `not_witSwapIWN`).

**Built over the tree world** (`Support/Model/Tree/World/`). `TWNT` is Core's `TW` over the tree
carrier, with store types as codes (`KTy`), the reborrow premises read at one record
(`RebRecLeT`, `RebEndRecT`, `RebCellLeT`), every reborrow's image the canonical one, and one more
constructor, `reread` (the tree grows, or a location no `mut` cell is at is re-typed). The images
are read through a template choice the world carries (`canonTc`, `canonDTc`, `TWd.tc`). Re-reading
carries the choice (`TcCarried`, `templAt_reread`, `templDAt_reread`, `TWNT.templ_reread`), a
carried choice exists (`TWNT.tcCarried_exists`, from `TWNT.tcCoherent`), and at the `Classical`
choice the images are one template per record (`canonTc_tmplT`, `canonDTc_tmplT`). Every `TWNT`
world satisfies the typed world's invariant (`twnt_invHolds`). No relation in the library reads
this world yet, and no rule uses its reborrow constructors across a stop.

On the chain, every result of the generated copy of Core builds over canonical worlds
(`canon-core` branch, namespace `Core.C`). The content is `C.fundamentalC` at `TWNC`;
`C.adequacyC` re-derives the library's statement from it. The demonic, pin, `Div` runtime and
cancel-runs results build there too. The two places the library chooses a reborrow's image are the
only proofs written by hand. `Core.Stdio` is not covered. This is evidence; Core's chain `TW` is
not made canonical, and Core moves to the tree world in a later PR of #771.

### Resource safety

**`resourceSafety`** (`Core/ResourceSafety.lean`) is `adequacyD` read over cells: for every closed
`CDerives` program at a persistent answer, every run from the empty memory, under every allocator,
continues to a value at the empty memory, and every `free ℓ` it reaches finds `ℓ` allocated. That
each allocation is freed exactly once follows informally (an allocation picks an unheld
location, `step1_alloc_iff`, a `free` removes the cell it frees, and the run starts and ends
empty); no theorem counts frees. `rtSafety` is a different statement, at the row `[tickSig]`
under the runtime's handler: progress and no double free, on terminating and diverging runs alike,
without leak freedom. The kernel guarantees that every linear value is used and that no memory
leaks; closing a host resource (a file) is the API of the resource's effect, encoded with
linear types in the library, not a kernel rule.

### The safety relation

A step-indexed linear weakest precondition with the following parts:
- **Exact ownership.** Each term owns an exact fragment of memory.
- **Capture is its own operation.** A stop is not read as a return: the stopped continuation's
  share keeps its branch's real cells and frame records (`crwpG`/`cerwp`).
- **The cactus invariant over all computations** (running, stored in a κ, spawned). Each owns its
  resources and frame records, pairwise disjoint. The design: it is preserved by step, capture,
  graft, unwind, spawn and join; adequacy is derived from that preservation; and the frame rules
  are instances of capture.
- **`[handle]` without `hdv`.** The handler rule is proved by induction on the index, with stored
  continuations around loops that never end (`ewp_handle`, `erwp_handle`).
- **Where κ resumes.** κ may resume at any extension Core's `Ext` allows (`extF`, `ext_extF`).

Evidence: `progStore_orDiverges`; borrows live across stops for `mut`/`imm` lends, reborrows,
deep reborrows, and the Anti-Frame (`erwp_M_frame`, `erwp_I_frame`, `erwp_reborrow(Deep)`,
`erwp_M_antiFrame`); a handler that lends its own cell and resumes κ inside it
(`HandlerLendProg`); cross-task scopes (`cerwp_scope`, `cerwp_scopeM`, which hold over any body),
tested by programs with one child and a fixed order of events (`CrossProg`, `CrossProgM`).
`CactusInv` (`reb-canon`) is stated, with `cactus_step`, `cactus_move` and
`joinReady_fd`, and not yet used: the cross-task programs are proved without it. **Built over the library's typed tree world** (`Core/StepsN.lean`, `Core/TreeWp.lean`,
`Core/TreeWpEff.lean`, `Core/TreeCactus.lean`, `Core/TreeStepKeep.lean`, `Core/TreeHeadlines.lean`).
`twp` is the step-indexed relation at a world that grows: a run starts at any extension of its
world, from the re-reading of its resource, and ends at an extension of the start, the frame
re-read there and the start and end related by row 5.27's `↭` masked at the run's own records,
read along the walks (`EndT`, `UpdA`, #806): an `imm` cell may be given up to the end world while
another part holds a copy, and a `mut` cell is read through the `imm` cell it sits beneath
(`[TR]` 6.48's ancestor technique; `UpdA.frame`, `UpdA.trans`). A run gives up a copy of a view
another part holds (`twp_consume_view_framed`; a callee, `twp_frame_callee_consume`; a spawned
task, `twp_child_consume`, each at a frame condition holding a copy); the last copy is refused
(`twp_refuses_last_copy`), a lend does not end while another part holds a live copy
(`twp_refuses_lendEnd_live_copy`), and ends by `twp_lendEnd` as it stands once every copy is
back (`twp_lendEnd_after_framed_consume`). Its rules: downward closure, the Kripke rule, bind, the frame (`twp_frame`, and
`twp_frame_w`, whose frame obligation also reads the start world's invariants), world and resource
changes at a segment's start (`twp_extend`, `twp_update`), and row 5.27's `mut` clause at every end
(`endT_inv`). `cerwpT` adds operations: a stop at a non-abortive entry of the table leaves a
continuation share (`contShareT`), a Kripke wand resumed at any extension and any list keeping
the re-readings of the stop list's records the share reads (`KeepRel`, `contShareT_resume`; the
whole-list condition with `extFT` against it implies it, `contShareT_resume_ext`). `CactusInvT` is kept by a step, by tree growth, by moving a part
between branches, by spawn and by join (`cactusT_step`, `cactusT_extend`, `cactusT_move`,
`cactusT_spawn`, `cactusT_join`). Proved at one branch (`Core/TreeHeadlines.lean`):
- **adequacy** (`topAdequacyT`, `cerwpT_adequacy`): a closed program at `cerwpT` at the empty table,
  from the empty world, whose result holds nothing, is `OrDiverges`; derived through `cactusT_step`;
- **R1**, a step keeps every other branch's open lend (`r1_stepKeepsFdEsc`, `stepKeepsFdEsc`):
  this rules out a run that ends holding part of a lend of its frame. Without `↭` at `twp`'s end it
  fails (`not_stepKeepsFdEscNoUpd`): a branch ends with a copy of another's lent cell;
- **R2**, a lend is not ended while a stored branch holds part of it (`r2_endBlockedByHolder`): the
  lender's piece composes with no rest containing that branch to a valid world;
- **R3**, a join ends a shared lend only when the other branches hold nothing of it
  (`r3_joinEndNeedsFdEsc`); with `fdEsc_at_join` and `immEnd_valid_of_fdEsc`, the end is valid
  exactly when no other branch holds part of the lend. R2 and R3 rest on `fdEsc_of_end_valid`;
  `config_end_refused` places both at the configuration of `cactusT_config`;
- **R4**, a stored continuation is never refused at a resumption the tree world's own extension
  allows (`r4_extExtFT`, `ext_extFT`, `Support/Model/Tree/World/ExtExtF.lean`): at a share inside
  a tagged typed tree world, every list at which a typed tree world holds and which `ExtLT` allows
  (Core's `Ext` over the tree carrier: the records an `imm` cell of the share reads kept, and the
  records strictly longer-lived than a borrow cell of the share the same), `extFT` allows. A record
  frozen at depth is reached from a lifetime of the share's cell by a chain of the tree's order
  (the strata, then the root's `FrameLifeT`), so `ExtLT`'s lifetime clause is read on one branch.
  `extLT_admits_drop`, `not_extLT_drop_relevant` and `not_extLT_drop_longer` show what each clause
  admits and refuses.

**Over several branches** (`Core/TreeHeap.lean`, `Core/TreeHandle.lean`, `Core/TreeSched.lean`):
`[handle]` without `hdv` at `cerwpT` for a scheduler at the program's top (`cerwpT_schedHandle`,
by induction on the index), with `κ`'s cell, resume and cancel at `twp` (`twp_kappaCell`,
`twp_kappaC_resume`, `twp_kappa_cancel`, `twp_kappaC_cancel`) and allocation, freeing, load and
store at `twp` (`twp_alloc`, `twp_free`, `twp_load`, `twp_store`). A scheduler meets `SchedOKT`:
every operation of the tasks' table is its own, each continuation tag is its entry's qualifier, the
entry's resumer guarantee follows from the join's (`fdJoinT`), and its clauses hold at the empty
table, each `κ` read by `KapSchedT`: resumable beside a state the clause keeps when that state is
valid and holds nothing at the masks of the records the branch owns at its stop (`fdMask`; `FdEsc`
read at locations). `cerwpT Tb Q Fb F` carries a base frame condition `Fb`: a stop hands the table
`Fb`, so a continuation resumes at `fdAt en v Fb O′`, the base and its resumer's guarantee at the
records it owns at that resume, with nothing from earlier stops. A task may start owning records:
its present frame condition avoids them, its base need not. **Multi-branch adequacy** (`multiBranchAdequacyT`): `hnd H e₀` is `OrDiverges` for
every scheduler `H` meeting `SchedOKT` and every task `e₀` at its table (`SchedOKT` fixes neither
how many continuations a clause holds nor which it resumes); derived through `cerwpT_adequacy` at
one branch (`cactusT_step`, the running branch alone in `CactusInvT`). The stored continuations are
not branches of `CactusInvT`: `KapSchedT` (and `PoolTJ`, below) carries them through
`cerwpT_schedHandle`'s induction on the index. The invariant over them is in pool form, each share
resuming at `KeepRel` and each entry of the stack apart from those below it at their record masks
(`fdMask`, `recMask`) except at what its nearest joiner shares, with no branch points (decision
74), since branch points are not kept
along tree extension (`not_joinPtKeptT`) and locations are (`fdMask_mono`). The
task runs at any base and present frame conditions every valid frame meets (`⊤` among them): the
scheduler's state is in the resumed branch's frame, and a valid frame avoids the task's records
from their opening, so the task may end a lend it opened. A
stopped branch's clause knows its frame holds nothing of the branch's lends, those it opened
during the segment included (`twp_bind_fd`, `noneAt_recMask_end`). One program is proved through
the headline (`Core/TreeSchedProgs.lean`, `asyncProg_safe`): a scheduler that resumes a task beside
a state of its own, its cells owned rather than borrowed. For `pingpong-mut` the stepper each task
runs under meets `SchedOKT` (`schedS_ok`, its answers a step-indexed fixpoint) and both tasks are
proved; the relay that hands the borrow between them is not.

**The resume condition reads only the share's own lineage** (D13): `contShareT` and `KapSchedT`
resume at any list keeping the re-readings of the stop list's records the share is relevant to
(`KeepRel`, `Support/Model/Tree/World/ExtF.lean`); the whole-list condition implies it
(`keepRel_of_extFT`, `contShareT_resume_ext`), and a share is carried along `KeepRel`
(`contShareT_kripke`, `KapSchedT.kripke`).

**A stored continuation across another branch's run** (`Core/TreeResume.lean`,
`Core/TreePool.lean`): a run that owns no record at its start ends at a list holding the
re-reading of every record of its start list (`twp_keepsList`), so a `κ` held beside it
(`KapAtT`: captured at its stop, share and records re-read, the records its share reads kept) is
held at the run's end (`twp_keepsKap`) and resumed there (`KapAtT.resume`,
`kapAtT_resume_beside`). A runner that owns records, opens lends and ends lends of its own, those
open at `κ`'s stop included, keeps `κ` held when the two hold nothing at each other's record masks
(`twp_frame_keep`, `twp_keepsKap_sep`): a record `κ`'s share reads is in the lineage of a record
proper (`TIT`); not the runner's, since the share would then hold part of the runner's lend
(`relFT_not_fdEsc`), so the frame's, which `EndT` re-reads. The separation is kept both ways at the
end (`MaskDiff`; R1 by `fdEsc_of_updX`). At the scheduler's interface: `kapAtT_resume_keep`, one
stored task resumed beside another, the other held at the end. Where `κ`'s share holds part of the
runner's lend, R2 at the stored branch (`kapStored_end_refused`) refuses the runner's end of it.
`config_resumable_after_open`: at `World/Config.lean`'s world, a record-free branch lending a fresh
location keeps the child's share, a view of the parent's lend, resumable. Record lists have
re-readings wherever the code typing agrees on their escrows (`SRecsRR.exists_retype`).

**Opening and ending a lend at `twp`** (`Core/TreeLend.lean`), each a `twp_update` instance, for a
lend of `ℓ ↦ own(())` with the empty escrow (record `lendRec ℓ`). Open (`twp_lendOpen`): the cell
becomes the lend cell `ℓ ↦ imm({α}, (), ∅)`, the run owns the record and the list carries it
tagged `α` (`TWNT.immFrame`; the record's frame lifetime read off the lend cell, the only view at
`ℓ`; other records' frame lifetimes kept since `ℓ` is no lineage location of theirs,
`le_not_linLoc`). End (`twp_lendEnd`): the lend cell goes back to `own`, the record leaves the
run's records and the list (`TWNT.immEnd`), when the rest of the run's resource and the frame hold
nothing at `ℓ` at any depth (`FdEsc ℓ ∅`). The lend cell splits into copies (`viewRes_dup`), each
a shared view another branch may hold across a stop; the end needs every copy back. Neither rule
asks anything of `α`. Escrows that hand out views of their contents (`TWNT.reb`) are not covered.

**Cancel in the scheduler interface.** A cancel is a resume into the continuation's cancel branch.
At a cancellable entry (`q ≠ lin`, `OpEntT.fin`), `contShareT` owes the unwinding
`ccatch (K†[raise …])` as a continuation, below the index, like a resume; `KapSchedT` (naming its
scheduler `H`) offers `hnd H (κ (inj₂ ()))` at `cerwpT` at the empty table, under the same frames
as a resume. An unwinding that performs one of `H`'s operations (an effectful finaliser) stops and
comes back to `H`'s clause as an ordinary stored continuation. `cerwpT_schedHandle` proves the
offering by its induction hypothesis (`twp_kappa_cancel_in`, `twp_kappaC_cancel_in`).
`MultiBranchAdequacyT`'s statement is unchanged. The unwinding is §19's: the raise passes
`[then]` frames, which run their finalisers, and the unwinding borrow forms (`withborU`), which end
the branch's lends; there is no per-type close (decision 73). #793 keeps this rule: a cancelled task
may hold `own` cells, `mut` cells, a copy of a view that only the frame holds, or a view's last
copy, and none of these may be discarded without running the branch.

**The scheduler's pool** (`Core/TreeSchedPool.lean`). `PoolT` is a list of stored tasks, each a
continuation held at the present world (`KapAtT`) whose mask is its present records' masks, every
two apart both ways (`NoneAt` of each other's record masks, and record locations distinct). Every
scheduler operation keeps it: a segment (`twp_keepsPool`, from `twp_frame_keep`: the run may open,
end, allocate and free, those lends open when a stored task stopped included), a park
(`poolT_park`), a resume (`poolT_resume`) and a cancel (`poolT_cancel`), the last two with the rest
of the pool beside the resumed run and a pool again at its every end (`PoolPost`: apart both ways,
records at distinct lent locations, so a task that parks again rejoins it).

**The park stepper** (`Core/TreeSchedRelay.lean`). The stepper `HP` (`schedP_ok`) hands a parked
task's continuation back, at the masks of the records the task owns at its stop. The loop `drive`
(`driveV`, the Z combinator) resumes a parked task each time it parks until it answers;
`drive_twp` keeps a pool of any length beside it, by strong induction on the index through
`poolT_park` and `poolT_resume`. These are lemmas, not a headline.

**Pool-scheduler adequacy** (`Core/TreePoolSched.lean`, over `Core/TreePoolShare.lean`). A
scheduler handler keeps its stopped tasks in its state as a **stack**: the state value is the
handler with the entries, each a tag beside a continuation (`stateVal H ts`, `poolVal ts`), and its
resource is `PoolTJ`. Each entry is held apart from the entries below it at their masks, except at
the lent locations its nearest **joiner** below shares (`shTop`, `AvoidUnsh`); the entries below
hold nothing at its masks; its `imm` cells sit at its own masks or where that joiner shares
(`HoldsIn`); a joiner shares only lent locations of its own or shared with it. A joiner collects
the copies of lends (`ViewsT`) the tasks above it hand back when they end (`PoolTJ.deposit`), and is
resumed with them. The scheduler's answers are functions of the state (`PoolAns Q H Inv`: applied
to any stack meeting the scheduler's invariant `Inv`, of any length, whose tasks run under `H` and
answer in `PoolAns` again (`GoodT`), **with the answer's resource meeting the running task's
conditions against the stack** (the stack holds nothing at its masks; it holds nothing at the masks
of the stack's records not lent at what the nearest joiner shares, and its `imm` cells only at its
own masks or there), it answers the program's `Q` under every frame condition whose frames avoid
all their records). `SchedOKT` is unchanged; it is read at `Qout = PoolAns Q H Inv`.
`PoolSchedAdequacyT` (`poolSchedAdequacyT`): `(hnd H e₀) (H, [])` is `OrDiverges` for every such
scheduler meeting `SchedOKT`, every `Inv` the empty stack meets, and every task at its table at
frame conditions every valid frame meets; through `cerwpT_schedHandle`, `twp_holdsIn`, `poolTJ_nil`
and `topAdequacyT`. It is tied to one representation of the scheduler's state and to answers of
the form `PoolAns`; `MultiBranchAdequacyT` is the general statement, with no state representation
fixed. Every condition is per record and is kept by every run beside the stack (`twp_keepsPoolJ`,
from `twp_frame_keep_sh`, `twp_frame_keep` with the separation from the frame read record by record
and the shared records exempt, and `twp_holdsIn`, which every run keeps by `UpdA`'s end clause:
an end `imm` cell is kept or absorbed by a start `imm` cell, and a cell from beneath a start
ancestor is `mut`). A clause proves its answer by the stack's moves, each a preservation lemma:
run a task beside the stack (`poolAns_run`, `poolAns_run_le`), park the stopped task as a ready task or a
joiner (`poolAns_park`), resume the top with what it has collected (`poolAns_resume`,
`poolTJ_resume`), resume or cancel the second with the first in its place, neither a joiner
(`poolAns_resumeSnd`, `poolAns_cancelSnd`, `PoolTJ.swap`), cancel the top (`poolAns_cancel`,
`poolTJ_cancel`), or hand a finished task's copies to the nearest joiner and resume the top
(`poolAns_depositResume`: at a joiner on top this is the join). The stack scheduler
(`Core/TreePoolSchedProgs.lean`, `stack_schedOK`) meets `SchedOKT` at `PoolAns` for every stack, its
return clause (`stackRet`, `stackRet_okAt`) the deposit-and-resume move; `stackProg_safe` is a
closed program through the headline.

**Limits of the interface.** It is depth-first across joiners (the stack discipline): the moves
reach only the top two entries, a joiner is resumed only from the top, once every task above it
has ended, and only two entries neither a joiner are exchanged. A scheduler picks among the ready
tasks above the nearest joiner; FIFO or round-robin across joiners needs a new `PoolTJ` move, not
only a new clause. Each view a joiner collects is a copy of a lend of `own(())` with the empty
escrow (`ViewsT`); the stack reads only that its cells are `imm`, the join's end of the lend reads
the shape. This is generalised when #791 lands lends with a non-empty escrow.

**Ending a lend at its copies composed** (`Core/TreeLendJoin.lean`). Copies of a lend cell compose
to `ℓ ↦ imm(S, (), ∅)`, `S` the union of their lifetime sets (`viewResS_compS`). In every world `S`
is the lend's lifetime: a tagged record proper's frame is at its tag (`frameLife_of_tagged`, from
`TaggedT` and `not_desc_proper`), and every cell at its location carries that lifetime and no other
(`proper_view_single`, from `view_at_lender`). So `twp_lendEnd_imm` ends a lend at the composed
copies, the run owning the lend's record (its tag read from the start world's list, `RecInv`),
through `twp_lendEnd` unchanged.

**A scheduler with spawn, cancel and join** (`Core/TreePoolSpawn.lean`). `SchedOKTLe N` is
`SchedOKT` with the return clause and the clauses asked only at stops `k ≤ N`;
`cerwpT_schedHandle_le` is `[handle]` at every index `n ≤ N` from it. A clause that runs a task
under its own scheduler proves its stop at `k` from `SchedOKTLe` below `k`, so `∀ N, SchedOKTLe N`
is proved by strong induction and is `SchedOKT` (`schedOKT_of_le`). `HS` has four operations:
`park` (the stopped task parked; the top ready, it is resumed with the parked task beneath it,
`poolAns_resumeSnd`; otherwise the stopped task resumed), `spawn th` (the spawner parked, the child
run holding nothing, `poolAns_run_le`), `cancel` (the stopped task parked; the top ready, it is
cancelled, `poolAns_cancelSnd`) and `par (th₁, th₂)` (the payload's resource split between two
children, each holding copies; the parent parked as a joiner sharing what it owns or is shared with
it, the second child stored unstarted above it as a continuation the clause builds, `κU`,
`kapSchedT_κU`, and the first child run); a task's end hands its copies to the nearest joiner and
resumes the top. Children are verified at tables that themselves have `spawn` and `par`: the tables
are indexed (`tabAt k`, its children's tables those below `k`), and `tabAt k` agrees with the
scheduler's table `TJ` at the stops up to `k` (`tabAt_inclLe`, `cerwpT_table_mono_le`,
`cerwpT_tabAt`), so children spawn and join at every depth. `hs_schedOK`: `SchedOKT` at `PoolAns`
for every stack. Limits of this scheduler: `park` exchanges the stopped task with a ready top
rather than queueing it; a joiner is never cancelled (`cancel` cancels only a ready top); `par`
children hold only copies of lends (`ViewsT`); `spawn` children hold nothing.

**Interleaved lends across parks** (`Core/TreePoolSpawnProgs.lean`), three closed programs
`(hnd HS root) (HS, [])`, each `OrDiverges` through `poolSchedAdequacyT` with every premise
discharged. The program text has no borrow form: each task's lend is opened and ended in the proof,
by `twp_lendOpen` and `twp_lendEnd` (each a `twp_update` instance) around the task's own code. Each
task holds one lend, of its own cell, and every lend is at the same lifetime `α₀`. The loan task
`L = let a = alloc () in ubind (λ_. free a, λ_. free a) (park ())` opens a lend of `a`
(`twp_lendOpen`) and parks holding the lend cell (an `imm` view, its own copy) with the record
open; resumed or cancelled, it merges the view, ends the lend at the resumer's guarantee
(`twp_lendEnd`) and frees `a`. `progLoan_safe`: the root spawns `B = L` and runs `L`; B parks with
its lend open, the root parks holding its view, B resumes and ends its lend, then the root ends its
own. `progCancel_safe`: the root runs `LC` (as `L`, its finaliser parking again inside its own
`ubind`) and spawns `park (); cancel ()`, which cancels the root while it is parked holding its
view; the finaliser parks, is resumed, and ends the lend. `progDepth3_safe`: the root spawns two
`L`s and runs a third; three tasks hold a lend open across a park at once.

**A lend shared by a tree of tasks** (`Core/TreePoolJoinProgs.lean`). `rootJ d = let a = alloc ()
in let _ = par (node d, node d) in free a`, with `node 0 = λ_. park (); cancel (); ()` and
`node (d + 1) = λ_. let _ = par (node d, node d) in ()`. The root opens a lend of `a`; every task of
the tree holds a copy of it (`viewRes_dup`), every inner node a joiner; leaves interleave by parking
and cancel a ready sibling on top. Each task's end hands its copies to its parent; the root,
resumed with every copy, ends the lend at them (`twp_joinEndFree`, `twp_lendEnd_imm`) and frees `a`.
`progJoin_safe d`: `(hnd HS (rootJ d)) (HS, [])` is `OrDiverges` at every depth `d`, through
`poolSchedAdequacyT` with every premise discharged; `progJoin_depth1` and `progJoin_depth3` are its
instances at `d = 0` and `d = 2`. **The early join is refused**
(`twp_refuses_join_early`): a scheduler that resumed a joiner while an entry above it still holds
a copy `viewRes β ℓ` of its lend would run it under a frame holding that copy, and no such run
ends the lend; the interface's resume condition `fdMask` at the joiner's masks excludes that frame
(`not_fdMask_above_copy`).

**Borrow edges point to ancestors, in `CactusInvT` configurations** (`borrowEdges_ancestors`,
`lender_ancestor`; no scheduler instance). In `CactusInvT`, every view a part of a branch's
resource holds (a stored continuation's share among them) carries only lifetimes enclosing the
branch point; and if the part holds any cell at the location of a record proper framed at `α`
(`FrameLifeT`), `α` encloses the branch point. The second reads the invariant alone, with no
premise linking the cell to `α`: a part on a branch not inside `α` holding a cell there is refused
(`fd_le_of_branch`: a view carries `α`, an `own` cell is beneath a borrow, `TWNT.noOwnUnder`, a
`mut` cell is refused by `NoMutT`). A view there carries `α` and nothing else
(`view_at_lender`, `lender_view_carries`). Instances (`Core/TreeBorrowEdges.lean`), built from
the empty world by `TWNT.alloc` and `TWNT.immFrame` (`recWInv_lendStep`, `twp_lendOpen`'s update
at the world), the second branch added by hand with `cactusT_spawn`: `lenderEdge_depth1` (a branch
at a lend's own lifetime holding its view) and `lenderEdge_depth3` (three lends nested
`α₃ ⊏ α₂ ⊏ α₁` on the chain tree, a branch at `α₃` holding the outermost view, its lender two
levels up). These are properties of `CactusInvT` configurations. The scheduler's stored tasks are
carried by `PoolT`/`KapAtT`, not as branches of `CactusInvT`, and nothing yet connects the two:
deriving the property for `PoolT`/`KapAtT` shares is open (#789).

*Open*:
- adequacy derived from invariant preservation, at the relation the typing rules use;
- preservation at spawn and join;
- the frame rules as instances of capture;
- one relation with abortive stops and forwarding (the two relations `erwp`/`cerwp` merge);
- the lend rules at `twp` over the tree for escrows with contents (reborrows, `TWNT.reb`), and
  multi-branch programs whose tasks borrow each other's lends other than as views of what a
  joiner below them shares (`PoolTJ`);
- borrow edges to ancestors for the scheduler's stored shares (`PoolT`/`KapAtT`, #789);
- a FIFO scheduling policy (a recursive append in the clause); `pingpong-mut`'s relay is not yet
  written through the pool. Across joiners, FIFO or round-robin needs a new `PoolTJ` move, not only
  a new clause: the stack interface is depth-first across joiners;
- views of lends with a non-empty escrow collected at a joiner (`ViewsT` fixes `imm(S, (), ∅)`;
  with #791).

### Semantic types read at the tree (#782)

The relation's types are read at the current tree and are monotone along its extension. Two
layers (`docs/new-core/scope-782.md`):

- **Store types** are syntactic codes (`KTy`: `1`, `+`, `Imm`, `Mut`, `[a]`, `ref`) read at the
  tree; a `mut` cell's invariant is its location's code read at the current tree, re-read when the
  tree grows. A code's meaning is carried along the re-reading of a covered resource, at every
  re-typing that agrees on the locations it holds a `mut` cell at (`interp_retype`,
  `RR.exists_retype`; `Support/Model/Tree/Reread.lean`, `World/Codes.lean`).
- **The relation's value types** (`STy`, `Core/TreeSem.lean`) are step-indexed predicates at the
  tree world and the record list, each downward closed in the index and monotone along world
  extension, on the re-reading, at every list keeping the re-readings of the records of the old
  list the resource reads (`KeepRel`: records it does not read may have been ended, and records
  opened, by other branches). Every former is one, each law proved from the components': codes, `1`, `0`, `+`,
  `⊗`, `Imm`, `Mut` (at a store code), `[a]`, `ref`, `!`, `Unk`, the integers, the opaque types,
  the families `[L]`, thunks, `μ` (least fixed point over value-type candidates, with fold and
  unfold at a monotone body: every former `VTy.NoMut` lets `X` occur under is monotone in it, and
  `μ` in its body (`STy.mu_le`), shown at `STy.allBody_mono`; `List`'s cons folds,
  `STy.list_cons`; a map from `NoMut` bodies to monotone bodies is not built) and type variables. A value stored
  before a graft meets its type after it (`STy.reread`; at a proper extension, on a view nested
  three deep, `reread_v3`). **The computation types** (`SCmp`,
  `Core/TreeSemC.lean`) are downward closed: `F A` (`SCmp.ret`), `⊸`, `&`, `⊤`, `∀α ⊏ c` over the
  lifetimes below `c` in the current tree, and `ν` (greatest fixed point over candidates).
- **`F A` is a bare run** (`SCmp.ret`), as Core's `cC (.ret A)` is a bare `wpTS` run: a
  `cerwpT` run at the world and list it is read at, owning no records, to a value of `A`. It is
  Kripke along the re-reading of its whole list (`SCmp.ret_reread`, from `cerwpT_kripke`) and not
  along `KeepRel`: a bare `cerwpT` run owning no records, the records `F A` runs at, is not
  (`Obs.cerwpT_not_keepKripkeNil`, `Core/TreeSemObs.lean`). `cerwpT` quantifies over starts whose
  list re-reads its list whole, a resource holding a view has none at `[]` (`cerwpT_nil_of_imm`),
  and the property would make the stuck `() ()` over a lend's view a run at the lend's list owning
  no records; framed beside the lend's record (`twp_frame`), `let a = alloc () in () ()` would be
  a run at the empty world, which adequacy (`cerwpT_adequacy`) refutes. `F A` is monotone in `A`
  (`SCmp.ret_le`, from `cerwpT_post_mono`), and `U` in its computation type (`STy.thunkC_le`).
  As in Core, the Kripke quantifier sits at `U` only: a thunk is a run at every world extension
  and every list keeping what it reads, monotone by definition. **A thunk is introduced as Core's
  `thunkF_compatC`/`thunkV_compatC` introduce one**: from its computation at every world and list
  over a resource in which the environment is a value of its type, the environment carried to the
  later world and list by its monotonicity (`TEnv.Mono`, the tree's `gDenC_local`, met at every
  value type by `STy.env_mono`), at every computation type (`STy.thunk_intro_env`), at `F A`
  (`STy.thunkRet_intro_env`), for `λ_. M` with the forcing's head step paid from the index
  (`STy.thunkRet_lam_env`; met at `λ_. inj₁ ()`, `STy.thunkRet_constInl`), each with a corollary
  at an environment read at a value type (`STy.thunk_intro`, `STy.thunkRet_intro`,
  `STy.thunkRet_lam`), and of a value (`STy.thunkC_val`).
  `ν` folds and unfolds at Core's body shape `F(A ⊕ U X) & F B` (`SCmp.loopBody_mono`), and is not
  empty there (`SCmp.loop_nonempty`).
- **Continuation and task types** (`Core/TreeSemK.lean`) are thunks and boxed thunks, no new
  former: a continuation is `U (B ⊸ C)` (`STy.kont`), boxed at `@d` by BOXED-κ (`STy.kontBox`),
  a task `[@d] U C` (`STy.task`). The value types read the record list because a thunk is a run,
  and a run is at a list: read at a list fixed in advance (`[]`), a thunk type holds of every
  thunk holding a borrow, since no world with an empty list holds an `imm` cell
  (`cerwpT_nil_of_imm`; a stuck thunk is one, `nilRun_stuck`). Read at the list, a thunk's
  quantifier is the resume condition of the relation's continuation share (`contShareT`, per
  branch: `KeepRel`), so **a continuation captured at a stop, holding a view of an open lend, is a
  value of its type** at every answer type, result type, lifetime and nesting
  (`STy.kont_of_share`); boxed at a lifetime its share outlives, it is carried along any extension
  in which other branches opened and ended records of their own, and resumed there at its type
  (`STy.kontBox_resume_after`): the resume is read off the carried value (`STy.kont_resume` at
  the reflexive extension), at a list whose records are covered, which a start provides
  (`RecInv.cov_ls`). Instances (`Core/TreeSemKEx.lean`) at a proper
  extension of the tree (a fresh child grafted into a chain, `dExt`, `dExt_proper`), with the
  resume list adding a record at the lifetime the extension opened and not a re-reading of the stop
  list: a lend at depth 1 (`kontBox_depth1`), and a view whose witness holds the views of its two
  enclosing lends (`kontBox_depth3`), whose share reads all three records, re-read at the new tree
  while a fourth is dropped (`relFT_d3`, `keep_d3`). The instances use an empty operation table
  (`tbE`), a must-resume entry (`q = .lin`, so the cancel branch is vacuous) and the answer `()`
  at type `1`. The depth-1 resume configuration has starts (`Obs.d1_nonvacuous`: else
  `let a = alloc () in let b = alloc () in () ()`, opening its two lends, would be a run at the
  empty world); for the depth-3 one no start is exhibited, since no rule yet builds a view whose
  witness holds views (no reborrow rule at the tree, row 6). A continuation owning the records of lends its own branch opened is row
  6's: the value types own no records. These are results about one share at `KeepRel`; a
  scheduler's stored shares are carried in pool form (`KapSchedT`, `PoolTJ`, decision 74), each
  resuming at the same `KeepRel`.

On the semantic store typing (`KSem`, `Support/Model/Tree/KSem.lean`) monotonicity is proved for
`1`, `+`, `Imm`, `ref` and `[a]`, each from its components' (`kmono_unit`, `kmono_sum`,
`kmono_imm`, `kmono_ref`, `kmono_box`), and the re-reading exists when every assigned type is
monotone (`reread`). `kmono_mut` and `kmono_thunk` hold for every `τ` (for thunks, every
computation predicate) by the definitions of `vMut` and `vThunk`: they are not results about the
contents of a `mut` cell or a thunk. That a re-read cell's invariant is its location's code read
at the new tree (`RC.mut_inv`), that a lender reads back a value of the store type
(`RC.mut_readback`) and that another invariant is not a re-reading (`not_rc_of_inv_ne`) hold by
`RC`'s definition. What carries `Mut` is that the re-reading exists (`RR.exists_retype`) and that
it holds wherever the old invariant held on carried resources (`RC.mut_extends`,
`reread_extends`); at round 7's cell, at codes, along the graft, the re-read invariant admits the
value stored before it and the handler's borrow the old reading refuses (`round7_codes`). Carried by `trU` (row 5.57's extension by falsity), a cell is not a value of
this `Mut`, whose invariant is the store type read at the current tree (`trU_not_kmono`): that
rules out `trU` with this `Mut`. Against a `Mut` that keeps the predicate a cell was stored with,
the evidence is expressiveness: it refuses round 7's write (`graft_carried_refuses`, against
`round7_write`).

What this rules out:
- **a value type not monotone along extension**: every `STy` carries monotonicity as a field;
- **a bare run read as `F A`**: `F A` at `[]` over a view would otherwise hold of the stuck
  `() ()` (`cerwpT_nil_of_imm`, `nilRun_stuck`); read at every later list it asks the run at the
  lend's own list too, where a bare run is refuted (`Obs.cerwpT_not_keepKripkeNil`).
- **a continuation stored past its lend**: a boxed value holding a view at `α` is not of `[@d] A`
  unless `d` is strictly below `α` (`STy.not_box_of_view`, `STy.not_kontBox_of_view`): the `κ`
  above boxed at its lend's lifetime or at the root is not of its type (`not_kontBox_at_lend`,
  `not_kontBox_at_root`).

Re-read, a stored task may write the handler's newer borrow into a cell it made before the graft
(`round7_write`). The store typing grows at a `mut` lend of a location it does not type, and a
location keeps its type for the run (`TWd.addTy_ext`, `Cov.mono`, `RR.mono` on `tree-wp`, over
semantic types). One `mut` cell per location at any depth is an invariant of the typed tree world
(`TWNT.mutOne`); without it clause 3 of two covered cells is not covered (`clause3_not_cov`).

Departures: `Mut`'s payload is a store code, since a cell's invariant is index-free and a
step-indexed payload (a thunk in a cell) would need step-indexed cell invariants; one mode (no
observable view at `Imm`); the value types read the record list but own no records, and a thunk
runs owning none; `⊸` reads its argument at every index up to `n`.

*Open*: store typing growth at the codes; `Mut` at a payload that is not a store code (#790); a
continuation owning the records of lends its own branch opened (row 6); effect rows (`F_Σ`,
`CTy.eff`): no `SCmp` former, since `SCmp.ret` takes a table with its `Local` and `Down` proofs
and nothing yet builds a row's table with its entries downward closed (`opTableT_down` does it
given the entries'); the typing rules and the fundamental theorem over these types.

### Typing: suspension, scoped spawn, join

- **Operations** carry their qualifier (`lin`, `cancel`, `unr`) and what payload and answer own.
  A lend live across a stop puts the lender's exclusive cell in the continuation's share. An
  unrestricted operation (one that may resume more than once) resumed twice would lend twice
  (argued), so its share owns nothing, a clause of the share's definition (`contShareN`), and an
  unrestricted operation is excluded while a borrow or owned resource is live.
  Multi-shot continuations over duplicable state are a hypothesis, not a rule.
- **A lend's callback `∀'x ⊏ @bnd` may suspend at a row `Row.Suspend 'x @bnd`**
  (`Core/TreeGoal791.lean`): every operation named and not unrestricted; its payload and answer
  types free of `'x` and outliving `@bnd` at the constant's context (`VOutlives Δ bnd`), so their
  values lie in the stratum of every lend `α ⊏ @bnd`, what the Mut Frame asks of a stop (the
  relation's `LendOK`); and each capturable operation's cancel row meeting the same clauses
  (`CTy.SuspendC`), since the cancel run stops at its layers under the live lend. A constant is
  stated at its own lifetime context (*Lifetime-polymorphic suspending constants* below); at the
  empty context the bound, being defined, is closed and so `⊤`. Answers are kept at a closed
  bound (`Row.AnsC`); an answer, which arrives from
  outside the borrowed run, then lies in the top stratum and holds no borrow cell, so it is
  consistent with the run's view. `VOutlives ∅ bnd` excludes exactly the payload and answer types
  with, outside a box or `!`, an `Imm @b A` or `Mut @b A` (no `@b` is strictly longer-lived than
  `⊤`), a thunk `U C` or `Unk` (no outliving rule), or a box `[@b] A` at a `@b` with a variable;
  and the same in cancel rows. A box at a closed lifetime, whatever it holds (`[@⊤] U C`
  included), and `! A` pass. Cleanup that performs is kept: a cancel row may have layers.
- **Lends shared across tasks end only at a join**: scoped spawn. A branch resumed from a join
  asks that no other branch's flattening hold the joined location (`JoinReady`), which gives the
  resumer's frame condition (`joinFd`, `joinReady_fd`). The scheduler establishes it by finishing
  or cancelling every branch that held a borrow of the location and handing their borrows to the
  joiner, which is what a join does.
- **The resume condition** (nothing outside a resumed segment holds a location whose lend it
  ends) holds at the type `Imm 'r 1` in the tree (`fdFromLifetimeTypesT`). At every type it is
  reduced to the branch hypotheses (`hbr`, `hnα`: the others' flattening on a branch not inside
  the frame's lifetime) by `joinFd_of_branch`, whose ownership premise is an invariant of
  canonical-image worlds (`TWNC.noOwnUnder`). In the library's tree world, the condition at the
  lent location and the escrow's exclusive locations (`FdEsc`) gives the end of an `imm` lend
  (`immEnd_valid_of_fdEsc`); the condition at the lent location alone does not
  (`immEnd_esc_config`). It follows from a branch point not inside the frame (`fdEscOfBranch`,
  `escBeneathT`, `fdEsc_of_points`), and a run whose start and end are related by row 5.27's `↭`
  masked at the run's own records keeps it (`fdEsc_of_updX`; along the walks, `fdEsc_of_updA`).
  The mask is needed
  (`lend_open_needs_mask`). The condition holds at a join from the cactus invariant
  (`fdEsc_at_join`), other branches' steps keep it (`stepKeepsFdEsc`), and an end of the lend is
  valid only where it holds (`fdEsc_of_end_valid`).
- Lifetimes on continuation and task types alone do not supply it: not at `Imm 'r 1` in a single
  chain (`not_fdFromLifetimeTypes`), and not at closure types in the tree
  (`not_fdFromThunkTypesT`).
- *Open*: the typing rules and their compatibility lemmas.

### Closing a branch

One rule, stated in pieces at §12, §19 and §27: what may be closed, by whom, and what an unwind
passes through.

- **Two kinds of linear type.** A type that is consumable (§12, `Consumable`) is consumed, when not
  consumed by name, by its consume, which frees its cells. A strictly linear type has none
  and is consumed only by name: a declared type that is not consumable (`decl_linear`,
  `decl_not_ownFree`, §42). The checker inserts a consume only where the type has one (§12,
  `TDerivesP.consume_consumable`).
- **Closeability is a property of the suspension point**, read off the operation's qualifier
  (`Qual`, `kTy`):
  - at a `cancel` operation the continuation may be closed by its cancel component; closing it
    runs the dead region's unwind (`kappaC_cancel`);
  - at a `lin` operation it must be resumed: `U((B ⊸ F_Σ R) & ⊤)` is linear and not consumable
    (`kTy_lin`); no clause that cancels it is typed (`refuses_R_clauses`, R3); its cancel branch
    has no step (`kappaC_cancel_lin`) and is never reached by a typed program (`LiveOK.not_stuck`).
- **The typing rule across a closeable point.** Across a cancellable or abortive point (a row that
  `Row.Cancels`: some operation not `lin`; an abortive operation is never `lin`,
  `OpSig.cancels_of_ent`), every live value is own-free: `[let]`'s `hW`.
- **A branch paused at a `lin` point is itself linear.** It is not closed by a scope's end or by a
  parent's unwind; it is joined or resumed. Its continuation value is linear and not consumable
  (`kTy_lin`). Typing the branch itself (a stored task, a spawned closure paused at a `lin` point)
  as linear is a typing rule: #771 row 6.
- **Raise, cancel and panic unwind only through closeable points.** A raise passes a `[let]` frame
  only at a row that cancels, where the rule above holds; a cancel runs `κ.2`, which exists only at
  a `cancel` operation. Core has no panic: an integer division with no answer raises (§39).

### The named assertion: `HandlerLawN` (#835)

Over the chain, at the relation at the typed world `KW` (`Core/Chain/Goal791N.lean`), every
`CDerives` rule but three has a compatibility lemma, and `fundamentalN_all` proves `SemJN` at every
derivation from those three, `MissingN`. `HandlerLawN` (`Core/Chain/HandlerLawN.lean`) names them
as one hypothesis, a `Prop` and not an axiom, in `PinLaw`'s form (§29): three fields, each over
`SemJN` premises only, at every row, qualifier, handler and handled computation.

| Field | Rule | Core's lemma |
|---|---|---|
| `handleV : HandleVN` | `effHandleV`, `[handle]` at a value form | `handleV_compatC` |
| `handleVB : HandleVBN` | `effHandleVB`, BOXED-κ `[handle]` | `handleV_compatCB` |
| `reify : ReifyN` | `reify` | `reify_compatX` |

The top-level theorem is plain adequacy, every handler inside the program
(`Core/Chain/Adequacy791N.lean`):

    Goal791N : every cs, e₀ with (∀ c ∈ cs, c.OK) and CDerives ∅ (ctx791 cs) e₀ (F 1)
               has OrDiverges (substAll (vals791 cs) e₀)
    goal791N            : HandlerLawN → Goal791N
    fundamentalN_all    : MissingN → CDerives Δ Γ e j → SemJN Δ Γ e j
    handlerLawN_iff     : HandlerLawN ↔ MissingN

No scheduler, scheduler contract (`SchedOKN`) or restriction on handler names is quantified over:
a program that suspends handles its operations inside itself, and those handlers are typed by
`CDerives`'s handler rules.

It is believed because Core proves all three on its own relation, and `PinLaw` already rests on
the same belief: a borrow held across a suspension is sound under a handler written in the
program. The step `cN` does not give is the one `docs/new-core/assert-boundary.md` §2.2 names: a
clause that keeps `κ` hands it to `vN`'s `U` clause, which reads `KW.OwedR`, where the stop owes it
along `KW.Owed` at the floor the stop chose; `reify` reads its loop through the same clause. The
tail and last handlers (`effHandleT`, `effHandleL`) resume or cancel `κ` at the world the clause's
value is posted at, and are proved (`handleT_compatN`, `handleL_compatN`).

- **Not refuted.** Every configuration in the tree was checked against the three fields
  (`docs/new-core/configurations.md`, *Against `HandlerLawN`*): each is pointwise over a `κ`, a
  world or a share, and those at a `κ` use the thunk `κ = ()`, which no `[op]` step hands a clause
  (`kappa_ne_unit`, `kappaC_ne_unit`), and whose resumption is final (`unit_resume_final`), where
  every handed `κ`'s resumption steps (`kappa_resume_not_final`, `kappaC_resume_not_final`). Not
  verified that no typed instance refutes a field.
- **Not vacuous.** `handle_resume_inst`: the conclusion of `HandleVN` and `HandleVBN` at the
  relation at `KW` holds at the handler `resumeH`, whose one clause receives `κ` and resumes it,
  over every handled computation at every outer row (`handleVN_at_resumeH`,
  `handleVBN_at_resumeH`); every premise of each holds there over `perform`
  (`handleVN_resume_premises`, `handleVBN_resume_premises`). `ReifyN`'s premises hold at the
  residual `λx. x` (`reifyN_premises_inst`); no instance of its conclusion is proved. `Goal791N`'s
  premises hold at `prog791` (`goal791N_premises_inst`): a cell lent `mut` with `withbor (2)`,
  its callback performing `wait` while it holds the borrow, `wait` handled inside the program.

### The answer's view across a lend (#844, T1.3)

A lend's callback reads an answer at its own view `setLife c ℓ α`; the lender's table reads it at
`c`. Consistency moves between the two by what the answer holds at `ℓ`, not by its stratum
(`Core/Chain/SI/LocTy.lean`):

    NoMutAt ℓ ρ               ≜ ∀ e, ExS ρ e → ∀ ψ, e.get ℓ = some ψ → ψ.kind ≠ mut
    consistentX_setLife_iff   : NoMutAt ℓ ρ → (ConsistentX (setLife c ℓ α) ρ ↔ ConsistentX c ρ)
    consistentX_of_noMutAt    : (∀ ℓ, NoMutAt ℓ ρ) → ConsistentX c ρ
    noMutAt_of_top            : ρ.InStratum ⊤ → NoMutAt ℓ ρ
    noMutAt_of_setLife        : ρ.InStratum s → α ≤ s → ConsistentX (setLife c ℓ α) ρ → NoMutAt ℓ ρ
    not_noMutAt_inStratum_down: some ρ in Res_{↓α} has a `mut` cell at ℓ, at α, consistent with
                                setLife c ℓ α and with no view c where c ℓ ≠ α

`consistentX_setLife` (a walk missing `ℓ`) and `consistentX_of_top` are corollaries, and so is
`consistentX_of_outlivesN` (`Core/Chain/ReindexK835N.lean`), in place: at the closed bound the
answer is in `Res_⊤`, so `NoMutAt ℓ` holds at every `ℓ`. The callback's table steps
(`tabNK_lend_comap`, `tabNK_lendMapB_comap`) read the answer's consistency with the lender's view
and move it to the lend's view by `consistentX_setLife_iff`, at each lend of a `KW.LendMapB` map;
the closed bound is read only for `NoMutAt`.

- **Baseline.** No statement changes: `consistentX_of_outlivesN`, `consistentX_of_top`,
  `consistentX_setLife`, `tabNK_lend_comap`, `tabNK_lendMapB_comap`, `goal791N`.
- **Open.** At a non-closed bound the answer's stratum does not give `NoMutAt ℓ`: `Res_{↓α}` admits
  a `mut` cell at `ℓ` (`not_noMutAt_inStratum_down`), and `Res_s` for `α < s` admits one at a
  lifetime above `s`, which the lender's view can read and the lend's cannot. The stratum gives
  only the converse move, from the lend's view to the lender's (`noMutAt_of_setLife`). The
  lender-to-lend move needs `NoMutAt ℓ` carried in from where the answer is disjoint from the lent
  cell; no table carries it yet.

### Lifetime-polymorphic suspending constants (#844, Tier 1)

**What it adds.** The suspending lend constants (`Const791`) are typed at a lifetime context of
their own, so a callback's bound `@bnd` may name lifetime variables and a payload may hold a borrow
of a lend that encloses the suspending one.
- **The constant.** `Const791.poly 'y @b c` is `c` under one lifetime binder: its type is
  `∀'y ⊏ @b. c.ty` (the existing former `VTy.all`, `U(∀'y ⊏ @b. F A)`), its value `λ_. c.val`. A
  constant under binders `'y₁ ⊏ @b₁, …` is typed at `!∀'y₁ ⊏ @b₁. … c.ty`; a program instantiates
  it by `allEV`. No `VTy` former, `CTy` former or `CDerives` rule is added.
- **The premises at a context.** `Const791.OKAt Δ c`: at `poly 'y @b c`, `∀I`'s side conditions
  (`@b` and `Δ`'s bounds do not mention `'y`) and `c.OKAt (Δ, 'y ⊏ @b)`; at a lend constant, its
  rule's premises with the empty context replaced by `Δ`: `Δ ⊨ @bnd`, the outliving premises at
  `Δ`, the row `Row.Suspend Δ 'x @bnd`, the finaliser typed at `Δ`. `Const791.OK c` is
  `c.OKAt ∅`. One clause is kept closed: every answer of the row and of its cancel rows outlives a
  bound defined at the empty context (`Row.AnsC`), which is today's answer clause. `withloadU`
  (`wl`) does not carry it: its compatibility lemma moves no answer between views.
- **`Row.Suspend Δ 'x @bnd`**, `CTy.SuspendC Δ 'x @bnd`: the outliving clauses at `Δ`
  (`VOutlives Δ bnd`) instead of `∅`.
- **The laws** read at `δ ⊨ Δ`: `vN_inStratum_bnd`, `vN_add_eq_bnd`, `vN_add_eq`, `vN_lend_eq`,
  `ValRelOK.inStratum`, `tabNK_lendOKCR` and `tabNK_lend_comap` take `VOutlives Δ bnd` and
  `Δ.Models δ`. The `∅` forms are their instances at `models_empty_any`. The constants'
  compatibility lemmas (`withbor2S_compat`, `withbor3S_compat`, `withborFS_compat`,
  `withloadS_compat`, `sliceBorrowMS_compat`) are stated at `Δ` and `δ ⊨ Δ`.
- **The answer's view** (*The answer's view across a lend* above). The step that moves an answer
  from the lender's view to the lend's (`tabNK_lend_comap`, `tabNK_lendMapB_comap`) reads
  `NoMutAt ℓ` of the answer. At a bound with a variable the answer's stratum does not give it, so
  these steps carry it as a named premise of every answer of the row and its cancel rows,
  `AnsNoMut B δ ≜ ∀ Θ k v ρ, 𝒱⟦B⟧δ Θ k v ρ → ∀ ℓ, NoMutAt ℓ ρ` (`CTy.AnsC`). The constants
  discharge it from `Row.AnsC` at a closed bound (`ansNoMut_of_closed`, by
  `noMutAt_of_outlivesN`).
- **Inhabited at a variable bound**: `polyC_ok`, the constant `Λ'1 ⊏ ⊤. Λ'2 ⊏ '1. withbor2U` at
  `∀'0 ⊏ '2`, its row yielding `Imm '1 1`, a borrow of the enclosing lifetime.
- **A closed instance at `goal791N`** (T1.4, `Core/Chain/Nest844N.lean`): an outer `imm` lend's
  borrow yielded across an inner suspending lend to a handler between them, resumed and
  cancelled. The constant is `nestC = Λ'1 ⊏ ⊤. Λ'2 ⊏ '1. withbor3U` at `∀'0 ⊏ '2`, its row
  `yield : Imm '1 1 ↠^cancel 1` (cancel row `F 1`), finalised by `forget`. The program, in `F 1`
  at the empty context from `nestC` alone:

      r ← alloc (); (r, ()) ← withbor1U r (Λ'3. λi.                 -- outer imm lend of the input
        s ← alloc (); (s, ()) ← withbor2U s (Λ'4. λc.               -- the scratch cell, 'w = '4 ⊏ '3
          handle_yield (                                            -- the handler, inside '3, outside '0
            (c, ()) ← nestC ['3] ['4] c (Λ'0. λm. yield i; forget m); forget c)
          with H; ['4] ());
        free s; ['3] ()); free r

  `'3` and `'4` come from Core's own lends (`withbor1U`, `withbor2U` at the empty row); `nestC`
  is instantiated by `allEV` at `'3 ⊏ ⊤` and `'4 ⊏ '3`, so its callback bound is the variable `'4`
  and its payload `Imm '3 1` borrows the enclosing lend. `H` resumes `κ` (`progRes`) or cancels it
  (`progCan`), each clause releasing the payload with `forget`. Each meets every premise of
  `Goal791N` (`nestC_ok`, `d_progRes`, `d_progCan`), so `goal791N` concludes `OrDiverges` of each
  from `HandlerLawN` (`progRes_orDiverges`, `progCan_orDiverges`). The answer is `1`, closed.

- **Where the present relation stops** (`Core/Chain/Spike844N.lean`), each a configuration with
  every hypothesis discharged: `lender_mut_payload_empty` (the lender reads a `Mut 'x A` payload at
  `δ`, where `'x` is unbound, and it has no values); `lend_mut_payload_not_inStratum` and
  `lendOKCR_pa_fails` (the callback's own borrow is not in `Res_α`, so the Mut Frame's `pa`
  fails); `CrossStop.erwpK_refuses_borrowOut` (a segment starting with `ℓ` owned cannot stop with
  a borrow of `ℓ` in its payload, at any world index) and `CrossStop.not_crossTaskMLendK`
  (`erwpK_M_frame`'s statement at `KW`, `KW.PostK` and `Θ.view c` with `LendOKCR.pa` dropped is
  refuted). `RowSuspendB` is `Row.Suspend` with the payload and answer allowed to name `'x`
  (`rowSuspendB_of_suspend`). These bound Tier 2 (the callback's own borrow as a payload), which
  needs a new stop clause; they change no statement.

**Baseline preserved.** `goal791N : HandlerLawN → Goal791N`, its statement unchanged but for
`Const791.OK`'s shape; `fundamentalN_all`; `handlerLawN_iff`; `goal791N_premises_inst`; the
instances at the hardest case's row (`w2_ok`, `w3_ok`, `wF_ok`, `wl_ok`, the `*S_inst`). No change
to `CDerives`, the checker, the backends or the corpus.

**Open.** The answer at a bound with a variable: `AnsNoMut` without `Row.AnsC`, so that an answer
may hold a borrow of an enclosing lend. Not derived from the answer's type: the index world may
key `ℓ` at a lifetime above the bound, where a `Mut` answer type outliving the bound has values
holding a `mut` cell at `ℓ`; the obstruction is not verified. Tracked as #853.

### Not claimed

- Termination for programs that use the new rules.
- Threads: the invariant is per computation, so a concurrent reading stays possible. Two places
  rely on sequential scheduling: the frame of a run is fixed for the whole segment, and
  `JoinReady` is read at the resume (`SI/CactusInv.lean`).
- Lowering: per-task state machines, self-reference, per-state consume glue. Tracked as the series'
  last issue.

### Target programs

Eight programs (`corpus/pending/`, on the local branch `pending-770`, stacked on `fs-769`; held)
illustrate the theorem; they are not the goal. A rule shaped to one program is refused. When one
starts to pass, a variation must pass as well (#771). Three fail first on earlier gaps:
- no read of a boxed field through an `imm` borrow;
- no unbounded loop in a task of `spawn`;
- no `imm` reborrow of a handler's `mut` state.

### Design record

`docs/new-core/structure.md` (target structure and its rules), `docs/new-core/conditions.md` (every
condition and gap, classified), `docs/new-core/evidence.md` (the spikes' results by Lean name).

---

## 63. Entry 62 — the new backend: a `Λ` over a value form; `[lend-R]` at the empty row (#847)

### Motivation

Backend2 refused four checked programs (#847). Three (`corpus/alpha-app-arg.bc`,
`alpha-generic-arg.bc`, `alpha-lam-binder.bc`) build `Fun 'y < top. return v` with `v` a variable
or a literal: the `Λ`'s body erases to a value form, not a λ-value, and §44's fact covered only a
λ-value. The fourth (`alpha-withbor2r.bc`) holds a relaxed lend (`[lend-R]`, §29) at `main`'s
empty row, which Backend2 compiled only inside a state machine (§49).

### Language

No change: no type, rule, term, typing, elaboration, semantics or erasure.

### The rule

- **A `Λ` over a value form** (`Frontend/Check/Derived.lean`, `allI_inst`, replacing §44's
  statement at `t.isLam`). `[∀I]` checks its body with the binder's slot dead (`TDerives.allI`:
  the context `⟨S, false⟩ :: Γ`), so no variable of the body reads it. For an `allI` node whose body
  `t` has `valFormB (false :: u) t.erase` (`Frontend/Check/Rules.lean`: the erasure is a value
  form whose variables are slots live in `u`, the binder's slot not among them; a λ-value is one
  whatever it mentions; sound by `valFormB_sound`, `Expr.ValFormIn` of §24), the instantiation
  `(λ_. t.erase) ()` steps by one β, at every memory (`PureSteps`), to `t.erase.subst 0 ()`, and
  that is a value form over `u` (`valFormB_subst_dead`):

      allI_inst : valFormB (false :: u) t.erase = true →
        PureSteps ((allI … t).erase ()) (t.erase.subst 0 ()) ∧ valFormB u (t.erase.subst 0 ()) = true

  No code runs and no memory is touched: the instantiation's value is the body's. A λ-value
  satisfies the premise, so the statement contains §44's. Backend2 (`Backend2/Convert.lean`, the
  `allI` case) decides the same Boolean at the slots its context holds live
  (`valFormB (false :: ctx.map Option.isSome) c.erase`) and converts the body with the binder's
  slot dead, as §44 does.
- **`[lend-R]` at the empty row** (`Frontend/Check/Derived.lean`, `lendR_plain`). R1's term at
  the owner is `withborU d r (Λ. λm. M)` (`lendRE d M`, §29): the callback under the unwinding
  frame, whose finaliser `d` runs on the owner only when the callback stops at an operation
  (`ewp_unwind`, §19). At a row `Σ` with `Σ.isEmpty` the row's table has no entry
  (`rowTab_isEmpty`), so the callback never stops, and every end of its run is a return, where the
  frame pairs the owner with the answer (`ewp_ret_pair`):

      lendR_plain : Σ.isEmpty = true → closedAt 0 d → closedAt 0 (lendCb M) → closedAt 0 u →
        ewpTS ((lendCb M) () u) (opTable (Row.tab Σ δ)) (fun w => Q (u, w)) →
        ewpTS ((lendRE d M)[u/0]) (opTable (Row.tab Σ δ)) Q

  for every `d`: the finaliser never runs, and the relaxed lend is the plain lend, the callback
  run on the owner and its answer `b` giving `(r, b)`. Backend2's `conv` (`Backend2/Convert.lean`,
  the `lendR` case) reads the node's row by the same Boolean: at an empty row it lends the owner
  `mut`, converts the callback on the view and answers `(r, b)`, as the plain lends do
  (`genLend`); `d` is not converted. At any other row the node is a machine's (§49, `convK`) and
  `conv` leaves it outside the fragment.

### Programs

`corpus/alpha-app-arg.bc`, `alpha-generic-arg.bc`, `alpha-lam-binder.bc` and `alpha-withbor2r.bc`
at their goldens at every stage of Backend2; Backend2 compiles every corpus program.

### Baseline

No change to `CDerives`, the relation, the machine, the checker, the elaboration, the old
backend's output or a kernel program. `corpus/counts-backend2.expected` and
`erasure-backend2.expected` gain the four programs' lines; no other line changes.

### Open

- `lendR_plain` is stated at the empty row. A row of resuming operations handled by a direct call
  (§47) never cancels the callback either, but its proof needs the resumption, which is
  `PinLaw`'s ground (§29); such a lend stays a machine's.

---

## 64. Entry 63 — the new backend: a box taken apart is reused by the next box of its size (#651)

### Motivation

Backend2 allocated more than the old backend on six programs (#651). Each extra allocation is a
boxed field of a recursive type (§35, *one box a node*) built by a `roll`; Backend2 lays every
`μ` out on its type's own graph (`Backend2/Layout.lean`), one box a node. They have two causes.

- **A node taken apart and built again.** `match unroll ts { inr (t, rest) -> … cons(t, rest) }`
  (the token put back by `rec-parser`, `parse-recover` and `parse-recover-gen`): the `unroll`'s
  `case` and the payload's `letpair` load the boxed tail and free its object, and the `roll`
  allocates an object of the same words for the same tail. Rust moves the `Box` and allocates
  nothing. The old backend allocated nothing there only where its layout types, unified over
  the erased closure IR with no `μ` (`Backend/Clos/Types.lean`), put the rebuilt node off the
  type's cycle, its tail inline; on the cycle it freed and allocated as Backend2 did.
- **A node built with a fresh tail.** `count3`'s list in `effects-fail-list` (5), `map`'s
  elements `[[1, 2], [3]]` and `cons(0, l)` in `list-generic` (5), `evens`/`odds` in
  `rec-generic-mutual` (3). The old backend's unification laid these out with fewer boxes than
  nodes: a list built to a fixed depth and read only to that depth has an acyclic layout type,
  and a cycle through two functions' types is unrolled, one box for two nodes. That is a fact
  about the program's value flow, rebuilt by unification with no proof, and not one the checker
  states. Rust allocates one `Box` a node in each; so does Backend2, §35's target. They stay
  (Open).

### Language

No change: no type, rule, term, typing, elaboration, semantics or erasure. Only Backend2's
lowering to the word IR changes.

### Lowering

- **Spare boxes** (`Backend2/Lower.lean`, `getField`, `putField`, `LState.spare`). Where a
  `letpair` or a `case` takes a boxed field apart, its words are loaded as before and its object's
  free is deferred: the object is a *spare box* of its words. A pair or an injection the term
  builds (`Tm.pair`, `Tm.inj`) whose boxed field has as many words as a spare box stores them in
  it, and allocates nothing.
- **Where a spare box is freed.** Before a call (`lowerCall`), before a return (`emit` at
  `Dest.ret`), and at the end of each arm of a `case` for those the arm has not used: every arm
  starts with the boxes held before the `case`, and none is held past the join. So a spare box
  is reused only on a stretch of the path with no call between its free and the build, and every
  object is freed on every path that does not build into it.
- **What it rests on.** The deferred free is the free the lowering made before, at the same
  object, moved later on the same path past statements that do not read the object (its words are
  in locals). A build into it writes all its words before any read. So the reuse is sound
  exactly when that free was: when the box has one owner, the value taken apart. That is
  `Backend2/Layout.lean`'s existing `UNPROVED:` assumption on boxed fields (the LIR consumes each
  variable once on every path, which `Lint` checks of every compiled program), restated at
  `getField`. No kernel fact is read or rebuilt: the kernel has no boxes, and the choice of
  object is the allocator's bookkeeping below the typed term.

### Programs

Counts per run (`allocs indirect copies loads stores bounds`), Backend2 before and after, and
the old backend:

| program | before | after | old backend |
|---|---|---|---|
| `rec-parser` | `22 0 0 66 66 0` | `17 0 0 66 66 0` | `17 0 0 51 51 0` |
| `parse-recover` | `259 0 31 1848 1036 0` | `245 0 31 1848 1036 0` | `246 0 31 1808 984 28` |
| `parse-recover-gen` | `240 0 31 1983 1199 108` | `226 0 31 1983 1199 108` | `227 0 31 1943 1147 108` |
| `effects-fail-list` | `5 0 0 15 15 0` | unchanged | `0 0 0 0 0 0` |
| `list-generic` | `32 0 0 158 105 0` | unchanged | `27 0 0 148 102 0` |
| `rec-generic-mutual` | `11 0 0 45 33 0` | unchanged | `8 0 0 44 32 0` |

Every other count that changed is an `allocs` that fell, where a program takes a node of a
recursive type apart and builds one of the same words before a call: `count-down-exact` 6 to 3
(the counter's node moved to the accumulator), `operator-rounds` 90 to 83, and the
task programs, `async-borrow` 29 to 10, `async-logged` 25 to 15, `async-scoped` 25 to 9,
`async-workers-scoped` 43 to 14, `io-task` 31 to 14, `sched-a` 43 to 40, `sched-a-div` 14 to 11,
`sched-b` 44 to 41. No count rose.

A function that builds its boxes in spare boxes calls no allocator, so §50's `willreturn` class
(the functions at the empty row calling no runtime function but `bc_free`) can grow: `io-task`'s
has 9 functions where it had 5 (`corpus/trusted/io-task.txt`), each at the same two assumptions,
`CallRelated` and `HostStack`.

### Baseline

No change to `CDerives`, the relation, the machine, the checker, the elaboration, `Convert`, the
layouts, the old backend or a kernel program. Every corpus program keeps its output at every
stage of Backend2, with `live 0` where its golden has it.

### Open

- **The fresh-tail nodes** above (`effects-fail-list` 5, `list-generic` 32, `rec-generic-mutual`
  11, against the old backend's 0, 27 and 8) are one box a node, as in Rust: they meet §35's
  target and are recorded as explained rises under the switch's kill criterion 6
  (`docs/compiler.md` §5.4). The old backend's lower counts came from its layout unification, a
  value-flow fact rebuilt with no proof, which compiling from checked facts rules out. The
  intended way to remove them is fusion: an unfold followed by a fold (a hylomorphism) fused,
  so that the intermediate `μ` list is never built (#651).
- **The move.** Rust keeps the moved tail behind its pointer; the reuse still loads its words and
  stores them back (the loads and stores above are unchanged). Holding a taken-apart field as
  its pointer until a use needs its words would remove them.
- **Across a call.** A spare box is freed at the next call: `map` and `filter` (`lib/list.bc`)
  free a node before their recursive call and build one after it, as Rust does. Reuse across
  calls (Perceus's reuse tokens) would build them in place.

---

## 65. Entry 64 — the new backend: codata's η-thunk at any depth (#842)

### Motivation

Backend2 compiled the observations of a protocol object as indirect calls where the old backend
made direct ones (#842). `corpus/nu-file-*.bc` build their object as an η-thunk whose observations
are nested, `thunkv nu_in < < (nu_out (force f s)).1 .1, (nu_out (force f s)).1 .2 >,
(nu_out (force f s)).2 >`, and `alpha-nu-in.bc` builds one whose observation is written under the
binders of its arguments, `Λ'x. λb. (nu_out (force f k)).1['x] b`. §45's derived node recognised
only the flat form, the `&` of `f s`'s two observations. The thunk was compiled as a code of its
own, so the codata's closure class held two codes, `unfold`'s and the thunk's, and every
observation through a value read out of data (a pair, the rest an observation answers) dispatched
on them. The old backend made these calls direct with its closure flow analysis (`Backend/Clos/Flow.lean`), which follows a closure through
pairs; Backend2's flow reads data by its layout class (`Backend2/Flow.lean`), so it is the class
that must hold one code.

### Language

No change: no type, rule, term, typing, elaboration, semantics or erasure.

### The derived node

- **The η-tree** (`NuTree`, `NuArg`, `NuTree.toE`, `scripts/pin/TExpr.tmpl.lean`). A thunk that
  observes codata `f s` (`f`, with no state) by η-expansion is the erasure of a tree: an `amp` is
  a `&` (`withPair`) of the observations at `inj₁ ()` and `inj₂ ()`, a `lam` a `λx` passing `x` on,
  a `dead` a `Λ` (`λ_`) passing `()` on, and a `leaf` the observation made so far, `f s o₁ … oₙ`,
  directly or through a binding of `f` first (`(λg. g s o₁ … oₙ) f`, `g <- return (unbang f); …`).
  `NuTree.toE t f s os` is that erasure over the arguments `f`, `s` and the observation `os` made
  above it; §45's flat scheme is the tree `amp (leaf rb) (leaf rb)`.
- **`nuEta f s t`**'s premise `nuEtaB f s t.erase` (§45) now reads: the erasure is
  `NuTree.toE t' (var f) (s.map var) []` for some tree `t'` (`NuTree.parse` proposes the trees
  the shape allows; `NuTree.mem_parse`: it proposes every tree over a variable). The node is kept
  by moving the term's variables (`NuTree.toE_shift`, `nuEtaB_shift`, the same statement as
  §45's). The checker reads the variables at the first leaf (`nuEtaOf?`,
  `Frontend/Check/Rules.lean`) and checks them with `nuEtaB`.

### The fact

`Frontend/Check/Derived.lean`. Filling a variable of a tree's erasure fills it in the tree's
arguments (`NuTree.toE_subst`), so at a run the thunk is the tree over values `fv`, `sv`. An
observation `ps` of the tree that reaches the subtree `t'` (`NuTree.Reach t ps t'`: a projection at
an `amp`, any value at a `lam`, `()` at a `dead`) reaches it by pure steps, at every memory:

    nuEta_reach : t.Reach ps t' →
      PureSteps (nuAppsE (t.toE fv sv os) ps) (t'.toE fv sv (os ++ ps))

so an observation that stops inside the tree answers a `&` or a `λ`, a value, and touches no
memory; one that reaches a leaf reaches the same observation of `f s` (`nuEta_leaf`, `nuEta_obs`),
of `f` with no state (`nuEta_var`):

    nuEta_obs : t.Reach ps (leaf rb) →
      PureSteps (nuAppsE (t.toE fv sv []) ps) (nuAppsE (fv sv) ps)

and at `f = unfold step` (`hN C g`), the same observation of `etaN C g s`, which `f s` steps to
by one β at every memory (`nuEta_unfold`, from `hN_steps`). §45's three statements are these at
the flat tree, and are replaced by them.

### The lowering

Unchanged (§45): Backend2 reads the `nuEta` node, whatever its tree. With no state it is its
variable; with a state, when `f` is a variable a `bind` bound to `unfold step`, it is the call
`f s` made there; any other is compiled as its thunk.

### Programs

Every corpus program at its golden at every stage of Backend2. In `corpus/counts-backend2.expected`:

| program | before | after | old backend |
|---|---|---|---|
| `nu-file-twice` | `2 7 0 11 11 0` | `2 0 0 11 11 0` | `2 0 0 11 11 0` |
| `nu-file-contexts` | `3 5 0 10 9 0` | `3 0 0 10 9 0` | `3 0 0 10 9 0` |
| `nu-file-read` | `2 5 0 7 6 0` | `2 0 0 7 6 0` | `2 0 0 7 6 0` |
| `nu-file-consumed` | `2 3 0 5 5 0` | `2 0 0 5 5 0` | `2 0 0 5 5 0` |
| `alpha-nu-in` | `5 3 0 12 13 0` | `4 3 0 9 9 0` | `1 0 0 2 1 0` |

(`allocs indirect copies loads stores bounds`.)

No other line changes.

### Baseline

No change to `CDerives`, the relation, the machine, the elaboration, the old backend's output, a
kernel program or any program's erasure. `corpus/counts.expected` unchanged.

### Open

- **`tree-view-tasks.bc`, 600 indirect calls: the η-thunk's `f` is threaded through the `for`
  loop's state, and no fact says the loop hands it on unchanged.** The thunk is a `nuEta` node
  (flat), but `for t in 0..tasks` carries `f` in its state with the rest the body uses
  (`forData`), so `f` reaches the node out of the state's `letpair`, not from the `bind` of
  `unfold step`. The thunk is compiled as its own code, the class `nu. F (i64 + X) & F 1` holds it
  beside `unfold`'s, and every `resume_at`/`cancel_at` dispatches. A fact on the loop's node that
  a state component is handed on unchanged (as a walk's `read`, §46, fixes its view), or an
  elaboration that captures a `!` variable instead of threading it, would carry `f`.
- **`alpha-nu-in.bc`, 3 indirect calls and 4 allocations (the old backend's 0 and 1): a closure
  read out of a pair is read by its layout class.** `mk`'s thunk is now `unfold`'s call, but
  `wrap`'s object is a second code of the class (it is not an η-thunk: its `close` adds 100).
  Backend2's flow gives a value read out of a pair every code of its class, so three calls
  dispatch: `obs_read`'s `.1` on `w`, which the call passes in the pair of its arguments; the call
  of the closure that projection answers; and `obs_close`'s `.2` on the rest read out of
  `obs_read`'s answer. The class's layout is on the heap, since `wrap`'s code holds a value of the
  class itself, so each of the three objects is an allocation. Which code a value read out of a
  pair is, is not a fact of the typed term; a flow that follows a closure through a pair (as the
  old backend's did) or per-code layouts would make the calls direct and the objects inline.

---

## 66. Entry 65 — the new backend: the slots `absurd` absorbs (#862)

### Motivation

Backend2 refused a checked program (#862, `book/src/guide/iteration.md`'s `take(6, fib())`, with
`fn fib() -> 0 with Yield[i32]`): `LIR lint: … x379 consumed at ref Output (unused), where the
rule's premise does not hold`. The `for` inside `take` meets its source's end at `absurd`
(`zeroE`, the source's answer is `0`), and `main`'s output capability, a `ref Output`, is live
across that arm. `absurd`'s masks hold it in neither part, and `splitCtx` consumed it at the rule
`unused`, which `Lint` admits at a persistent type only (§12). This is F5's absorb case (§55,
`Check.AbsorbsAt`): `absurd` types the term at every type of a slot it does not read.

### Language

No change: no type, rule, term, typing, elaboration, semantics or erasure.

### The rule

- **At `absurd`** (`Backend2/Convert.lean`, the `zeroE` cases of `conv` and `convK`; `splitCtx`'s
  `absorbs`). `CDerives.zeroE hs hV` gives `V : 0` the part `Γ₁` of the split and absorbs the rest:
  `Γ₂` and every slot neither mask holds. Backend2 converts `V` in `Γ₁`'s slots and ends the path
  at `Tm.absurd v`; the slots of `Γ₂`, and now the slots neither mask holds, are left unconsumed.
  Only the `zeroE` cases pass `absorbs`; at every other rule a slot neither mask holds is consumed
  at the rule `unused`, at a persistent type only, as before.
- **What `Lint` reads.** `lintTm` gives a path that ends at `absurd` (or `unreachable`) no
  leftover set (`Left` is `none`): a path that never returns needs no consume of what it still
  owns. The premise is the `absurd` node at the path's end, read from the LIR; the slot's type is
  not tested. A variable left on a path that returns is refused at the function's end, at every
  type (`Backend2/LintTests.lean`, `absorbProg`).
- **At `⊤`.** `topI` is not split: Backend2 abandons its whole context at `Abandon.top`, whose
  premise (none: `topI` has no premise) `Lint` reads from the node (§12). Nothing changes there.

### Programs

`book/src/guide/iteration.md`'s `take(6, fib())` block on Backend2 at its answer, in Wasm and
natively. `corpus/gen-take-print.bc`: `take(3, naturals())` printed by `main`, with
`naturals() -> 0`: the output capability live across `absurd`'s arm.

### Baseline

No change to `CDerives`, `Core/`, the relation, the machine, the checker, the elaboration, the old
backend or a kernel program. No other corpus program's output, erasure line or count changes:
the consumes no longer made are on paths that end at `absurd`, which never run.

### Open

- `UNPROVED:` that no rule but `zeroE` and `topI` leaves a slot of a type that is not persistent
  in neither part of its split (`Check.SplitMasks.NeitherAbsorbed`, reduced to
  `Check.UnmentionedAbsorbed`). A slot a deeper `absurd` or `⊤` absorbs, unmentioned by the whole
  part above it, would reach another rule's split; `Lint` refuses its `unused` consume, so such a
  program fails to compile rather than run unsound.

---

## 67. Entry 66 — the new backend: an owned fold by pointer reversal (#876, B6)

### Motivation

Backend2 compiled every owned fold as a function that calls itself once per node
(`Backend2/Convert.lean`, `genFoldFns`), so a fold over a list of `n` nodes takes `n` native
frames: `corpus/deep-list.bc` (50000 nodes, `fold_own[1 + (i32 * X), i32]`) ran in a native
stack of 64 KiB on the old backend and needed 1–4 MiB on Backend2 (#876). The old backend
reverses pointers in an owned fold (`Backend/README.md`, *Stack*), but on a term it recognises,
assuming the ownership (`docs/compiler.md` §7.2, defect 6). The ownership is the rule's: §6's
`foldOwn` and `foldReuse` take the structure as `μX. T ⊸ F R`.

### Language

No change: no type, rule, term, typing, elaboration, semantics or erasure. Only Backend2's
conversion of a `foldOwn` or `foldReuse` node changes.

### The fact

The node itself, with its shape `F : FShape` (`TExpr.foldOwn`, `TExpr.foldReuse`;
`TDerives.foldOwn`, `TDerives.foldReuse`, `Frontend/Check/TDerives.lean`; `CDerives.foldOwn`,
`CDerives.foldReuse`, `Core/Fundamental.lean`, by `foldOwn_compatX` (`Core/FoldOwn.lean`) and
`foldReuse_compatX` (`Core/FoldReuse.lean`)). Its type `!U(A′_R ⊸ F R) ⊸ !U(μX. F.ty ⊸ F R)`
(`algOTy`, `foldOTy`; `A″_R`, `algRTy`, at `foldReuse`) says:

- the fold consumes the structure: `μX. F.ty` is taken by `⊸` and given back nowhere, so every
  node of it, and every cell at a `Ref X`, is the fold's own while it runs;
- where the recursive positions are: `F`'s `varX` and `refX` leaves;
- what the algebra is applied to: `F.resO R` (`F.resR R`), `R` at each recursive position, never
  a node of the structure.

The conversion reads `F` and nothing else: no term is recognised.

### The rule

- **The shapes** (`shapeReversal?`): `F = 1 ⊕ C` or `C ⊕ 1`, with `C` a product (`⊗`) of
  closed leaves and exactly one recursive position, `X` or `Ref X` (`shapeIsProd`,
  `shapeXCount`). Every other shape keeps `genFoldFns`' recursion.
- **The lowering** (`genFoldRev`): an entry function and two loops of tail calls. The stack is a
  value of the structure's own type `μX. T`, its bottom the base node `1`. The descent
  (`fold_down`) unrolls a node; at `C` it puts the stack at the recursive position and the node
  becomes the stack's top (`cutRev`: a boxed `X` rebuilt by a pair or an injection, a `Ref X`
  cell given the stack by `swap`), and it goes on with the child; at the base it applies the
  algebra and calls the ascent. The ascent (`fold_up`) unrolls the stack; at a node it takes the
  link from the recursive position and puts the result there (`plugRev`: at `Ref X` the cell is
  freed under `foldOwn`, and under `foldReuse` its contents swapped for `()` and the emptied cell
  paired with the result, as `travR` does), applies the algebra and goes on with the link; at the
  bottom it answers the result.
- **Nothing is allocated.** A boxed `X` taken apart by the descent is a spare box of the node's
  words (§64), and the node rebuilt with the stack in it is of the same type, so it is built in
  that box before the tail call; a `Ref X` cell holds the stack in place of the child, at the same
  type. The ascent frees each box and cell once, as the recursion did.

### What it rests on

- **Read:** the node's ownership of the structure (above). The stack is made of the structure's
  nodes, so no other word reaches them while they are reversed. In the LIR the reversal is
  values taken apart and rebuilt, each consumed once (`Lint`); the in-place storage is §64's spare
  box, at `Backend2/Layout.lean`'s existing `UNPROVED:` assumption on boxed fields, and a `swap`
  on a cell the fold owns.
- **`UNPROVED:`** (`genFoldRev`): that the two loops compute the fold the kernel's term computes
  (`foldOwnV`'s `travO`, `foldReuseV`'s `travR`): the algebra applied to the same arguments in the
  same order, the innermost node first, and the same cells freed, a `Ref X` cell at the ascent
  rather than at the descent. The algebra never receives a reversed link: it is applied to the
  base and to nodes whose recursive position holds a result. A mismatch shows as a disagreement
  with the source stage, or a leak or a double free in `live`.

### Programs

`corpus/deep-list.bc` runs natively on Backend2 in a stack of 64 KiB (and of 16 KiB), with its
golden output and `live 0`; its owned fold's 50000 nodes take no frame each. Every corpus program
keeps its output at every stage of Backend2 (`scripts/compile-backend2.sh`: the LIR, the word IR,
Wasm and native).

Counts per run (`bcc-counts --backend new`): no `allocs`, `indirect`, `copies` or `bounds` count
changes. `loads` and `stores` rise on the 19 programs whose owned folds run (below): the descent
stores each node back with the link in it and the ascent loads it again, where the recursion
kept the node's words in its frame. `deep-list`'s are now the old backend's (`450003 450003`).
`corpus/counts-backend2.expected` takes the new lines.

| program | loads stores before | after |
|---|---|---|
| `deep-list` | `300003 300003` | `450003 450003` |
| `13-2-sum-prog` | `120 78` | `153 111` |
| `sum-prog-exact` | `120 78` | `153 111` |
| `axes/data-effects` | `94 67` | `118 91` |
| `axes/result-fold-own` | `28 28` | `49 49` |
| `axes/scope-data-effects` | `52 33` | `61 42` |
| `clone-reuse` | `27 18` | `36 27` |
| `data-fold-bang` | `8 8` | `14 14` |
| `data-fold-generic` | `20 11` | `26 17` |
| `data-fold-list` | `42 27` | `60 45` |
| `data-fold-whole` | `92 50` | `107 65` |
| `decl-promise` | `15 15` | `24 24` |
| `gen-adapters` | `18 18` | `33 33` |
| `gen-adapters-fail` | `27 27` | `51 51` |
| `map-reuse` | `30 30` | `48 48` |
| `surface/map-reuse` | `24 24` | `42 42` |
| `print-borrowed-list` | `67 42` | `76 51` |
| `sched-a` | `445 441` | `477 473` |
| `sched-b` | `448 442` | `480 474` |

The owned folds that keep the recursion: `data-fold-tree`, `data-fold-forest`, `data-fold-group`
and `consumes` in `data-fold-whole` (a second recursive position, there under a `⊕`), and
`axes/free-monad` (`i32 + i32 * X`, a base with data). `sum-i32` has no fold node: its list is
freed by a consume (§12).

### Baseline

No change to `CDerives`, the relation, the machine, the checker, the elaboration, the layouts,
the word-IR lowering, the old backend or a kernel program. Every corpus program keeps its output
at every stage of Backend2.

### Open

- **A base with data.** `i32 + i32 * X` and other shapes whose base summand is not `1` keep the
  recursion: the stack's bottom must be a node of `μX. T`, and only `1` is one without data.
- **More than one recursive summand, or a recursive position under a `⊕` of `C`** (the old
  backend's *linear* shapes, e.g. `A ⊕ X ⊕ (B ⊗ X)`) keep the recursion.
- **Two recursive positions** (trees, `data-fold-tree`, `data-fold-forest`) keep a frame a level,
  as `fold_imm` does everywhere.
- **`foldOwnG`** (§61) and the consume of a `μ` (`genConsume`, §12) recurse once per node.

---

## 68. Entry 67 — per-code closure types: `Code⟨N; E⟩ C` (#855, K0)

### Motivation

Every closure has the one type `U C`, and every codata `U (νX. C)`, so the type does not say which
code a value is. Backend2 rebuilds the code sets with two flow analyses (`Backend2/Flow.lean`,
`Layout.lean`'s closure classes) and a per-use reconversion (`takesClos`), all `UNPROVED:`. This
entry states a value type that names its code, as Rust's closure types do, with an explicit
erasing coercion to `U C` (`dyn`). The design is `docs/new-core/scope-855-per-code-types.md`
(option (a), decided 2026-11-07); this entry is its unit K0. It adds the syntactic and semantic
lemmas the later units reuse, and no `VTy` former, rule or relation clause (K1–K4).

### Language

- **The former** (K1). `VTy.code (N : Expr) (E : VTy) (C : CTy)`, written `Code⟨N; E⟩ C`: a thunk
  of `C` whose code is `N` and whose captured environment has type `E`. It is a separate former
  beside `U C`; no rule that asks for `U C` accepts a `Code⟨N; E⟩ C`.
- **A code** (`Core/CapNorm.lean`). For a closure `λM`:
  - `Expr.occs k e`: the free variables of `e` under `k` binders, counted from the binders.
  - `Expr.capVars e`: the captures, `occs 0 e` sorted without repeats.
  - `Expr.capNorm e`: `e` with each free variable `i` renamed to its rank in `capVars e`
    (`Expr.ren`). The code of `λM` is `N = capNorm (λM)`, itself a `λ`.
  - `Expr.capEnv e γ`: the captured values of a closing substitution, in rank order.
- **The environment type.** `E = A₀ ⊗ (A₁ ⊗ (… ⊗ (Aₙ₋₁ ⊗ 1)))`, the captures' slot types in rank
  order, ending in `1`; `1` when nothing is captured. Its values are `tupleV us`, right-nested
  pairs ending in `()`. The trailing `1` makes the tuple decide the capture list (`tupleV_two`
  at two captures): the scope's `A₀ ⊗ A₁` without it would let `[g, (s, t)]` and `[g, s, t]` share
  a tuple.
- **`[α]` and equality** (K1). `alphaB` at `code`: `N` equal as an `Expr` (`DecidableEq`), `alphaB`
  at `E` and at `C`. `N` holds no lifetime and no name.
- **Free lifetimes** (K1). `VFree x (Code⟨N; E⟩ C) ≜ VFree x E ∨ CFree x C`. No `VOutlives` rule
  for `code`, as there is none for `U`.
- **Persistence.** `Code⟨N; E⟩ C` is not persistent; `!Code⟨N; E⟩ C` is.
- **Printing.** Types contain bodies. `ppVT` and the checker's messages print a code as a digest
  (`{closure@span}` with `E`), never the body.

### The relation

```
𝒱⟦Code⟨N; E⟩ C⟧ v ρ  ≜  (∃ us. v = N[us] ∧ 𝒱⟦E⟧(tupleV us) ρ)  ∧  𝒱⟦U C⟧ v ρ
```

- `N[us]` is `Expr.psub 0 us N`. The first conjunct is the code (`codeP`); the second is the `U`
  clause (`codeRelC`). In the observable view the clause is `True`, as `U C`'s is.
- At the chain's relation (`codePN`, `codeRelN`, `Core/Chain/CodeNuKW835N.lean`) the conjunct reads
  `vN E δ Θ n (tupleV us) ρ` at the value's world and index.
- **The environment holds the whole resource.** The scope's clause split `ρ = ρE ⋆ ρR` with `ρR`
  unread. `nuOutK` needs the state's resource to be the codata's (`candN` holds the state at the
  whole `ρ`); with `ρR` the step is not derived (obstruction not verified). So the clause holds `E`
  at `ρ`, and `codeI` carries a premise that makes that true (below).

### The rules

Each is a `CDerives` rule with one compatibility lemma, mirrored into `CDerivesP` and `TDerives*`
by `scripts/gen-pin.py`, and into `CDerivesAt` (`Core/Tied.lean`) by hand. No new index and no new judgment.

| Rule | Statement | Unit |
|---|---|---|
| `codeI` | `Γ ⊢ λM : U C` and `Γ.CapOK (λM)` ⟹ `Γ ⊢ λM : Code⟨capNorm (λM); Γ.capTy (λM)⟩ C` | K3 |
| `codeIB` | the same at `!U C` ⟹ `!Code⟨…⟩ C`; its premise on the context is `Flat(Γ)` (`Ctx.FlatLive`, §10), as promotion's | K3 |
| `codeErase` | `Γ ⊢ e : Code⟨N; E⟩ C` ⟹ `Γ ⊢ e : U C` | K3 |
| `codeEraseB` | `Γ ⊢ e : !Code⟨N; E⟩ C` ⟹ `Γ ⊢ e : !U C` | K3 |
| `force` (restated) | `Ctx.SoloP Γ i T`, `T.forceTy = some C` (`T` is `U C` or `Code⟨N; E⟩ C`) ⟹ `forceE C (.var i) : C` | K3 |
| `unfoldK` | `unfold : !G ⊸ !Code⟨hCode C; !G ⊗ 1⟩ (S ⊸ F Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C))`, at a consumed context, with `C.NuOk`, `G.forceTy = some (S ⊸ C[S/X])` (`G` is `U(S ⊸ C[S/X])` or a code type of it) and `C.BindsFresh S` | K4 |
| `nuOutK` | `x : Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)` ⟹ `x : C[Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)/X]` (`force` at a ν is `x`), with `C.NuOk`, `G.forceTy = some (S ⊸ C[S/X])`, `C.BindsFresh S` and `C.BindsFresh G` | K4 |

- `Γ.capTy e` (`Ctx.capTy`, `Core/CodeRules.lean`): the tensor of `Γ`'s slot types at
  `capVars e`, in rank order, ending in `1`.
- `VTy.forceTy` (`Core/Types.lean`): `some C` at `U C` and at `Code⟨N; E⟩ C`, `none` elsewhere.
- `Γ.CapOK e` (`Ctx.capOK Γ e = true`, a `Bool` test, `Core/CodeRules.lean`), a side condition the
  checker tests: every captured slot is live, and every
  live slot of `Γ` that `e` does not capture is persistent. With it the uncaptured slots hold `∅`
  (`vCE_empty_of_persistent`), so the closure's resource is its captures'. It is a premise, not
  an inversion of `CDerives`.
- `C.BindsFresh G` in `nuOutK`: the unrolling under a `∀'x` leaf reads the code type, which
  contains `G`, at `δ[x↦α]`, and a code-typed `G`'s environment could mention `x`. `codeTy`,
  `hCode`, `hEnv` and `unfoldKTy` are in `Core/CodeNuOut.lean`.
- `etaCode C = λo. self x₀ x₁ o`, the code of `unfold step s = etaN C g s`, with the step `x₀` and
  the state `x₁` captured; `hCode C = λs. λo. self x₀ s o`, the code of `unfold step`.
- `codeErase` is not subsumption: it is a rule on the same term, so the typed term has a node for it,
  which Backend2 reads (B4). In the machine it is the identity.
- `eraseD` (covariant erasure inside `C`, K6) is not in this entry.
- **The inversion's cost** (CLAUDE.md, *Do not invert `CDerives` casually*). `codeI` types the
  term `λM` at a new type, and `codeErase`/`codeEraseB` add a view step from a code type to `U`.
  In `Core/Inversions.lean`: `VS` gains the two erase steps, and `VView.hnf` the code heads;
  `VarCls` is restated over `forceTy`; `LamCls` is the computation case or `ThunkCls`, the λ read
  at `U`, `!U`, `Code` or `!Code`; `LamAx` reads at the axiom type's views and their code types.
  `lam_bang` and its uses in `Core/Rejections.lean` and `Core/EffCancelTyped.lean` are restated.
  `der_swap` reads at `ValClsC`; `hnf_of` and `eq_of_heads` take a no-code-head hypothesis their
  callers discharge. K4: `VarCls` gains a third disjunct, a variable at a code-typed `ν` read at
  `C[codeTy/X]`, restated in place, with new `JR` lemmas about `instT`, which do not invert
  `CDerives`. No inversion is added and no substitution over derivations; every rejection keeps its
  statement and verdict.

### Erasure policy

- **C1, specific by default.** A function or codata type written in a parameter or return position
  is an `impl`: the parameter becomes a template parameter, instantiated at the argument's code
  type. `dyn` is written to opt in, and means `U C`.
- **C2, silently at a lend's exit.** Where a code type captures `'x` and the rule asks `¬ VFree x B`
  (`withbor1` and the lend rules), the elaborator inserts `codeErase` to `U C`, which is today's
  typing.
- **C3, silently at a join.** Two different codes joined (`if`/`match` arms) with no expected type
  are erased to `U C`; S1's census counts these sites.
- Wherever the expected type is `U C` (parameters written `dyn`, data fields, arrays, `Ref`
  contents, handler arguments and state), `convVal` inserts the `codeErase` node.
- **The growing-instantiation guard.** A template whose instantiation reaches itself at a type
  argument containing the previous one is instantiated at the argument's erasure, with a note
  (scope §4.4). It is load-bearing: without it nested `Code⟨…⟩` inside `E` grows without bound.
- A closure capturing a value of its own code type is not formable (`E` would contain the type);
  the elaborator erases that capture.

### The library code of this entry

`Core/CapNorm.lean`:
- `Expr.capNorm_shift : Expr.capNorm (Expr.shift d c e) = Expr.capNorm e`.
- `Expr.psub_capNorm : (∀ i ∈ Expr.occs 0 e, i < γ.length) →
  Expr.psub 0 (Expr.capEnv e γ) (Expr.capNorm e) = Expr.psub 0 γ e`, and its form at a thunk,
  `Expr.lam_psub_capNorm`: `λ(γ(M)) = (capNorm (λM))[capEnv (λM) γ]`, the value
  `thunkF_compatC` builds.
- `Expr.occs_capNorm_lt`: a code's free variables are below its number of captures.

`Core/CodeNu.lean`: `tupleV`, `codeP`, `codeRelC`, `etaCode`, `etaEnv`, `codeCand`;
`occs_lt_of_closedAt` (with `closedAt_of_derives`, `codeI`'s hypothesis on `γ`);
`etaCode_capNorm`, `etaN_code`, `etaN_codeRel`, `codeRel_etaN`, `candN_le_codeCand`, and
**`nuOutK_step : (codeCand C G S δ).Le (nuF C δ (codeCand C G S δ))`**, at a `G` whose values are
`U(S ⊸ C[S/X])`'s.

`Core/Chain/CodeNuKW835N.lean`: `codePN`, `codeRelN`, `codeCandN`, `etaN_codeRelN`,
`codeRelN_etaN`, `candNN_le_codeCandN`, and **`nuOutK_stepN : (codeCandN C G S δ).Le (cBN (U(νX. C))
(codeCandN C G S δ) C δ)`**.

### Size

`experiments/CodeSize` (`lake build code-size`) walks each corpus program's typed term, each
`use` body once per key, and measures `capNorm` of each closure node and the type with codes nested
inside `E` (a capture bound by `bind`/`letPoly` to a closure counts that closure's nested size;
any other capture counts `1`).

Over the 330 corpus programs that check this way (10 of 340 do not: they need the library's
data table, which the experiment does not load), at 9,152 closure nodes, in `Expr` nodes:

| | median | p95 | max | total |
|---|---|---|---|---|
| code `N` | 38 | 921 | 135,827 | 4,672,257 |
| type, codes nested in `E` | 39 | 929 | 135,829 | 4,691,273 |
| captures per closure | 0 | 2 | 6 | 3,537 |
| `etaCode C` (424 `unfold` nodes) | 239 | 369 | 437 | 110,380 |
| type at each use of a closure-bound slot (784 uses) | 61.5 | 913 | 20,824 | 223,199 |

- The largest type is `corpus/float-roundtrip.bc`'s, 135,829 nodes, a closure around nearly the
  whole program (its erased `main` is 143,317 nodes). Stored unshared its codes total 1,106,707
  nodes, 7.7 times the program: a closure's code contains every closure nested in it.
- Nesting through `E` is rare (156 closures; at most 1,142 nodes added): most closures capture
  nothing (median 0), and the bulk is the code itself.
- **So `N` is held by reference, not rebuilt.** A code is the erased subterm itself, shared, with
  a digest (a hash of `capNorm`, computed once per node) for keys and comparisons, structural
  equality on a digest match. With sharing the codes are linear in the program; rebuilt per type
  they are quadratic in the nesting depth. Structural `N` stays the kernel's statement: the digest
  is the checker's and Backend2's representation of it, and printing uses the digest too.

### Baseline

No change to `CDerives`, the relation, the machine, the checker, the elaborator or a backend.
`fundamentalC`, `adequacyC` and `goal791N : HandlerLawN → Goal791N` keep their statements and
proofs; every corpus and kernel program its output. The later units must preserve the same three.

K3 (the four rules and the restated `force`): `fundamentalC`, `adequacyC` and `goal791N :
HandlerLawN → Goal791N` keep their statements and cover the new rules, the chain's through
`FundamentalKW835N`. The judgment freeze holds: no new judgment, and the rules join `CDerives`,
mirrored by `scripts/gen-pin.py` and, into `CDerivesAt`, by hand. Every rejection theorem keeps its verdict; one that flips is
reported as an intended change.

### Open

- **Built (K1, K2):** `VTy.code` (`Core/Types.lean`) and its arm at every match in `Core/`,
  `Frontend/` and `Backend2/`; `[α]` at `code` (`VTy.alphaB_refl_code`); the clauses `vCE`
  (`vCE_code`: the clause is `codeRelC`), `vNE` (`vNE_code`: `codeRelN`) and `vOE` (`True`); every
  law of the relation at `code`, with no new hypothesis. `fundamentalC`, `adequacyC` and `goal791N`
  keep their statements.
- **Built (K3):** `codeI`, `codeIB`, `codeErase`, `codeEraseB` and the restated `force`, with their
  compatibility lemmas at Core's relation and at the chain's, and `codeI`'s semantic step: the
  captured tuple is in `𝒱⟦Γ.capTy (λM)⟧` at the whole resource.
- **Built (K4):** `unfoldK` and `nuOutK`, with their compatibility lemmas at Core's relation and
  at the chain's. Core's unrolling at a code type is proved (`cB_unrollK`, `nuP_codeCand`, the
  analogue of `vC_inst_envS`/`cBN_unroll`). The kernel program `Core/Chain/CodeLoop855N.lean`: a
  unit stream over a cell whose state stays at `Code⟨etaCode C; …⟩(Stream 1)` across three
  observations and the close, by `nuOutK`, concluded at `adequacyC` (`progK_runs`) and at
  `goal791N` (`progK_orDiverges`).
- **Not built until their units land:** the lend-exit lemma (K5), `eraseD` (K6), and `cloneCode`
  (K7, #928).
- **No code type in the checker.** No rule of the checker or the elaborator synthesises a code
  type before S1, and Backend2 does not lower K4's rules (S4, the B-units), so the corpus is
  unchanged by K3 and K4.
- **`CapOK`** is a premise of `codeI` until #894 removes it.
- **Choices K1 made that the entry does not state:**
  - A type substitution (`VTy.rename`, `VTy.subst`) leaves `Code⟨N; E⟩ C` as it is, as it leaves
    `U C`: no `μ` variable reaches `E`, `Cl k` holds, `Occ` fails. The clause reads `E` at no
    environment, as `U C` reads `C`; a captured slot's type is read the same way in `Γ` and in
    `E`, so `codeI` needs no closedness premise.
  - `vC_ind` and `vN_ind` keep the code clause in one unfolding (`vF`, `vFN`) with the property at
    every value of `E`, from an outer induction on the type's size: `E` is smaller and no
    substitution enters it.
  - `TyEq` at `code`: equal `N`, `TyEq` at `E` and `C`. `VTy.inFrag` at `code`: `E` and `C`.
    `NoThunkT` at `code` is `False`, as at `U`. `VTy.persistent`, `VOutlives`: as `U`.
  - The step-indexed model (`Core/Chain/SI/Sem.lean`) and the tree model (`Core/TreeGoal791.lean`)
    read `code` as empty, as they read `μ` (#840).
  - Printing: the checker prints `Code⟨#h; E⟩ C`, `#h` a hash of `N`'s serialisation, not
    `{closure@span}` (a kernel type has no span). Backend2's `useKey` prints a type `ofV` refuses
    exactly (`keyVT`, `N` in full), so two codes are two keys; `ofV` refuses `code` (B1).
- **The chain's equation at the code candidate** is not derived; obstruction not verified.
  `nuOutK_compatN` is proved by a direct route instead: `node_okP`, the node lemma over a leaf
  predicate, at the code clause, with `cBNP_unroll` (each state mapped into the code clause at the
  leaf's world by `etaN_codeRelN`). `cBN S R` is `cBNP S (thunkRN R)` (#947).
- **The scope's `ρR`.** With a part of the resource the environment does not hold, `nuOutK` is not
  derived; obstruction not verified. This entry drops `ρR` and moves the obligation to `codeI`'s
  premise `Γ.CapOK`. That a well-typed closure always meets `CapOK` (no live non-persistent slot
  goes unused) is not derived; where it fails, the checker keeps `U C`.

---

## 69. Entry 68 — the new backend: a cancel that suspends (#869)

### Motivation

§27 lets a finaliser perform an operation whose handler is outside every region that can cancel
it (D2), and records it in cancel rows. Cleanup that awaits (closing a socket during a cancel,
the pipes connector's per-step finaliser) needs a finaliser that may suspend, and a cancel row
holding a machine operation, lowered. §49 refused both.

### Language

No change to types, rules, terms, typing, semantics or `Core/`. The surface's finaliser rows are
§27's (#868).

### The rule

One construct per step of `Paper`'s machine:

- **The cancel component.** A machine operation's suspended computation is `U((B ⊸ F Y) & K)`
  (§49). At a capturable operation (`capB`), `K = F C`, `C` the outcome of `F_{fin} 1`, the cancel
  row's own outcome. With no machine operation in `fin`, `C` is `1 ⊕ P_fin`, as before; the
  nesting of cancel rows is finite (§27), so the type is. At a must-resume operation `K = ⊤`
  (§49).
- **A cancel that may suspend is a machine.** The cancel entry of `k`, and `κ`'s cancel at a
  drive over `k.1`, whose cancel row has a machine operation, is a machine of `C`'s outcome. The
  callee's cancel and each finaliser in it are call points.
- **`cfin` as a frame** (`cfinF`). It holds the error kept so far. On the finaliser's answer or
  raise it keeps the first error and goes on with the cancel (`[cfin-ret]`, `[cfin-raise]`). When
  the suspended cancel run is itself cancelled, it keeps the earlier error and goes on through the
  rest of the region (`[cfin-cancel]`). The run's end answers `()` or the kept error (`[cancel]`,
  `[cancel-raise]`).
- **`[then]` with a finaliser that may suspend** (`unwindF`). On an ordinary unwind the finaliser
  is a call point of the machine; its row is in the machine's (`Σ_D ≤ Σ`). The pending raise is
  held in a frame, dropped when the finaliser raises (`then_fin`) or when the machine is cancelled
  meanwhile.
- **Who drives.** The canceller. A suspension of a cancel run returns to the code that observed
  `.2` and is forwarded to the nearest live handler (§19 *Cancels*); the cancelled region's
  handlers are dead, the cancelled task's own site among them. The forwarding is transcribed from
  `Paper`'s `ufin`, `ufinC`, `cfret`, `cferr`, `cfcancel` and `creraise`.
- **Stack machines** (§52) keep a pure cancel path: a machine with a suspending finaliser, or whose
  operation's cancel row has a machine operation, is not a stack machine.
- **Facts read.** Each row entry's qualifier, answer and cancel row; `[then]`'s `Σ_D`; `κ`'s
  `cancelTy`. `ThenLe` and `Σ_D ≤ Σ` are the typing's. The conversion fails loudly on a
  suspension outside its machine's row.
- **`UNPROVED:`** A non-capturable operation's cancel entry is never entered (it traps). A stored
  site's stack is owned by a suspended cancel run's `k` alone.

### Programs

- `deep-gen-count` (the #866 twin of `deep-gen`): `((), i32[2])`, `live 0`.
- `core-fin-op`, the `progFinOpT` twin: a finaliser performs, and the outer handler resumes.
- `core-fin-keep`, the `progKeepT` twin: a kept error across a suspension.
- `cancel-suspend-unwind`: finalisers suspend on an ordinary raise; one supersedes the pending
  raise, one frees a cell.
- `cancel-suspend-nested`: two suspending finalisers, the callee's cancel itself a machine; the
  first error kept.
- `core-fin-stored-k-op`: a stored `κ` cancelled after its handler returned, its cleanup suspending
  in the canceller.
- `core-fin-cancellable`: an abort unwinds through a finaliser that performs a capturable
  operation, handled outside the abort: `(inr (), i32[1])`, `live 0` (§27, `Σ_M`).
- `core-fin-nc`, the `progNC₁T` twin: the outer handler cancels the finaliser's continuation
  (`[cfin-cancel]`): `()`.
- `core-fin-op-cap`: `core-fin-op` with a capturable finaliser operation: `inr ()`.
- `cancel-suspend-cancel`: the suspended cancel run cancelled in turn, the outer finaliser freeing
  a cell: `()`, `live 0`.
- `core-fin-consume`, the `progConsumeT` twin: an unrestricted finaliser operation whose own cancel
  row holds an abortive one: `inl ()`.
- `core-fin-keep-unr`, the `progKeepT` twin with an unrestricted finaliser operation: `inr ()`.

In `core-fin-op`, `core-fin-keep`, `cancel-suspend-unwind`, `cancel-suspend-nested` and
`core-fin-stored-k-op` the finalisers' operations are must-resume; `core-fin-cancellable`,
`core-fin-nc`, `core-fin-op-cap` and `cancel-suspend-cancel` use a capturable one, and
`core-fin-consume` and `core-fin-keep-unr` an unrestricted one.

### Baseline

No change to `CDerives`, the relation, the machine, `Core/`, `Paper/`, `Support/`, the checker,
the elaboration, the old backend or a kernel program. Every LIR type of the existing corpus is
unchanged (`outcomeTy`'s empty case). `corpus/counts-backend2.expected` and
`corpus/erasure-backend2.expected` are unchanged.

### Open

- A stack machine whose cancel suspends: Backend2 refuses a cancel that may suspend over a task's
  own stack (§52) until a lowering proved memory-safe (the stack freed exactly once along every
  suspending cancel run) lands, #970.
- Cleanup that awaits needs `lib/async.bc`'s `cancel` to have a cancel row (the surface).
- The old backend keeps refusing a finaliser that suspends (§27 *Lowering*).
- A finaliser that reaches a capability the body uses (§27 *Open*, a kernel question).

---

## 70. Entry 69 — `>|` and stream chains (#919, pipes unit S)

### Motivation

Pipes (#907, `docs/new-core/scope-pipes.md`, decision B′): `|>` is push and keeps §33's cases;
`>|` is pull, and is new. Under (R) an adapter is a *stage*: a computation that performs the item
effect `Stream[A, K]` (`next()`, `stop()`, L1 #920) and `Yield[B]`, with no source parameter. A run
of stages is one n-ary connector (L1), so the user never sees a bracketing. This entry adds the
surface: the token, the rule that recognises a stream edge by effects, the chain's normal form,
and the transitional reading of `>|` that lets it be written today, before the connector (L1) and
the stage-form adapters (L2, #921) exist.

### Language

- **The operator.** `e >| s`, the token `>|`, has the precedence of `|>` (the lowest, below `||`)
  and associates to the left. Its right operand is a stage as `|>`'s is: a spine `f`, `f[As]`,
  `f(a, …)`, or a parenthesised chain (below). Printed `(e >| s)`.
- **A stream stage.** A function stage `f(…)` is a *stream stage* when `f` performs lib's item
  effect `Stream` — identified by **lib's declaration** of it (L1, #920), never by an effect's
  name — or, **transitionally until L2**, when `f`'s first parameter, as its signature writes it,
  is a stored generator `U (pull A K R)` (today's source-owning adapters, `lib/adapters.bc`). A
  handler is never a stream stage. **Until L1 declares `Stream`, the first kind does not exist:**
  a user's effect named `Stream` makes nothing a stream stage, and S classifies by the parameter
  only.
- **A stream edge** (by effects; **decided in L1**). `e ∘ s` is a stream edge when `s` performs
  lib's `Stream` and `e`'s **inferred row** has an iteration effect (`Env.iterEff`, §15; `Yield[A]`
  in lib). A written row is an upper bound (§18), so it is never read as what `e` performs: the
  decision reads the row the elaboration infers for `e`, where rows are inferred (after
  `resolvePipes`, at the `Env`), and where inference has none for `e`, the edge is §33's case
  (iii) with the note `cannot tell whether this is a stream: annotate the block's row`. L1 adds
  the test with the branch it decides (the connector); in S no edge's elaboration depends on the
  left side's row — a `|>` is §33's by the stage, and `>|` is accepted by the stage — so S has no
  stream-edge test and no note.
- **The normal form.** A maximal chain is a source and a list of edges, each marked with its mode
  (`|>` push, `>|` pull): left-nested, the source first. `(a ∘₁ b) ∘₂ c` is read as written; a
  stage that is itself a chain, `a ∘₁ (b ∘₂ c)`, is spliced into the chain when every edge it
  adds is a *joining* edge. **Until L1, only `>|` joins:** a `|>` edge is always read as written,
  so a parenthesised chain at a `|>` edge is a stage, as §33 reads it (`range(0, 3) |> (sum(range(0,
  2)) |> g(5))` is `g(range(0, 3), sum(range(0, 2)), 5)`, `corpus/pipe-push-paren.bc`), and only
  programs that write `>|` can be rebracketed. L1 may let a `|>` into a stage of lib's `Stream`
  join. Two bracketings of one chain of joining edges have one normal form (theorem below), so they
  elaborate to one term. A `>|` edge takes the span from its chain's source to its stage; a `|>`
  edge keeps its node's.
- **The mixing rule.** `|>` and `>|` mix freely in one chain; the operator at each edge names that
  wire's mode. `src >| take(3) |> each(f)` is one chain of three stages with one pull and one push
  wire (one connector, L1). An edge that is not a stream edge is §33's, whatever chain it is in.
- **Elaboration, edge by edge** (in order, the source first):
  - **`|>`**: §33's cases by the stage, exactly as before §70 — (i) a handler, (ii) a computation
    parameter first, (iii) any other function. A source-owning adapter is case (iii), the left side
    stored at its parameter (§15).
  - **`>|`** into a stream stage (until L1, a source-owning adapter): case (iii), as `|>`. So `>|`
    is usable at once, and every output and count of a `|>` pipeline written with `>|` is the
    `|>` form's.
  - **L1** adds: a stream edge into a stage that performs lib's `Stream` runs on the connector.

### Refusals

- `` `>|` connects stream stages; `f` is not a stream stage `` — `>|` into a function that is not
  a stream stage (or into a handler: `` …; `h` is a handler: write `|>` ``).
- `` the right of `>|` is a stream stage, applied to its other arguments `` — a stage that is not
  a spine.
- **A limit:** a generic first parameter, `app[T](it: T, …)`, is not a stream stage: `>|` refuses
  `app` (the parameter is no stored generator until it is instantiated, after this pass), and
  `|>` into it is §33's case (iii), unchanged.
- **A limit (§15, not §70's):** a generator's call is stored only at a parameter written
  `U (pull …)`, so at an abbreviation of it both `|>` and `>|` are refused today
  (`corpus/pending/pipe-alias.bc`, #973).
- **Not added here:** the refusal of a source-owning function at `|>` (scope §3 item 3). It moves
  to L2, where lib's adapters become stages; in S it would break `corpus/gen-pipeline-pipe.bc`,
  `bench/chain-gen` and the book's sites. The `>|` refusal of a `Stream` stage whose left side
  yields nothing moves to L1 with the stream-edge test.

### The user's example

    watch(kube) |> filter(p) |> each(e -> reconcile(e) |> retry(3) |> timeout(30s))

- The outer chain is a stream chain: `watch` performs `Yield[Event]`, `filter` and `each` perform
  `Stream[Event]`. One connector, push wires. (Waits for L1/L2: `each`, the (R) `filter`, and a
  `watch` that performs I/O.)
- `each`'s per-item body `reconcile(e) |> retry(3) |> timeout(30s)` has no stream edge: neither
  `retry` nor `timeout` performs `Stream`. It is §33's case (ii), effect layers, run per item.
- In this order, a timeout that `retry` does not catch escapes `each`'s body, so `each` raises, and
  **the whole `watch` pipeline is closed** (`docs/new-core/scope-pipes.md` §3), each stage's cleanup running
  downstream-first. To keep watching after a per-item failure, handle it inside `each`'s body
  (`… |> timeout(30s) |> log_and_skip`).

### Theorem

`Frontend.Elab.Pipes.chainOf_bracketing` (`Frontend/Elab/Pipes.lean`): for a bracketing (a tree of
pipe nodes, `PipeTree`) whose leaves are not pipe nodes and whose edges all join, the marks of the
normal form (`PipeChain.marks`: the source, and each edge's mode and stage) are the tree's in-order
flattening. So two bracketings with one flattening have one normal form
(`chainOf_bracketings_eq`; `chainOf_assoc` for `(a ∘₁ b) ∘₂ c` and `a ∘₁ (b ∘₂ c)`). The
elaboration reads the marks only, each edge at the span from the chain's source to its stage
(for an unbracketed chain, the parser's own node span), so two bracketings are one core term up to
where the source and stages sit in the text: `bcc desugar` prints them identically when the
source starts at one column (checked on `((a >| b) >| c) >| d`, `a >| (b >| (c >| d))` and
`a >| ((b >| c) >| d)`), and they erase alike in any layout
(`corpus/sugar/pipe-bracket.lowered.bc`).

### Programs

- `corpus/pipe-pull.bc`: a `>|` chain of three stages over a generator, and the same chain in `|>`
  (case (iii)): `(i32[20], i32[20])`, counts `3 0 0 3 3 0`, as `gen-pipeline-pipe`.
- `corpus/pipe-bracket.bc` and `corpus/sugar/pipe-bracket.lowered.bc`: three bracketings of one
  chain (one with a `|>` wire in its left side), each erasing as the nested calls: `(i32[25], (i32[25], i32[25]))`.
- `corpus/pipe-mixed.bc`: a mixed `|>`/`>|` chain, a parenthesised `>|` sub-chain spliced at a
  `>|` edge, and a chain into a sink and then a plain function: `(i32[56], (i32[4], i32[28]))`.
- `corpus/pipe-left-row.bc`: left sides that are not generator calls, every `|>` §33's as before:
  an `if` of values and an `if` calling a function without a written row, piped into a function
  that performs a user's effect named `Stream`; a call of a function performing a one-operation
  unit effect (`Wait`, the shape of an iteration effect); a call of `three() -> i32 with
  Yield[i32] = 3` (a written row that over-approximates); a stored generator piped `>|`; a call of
  a function without a written row piped `>|`:
  `((i32[13], (i32[14], (i32[11], i32[13]))), (i32[6], i32[5]))`.
- `corpus/pipe-push-paren.bc`: a `|>` into a parenthesised `|>` chain is §33's, as written:
  `i32[315]` (the review's probe p6).
- `corpus/pending/pipe-alias.bc`: `range(0, 4) >| tot`, `tot(it: P)`: accepted as a stream stage
  (the abbreviation unfolded), then refused where the call would be stored, as `|>` is.
- `corpus/pending/pipe-stream-edge.bc`: an `if` of generator calls piped `>|` into a function that
  performs the program's own `Stream`: refused (`` `sum_items` is not a stream stage ``) until L1,
  where a stage of lib's `Stream` is a stream edge on the connector.
- `corpus/reject/pipe-pull-plain.bc`: `3 >| double`: `` `>|` connects stream stages; `double`
  is not a stream stage ``.

### Baseline

No change to `CDerives`, `Core/`, the checker, the machine, the backends or lib. §33's cases
(i)–(iii) are unchanged: every `|>` edge is elaborated by `pipeStage`, as before. A chain is read
in its normal form, which differs from the parse only where a parenthesised chain of `>|` edges is
the stage of a `>|`, and a `>|` edge takes the span from its chain's source to its stage (the
parser's own span for an unbracketed chain); a `|>` edge is elaborated as before, at its node's
span. Checked: `bcc
desugar`, `bcc check` and `bcc print` of every corpus, bench, docs and book program with `|>`
and of the review's `|>` probes (32 programs, 96 outputs) are identical to main's; the three
probes that differ write `>|`, which main does not parse.

### Open

- L1 (#920): lib's `Stream`; a stage that performs it is a stream stage, keyed on that
  declaration; the stream-edge test on the left side's inferred row, after row inference, with the
  note where none is inferred; the connector.
- The transitional reading ends at L2: `>|` into a source-owning adapter, and the refusal of one
  at `|>`, change there.

---

## 72. Entry 71 — host externs under the chain's adequacy (#963, K1)

### Motivation

`goal791N : HandlerLawN → Goal791N` (§62) covers closed programs with no extern, at `F 1`. A
program that reads or writes through the host is outside it. The design is
`docs/new-core/scope-host-externs.md` (#963), choices C1–C5 as recommended.

### What it adds

**Host externs under the chain's adequacy.** `goal791N : HandlerLawN → Goal791N` is extended
from closed, extern-free programs at `F 1` to programs that call host externs, at any persistent
answer type. No new type former, `CDerives` index, or relation clause. `erwpK`, `KW`, the
tables and `HandlerLawN` are unchanged.

1. **The extern contract `ExternN`** (the form of `ConstN`'s conclusion):

       ExternN T v :=  closedAt 0 v = true ∧ T.Persistent ∧
                       ∀ δ Θ n, Θ.OK → vN T δ Θ n v ∅

   `ExternsMeetN Γx γx` states it slot by slot, each slot live, as Core's `ExternsMeet` does. It is a named
   hypothesis (a `Prop`, not an axiom), stated once for every extern.

2. **What a host is claimed to meet (C1 (b)).** The theorems take `ExternsMeetN` as their
   hypothesis. The claim `bcc trusted` prints for a host extern is a claim about behaviour:
   "on each run, the extern behaves as a typed closed term at its representation". Both
   memberships, Core's `vC` and the chain's `vN`, follow from that claim by the two
   fundamental properties. For the standard models it is a theorem (`stdModel_meetsN`, from
   `HandlerLawN`). For a real host it is assumed, at the same assurance levels as today.
   *Why a host can meet it* (an argument, not checked in Lean): `OrDiverges` is a property of
   finite prefixes, and a finite prefix observes finitely many host answers. A model whose cell
   holds that trace answers the same, and it is a typed closed term. This is the prophecy
   reading §34 already takes for `Stdin`, extended to the clock and sockets.

3. **`Goal791N` restated in place (C5):**

       Goal791N := ∀ cs Γx γx e R, (∀ c ∈ cs, c.OKAt ∅ Γx) → ExternsMeetN Γx γx →
         CDerives ∅ (ctx791 cs ++ Γx) e (.comp (.ret R)) → R.Persistent →
         OrDiverges (substAll (cs.map (·.valAt γx) ++ γx) e)

   The old statement is the instance `Γx = []`, `R = 1`.

4. **A host call is a call (C2).** A call into an extern is ordinary steps of the value that
   closes its slot: neither a machine step nor a stop. Owned buffers move through `⊸`'s
   resource split. Blocking I/O is covered: a call that never returns is a diverging run, which
   `OrDiverges` allows. A cancel cannot land inside a host call.

5. **The finaliser at the externs' context (K1.3, widened).** A lend's finaliser may name
   extern slots, so that a capability cell (`Output`, a file, a socket) lent across a
   suspension or an unwind can be handed back to the host on cancel (e.g. `λr. take_output r`).
   This applies in two places:
   - **The suspending constants:** `Const791.OKAt` takes the finaliser at the externs' context,
     `CDerives Δ Γx d (U (Ref A ⊸ F 1))`. The constant's value is closed by the extern values,
     `c.val[γx]`. Today's premise is the case `Γx = []`.
   - **The checker's unwinding lends** `withbor1U`/`withbor2U`/`withbor3U`: their premise
     `closedAt 0 d` is dropped. `d` stays typed at the rule's context `Γ` (`Ctx.DeadP`, so it
     names persistent slots only) at `U (Ref A ⊸ F 1)` (resp. `U (Mut a A ⊸ F 1)`).
   This removes a premise and adds none. The finaliser stays at `F 1`, effect-free.

### Baseline

- `goal791N` (restated in place; the old statement is an instance), `fundamentalN_all`,
  `handlerLawN_iff`;
- Core's `fundamentalC`, `adequacyC`, `externs_every_run`, `externs_loop_every_run`,
  `io_every_run`: untouched apart from the three `withbor*U` compat lemmas, which are restated
  without `closedAt 0 d`;
- `prog791_orDiverges`, `progRes_orDiverges`, `progCan_orDiverges`, #844's nest instances and #855's `progK_orDiverges`,
  with their statements unchanged;
- every `Const791.OK` instance (each holds at `Γx = []` unchanged), and the five `*S_compat`
  statements unchanged;
- every corpus and kernel program with the same output. The checker's finaliser stays
  `consumeE src` until a later unit lets it name an extern, so no program's term changes in K1.

### Units

- K1.1, built: `ExternN`, `ExternsMeetN`, `gN_of_meetsN`, `Goal791N` restated in place, `goal791N`
  re-proved.
- K1.2, built: the standard models meet `ExternN` (`stdModel_meetsN`, all fifteen, from
  `HandlerLawN`), and Core's end-to-end theorems at the chain, `externs_every_runN`,
  `io_every_runN`, `externs_loop_every_runN` and `io_loop_every_runN`, through `goal791N`
  (`Core/Chain/Externs791N.lean`). The program's input is one more extern slot (`Γ ++ [Bytes]`),
  so the I/O theorems are plain instances of `goal791N`.
- K1.3, part one, built (#1026): `Const791.OKAt Δ Γx` takes the finaliser at the externs'
  context. Each constant is closed by the extern values (`valAt γx`), and `Goal791N` substitutes
  `cs.map (·.valAt γx) ++ γx` with `c.OKAt ∅ Γx`; today's statement is the instance `Γx = []`.
  `w2_takeOutput_okAt`: a lent `Ref Output` whose finaliser hands the cell back by `take_output`.
  Part two, the unwinding lends `withbor1U/2U/3U` without `closedAt 0 d`, is K1.3b.
- K1.4: the kernel instance `progIO` (a lent `stdout` cell, written across a `wait`, resumed and
  cancelled).
- K1.5: `IORun.every_runN` at the checked wrapper; `corpus/io-effects.bc` concluded by the
  extended `goal791N`; `bcc trusted` names it.

K1.3b, K1.4 and K1.5 are not built; each unit's code PR marks its line *built*.

### Open

- **Suspending I/O answered by the platform** (the "stop" reading, scope §4.3): it needs a run
  relation with world steps and a new adequacy theorem. Out of K1 (C2).
- **Effectful finalisers** (I/O performed on cancel through an effect, surface A4): that is K-b
  for the lend form (approved, after K1.3), not K1.
- **A buffer borrowed across an `await`** (#844 Tier 2, `read(sock, &mut buf).await`): the loans
  line.
- **`HandlerLawN` on the models** (C4): `stdModel_meetsN` keeps `HandlerLawN` as a hypothesis. A
  handler-free fundamental would remove it; that is #840's fragment machinery.
- **Pins:** the theorems ask for `pins = []`. A program relying on `PinLaw` stays outside.
- **Descriptors:** the empty final memory covers capability cells, not descriptors (§11). That a
  freed cell's descriptor is closed is the host's claim.
- **Not derived:** the representation congruences at `vN` are expected to be `funext` equations
  under `famL` (risk, measured on `read_byte` first in K1.2). There is no `vC → vN` lemma; both
  follow from the behavioural claim.

---

## 73. Entry 72 — unsigned integers: `U32` and `U64` (#981)

This entry amends §8, as §37 does for floats.

### Motivation

`lib/json` cannot round-trip integers in 2⁶³..2⁶⁴ exactly: there is no unsigned 64-bit type, and
serde keeps them. The host operations are already signless: each is named as the Wasm instruction
that computes it on bit-vectors, and the signed and unsigned readings are separate operations
(`div_s`/`div_u`, `lt_s`/`lt_u`, `shr_s`/`shr_u`, `convert … s/u`). What is missing is a type
that says a value is read unsigned, so that the surface picks the `_u` operations and printing
reads the type.

### What it adds

**Types.**

    A ::= … | U32 | U64                                   (VTy.int w)

`Width` gains `u32` and `u64`, with bits `UInt32` and `UInt64` (`Width.bits`), the same bits as
`w32` and `w64`. Like the other integers, they hold no resource: they are persistent (§10),
`Imm̲ 'b U32 = U32`, and they outlive every lifetime. The relation's `int` clause is "a literal of
the width", so it covers them with no new clause.

**Literals.** `IntLit` gains `u32 n` (`UInt32`) and `u64 n` (`UInt64`), at widths `u32`/`u64`.

**Operations at the new widths.** The grouped integer operations (binary, partial, unary,
`eqz`, tests) apply at `U32` and `U64` with the types they have at `I32` and `I64`, and compute
the same function on the same bits: `ℍ.call` at `u32` is the `…32` family of the host, at `u64`
the `…64` family. **The host structure gains no field.** All the operations are admitted at
the unsigned widths, the `_s` ones included, because they are total functions on bits. Choosing
`div_u`, `lt_u`, `shr_u`, … for an unsigned operand is the surface's job (the follow-up surface
unit), and printing reads the type.

**Conversions.** One new operation family, the bit-preserving change of reading between same-size
integers:

| operation | type |
|---|---|
| `reinterpret_u i` | `I32 ⇒ U32` (`i = i32`), `I64 ⇒ U64` (`i = i64`) |
| `reinterpret_s i` | `U32 ⇒ I32`, `U64 ⇒ I64` |

Each is the identity on bits: one machine step, answering the literal of the other width with the
same bits. Every other conversion composes through them and the existing operations, which are
unchanged. For example, `u32 → u64` is `reinterpret_s`, `extend_u`, `reinterpret_u`;
`u64 → f64` is `reinterpret_s .i64`, `f64.convert_i64_u`; `f64 → u64` is `i64.trunc_f64_u`
(partial), `reinterpret_u .i64`; `u8 → u32` is `extend8_u`, `reinterpret_u .i32`. `convert`,
`trunc` and `trunc_sat` keep their `IWidth` (`i32`/`i64`), whose `Sx` argument already gives the
unsigned reading.

**Overflow.** The kernel's arithmetic wraps, as at `I32`/`I64` (§8). Raising on overflow is the
surface's `checked` sugar, which at the unsigned widths uses the unsigned tests (`add`: the result
`lt_u` an operand; `sub`: `lt_u` of the operands; `mul`: a `div_u` check).

**No** new `VTy`/`CTy` former, `CDerives` rule or index, or relation clause. The `int` former gains
two widths, as for `f32`/`f64` (§37).

### Baseline

`fundamentalC`, `adequacyC`, `hostOp_compatX` (restated at the new arms of `hostArg`/`hostRes`,
same proof: `ℍ.call` answers a literal of the stated type), `fundamentalN_all`, `goal791N`, the
`Persistent`/outlives lemmas for `int`, every `Host` instance (`wasmHost` and the models) with no
new field. Every corpus and kernel program has the same output: no existing term changes, and the
widths are new.

### Units

- Kernel/Support, built (#1018): `Width.u32/.u64`, `IntLit.u32/.u64`, `hostArg`/`hostRes` and
  `ℍ.call` at the new widths, `reinterpret_u`/`reinterpret_s`; the interpreter's arms; every
  exhaustive match elsewhere (Frontend, backends) given the arm of its 32/64-bit sibling, so the
  build stays green. A backend lowers `U32`/`U64` to the machine's `i32`/`i64` (signless), and
  `reinterpret_*` to nothing.
- Surface (follow-up): the type names `u32`/`u64`, literals with a range check, `_u` operation
  choice for `<` `<=` `>` `>=` `/` `%` `>>`, `as` conversions, `checked` ops, printing and
  parsing in `lib`.

The surface part is not built: until it lands, the surface refuses the operators at `u32` and
`u64`.

### Open

- Narrower unsigned widths (`U16`) and `I8`/`I16`: not asked for.
- Whether `U8` gains arithmetic now that the grouped operations are admitted per width: not in
  this entry (`U8` keeps §8's "no arithmetic of its own").

---

## Status

What implements each entry is kept one paragraph per file in `docs/status/`: the paragraphs
written before the split in `docs/status/legacy/`, in their order, then one file per entry,
`docs/status/<entry>.md`. `scripts/status.sh` prints them in order. An entry's status is a new
file, or an edit to that entry's file (`docs/status/README.md`).

---

## Changelog

The changelog is kept one entry per file in `docs/changelog/`, named by the entry's version.
`scripts/changelog.sh` prints the list, newest first, and `scripts/changelog.sh --version` the
current version. A new entry is a new file, numbered by docs-foreman
(`docs/changelog/README.md`).
