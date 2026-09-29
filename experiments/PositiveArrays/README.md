# PositiveArrays: arrays as the positive indexed tensor

**Question.** Richter, Böhler, Weisenburger and Mezini, *Compiling with Arrays* (ECOOP 2024,
arXiv:2405.18242, `[CC-arrays]` below), read arrays as the positive dual of the function type:
an array is eliminated by a pattern match that binds one variable per index. What does that
eliminator become in a linear setting with borrows and run-time lengths? Does it give K2 of
`docs/strings-slices-design.md` (an owned array lent as a family of element borrows, with no
cell) a cleaner statement and a proof? How do K3 (run-time split) and K0 (the counted loop)
fit? The working hypothesis is that arrays, records and structs are all instances of one indexed
tensor `⊗_{i∈I} A_i`.

Build: `lake build PositiveArrays`. The library imports `Core` and nothing imports it.
`Paper/`, `Support/`, `Examples/`, `Core/`, `Frontend/` and `Backend/` are unchanged. The
experiment builds at `main`.

| file | contents |
|---|---|
| `MapOwn.lean` | the owned eliminator: **`wpTS_arrayMap`**, each element consumed once by a persistent indexed body, results an `Array B`; `arrMap_compatX`, the constant `array_map`; `famLenBound`, from §9's length bound |
| `Partial.lean` | `wpTS_M_framePartial`: lend the places satisfying a predicate, and keep the others owned inside the callback |

**Promoted to `Core/`** (SPEC §9): the indexed tensor, both frame inductions and the split
(`Core/SliceFrames.lean`: `sepList`, `wpTS_M_frameList`/`Fam`, `wpTS_I_frameList`/`Fam`,
`vP_fam_split`/`join`, `sepList_partition`), and K2 with its constants (`Core/Slices.lean`:
`sliceBorrowM_compatX`, `sliceBorrowI_compatX`). The names below refer to those files.

There is no `sorry` and no `axiom`. Every result's `#print axioms` is within `[propext,
Classical.choice, Quot.sound]`.

## Verdict

- **K2 is proved at `Mut` and at `Imm`**, against the typed world as it is, with the design's
  term (`withbor`'s `λa. λg. (a, g () a)`, which passes the handle) and no model change.
  The statement is "a borrow of an indexed tensor is an indexed tensor of borrows". The proof is
  the per-component frame iterated over the index set: `wpTS_M_frameList` and
  `wpTS_I_frameList`, by induction on a list of places. The risk the design rated medium and
  medium-plus is now low. What remains is promotion: a spec entry, a `CDerives` constant, and a
  `fundamentalC` case that is these lemmas.
- **K2 has side conditions the one-cell rules do not all have.** `A` and `B` must each outlive a
  lifetime of `Δ`, at both modes. That is `withbor2`'s condition on `A`, plus the condition
  `withborF2` (SPEC §5) already carries on its result. `withbor1` has neither. The proof uses
  them: with more than one frame the callback runs below every frame but the innermost, and
  what it returns (and, at `Imm`, the payloads handed back) must be reboxed at each outer
  frame's lifetime. Whether they are needed is not verified. They are not known to be blocked
  without them. For text (`A = u8`) and for results that hold no borrow they cost nothing.
- **The class hypothesis holds at the model, not at the types.** One lemma covers a struct's
  fields (a static list of places, heterogeneous types) and an array's elements (a run-time
  range). At the types there are two typings. The static one is derivable today by nested
  `withbor` (`experiments/Places`). The run-time one needs a constant, because the nesting depth
  is a run-time value. Partitions of the index set are splits of the family, for any predicate
  (`sepList_partition`). The types express static subsets and contiguous run-time ranges.
  Strides and other predicates are expressible in the model and have no value form yet.
- **The eliminator is a bulk operation, not a fold.** In the paper a pattern variable can be
  used only under an index scope. Read linearly at a run-time `n`, that makes each element
  consumed once by a body run once per index. The body is persistent and indexed,
  `!(I32 ⊗ A ⇒ B)`, the `&` form, and the result is again indexed (`Array B`): a map. Proved for
  owned arrays at `wpTS` (`wpTS_arrayMap`), and as a constant given one named fact
  (`arrMap_compatX`); `array_free` is its instance at `B = 1`. K0 is a
  different eliminator (a fold over the index set with loop-carried state), and it is still
  needed.
- **One gap surfaced, now closed.** `tab` builds `arrLen c` cells (`c` if `c < 2³¹`, else
  `0`). A constant that returns an array as long as its argument, such as a map, needs the
  relation to carry `c < 2³¹` (`FamLenBound`). SPEC §9's clause now carries it, and
  `famLenBound` derives the fact.

## 1. The paper, read first-hand

The whole paper was read, all 24 pages. The figures were read from the extracted text, which
loses part of their typesetting. The artifact on figshare was not downloaded.

**The idea.** Polarized type theory distinguishes positive types, defined by constructors and
eliminated by pattern matching, from negative types, defined by destructors and introduced by
copattern matching (§3.1). Functions are negative. The positive function type needs a
higher-order judgment: its eliminator binds a *variable of type "term in the context of a
variable"*. The paper avoids that by restricting the domain to `Fin n` and calling the result an
array (§3.1, "Interpreting positive function types as arrays"):

    Intro   Γ, x : Fin n ⊢ b : B
            ──────────────────────
            Γ ⊢ (for x. b) : n ⇒ B

    Elim    Γ ⊢ f : n ⇒ B    Γ, x : (a : Fin n ⊢ B) ⊢ c : C
            ──────────────────────────────────────────────
            Γ ⊢ let (for a. x) = f; c : C

    Beta    let (for a. x) = (for a. b); c ≡ c[x := b]

"Consider `b[a := 2]` as `b₂`, and `let (for a. b) = f; c` as `let (b₀, …, b_{n−1}) = f; c`":
the match binds `n` variables. The eliminator is used only in the sugar
`let for i. (x = e₁); e₂`. In the IR (§4.2, Figure 3), a variable bound under `for i` is used
only inside another `for i` scope (the scope contexts `C[for i:n. ·]`).

**What it buys them.** The let-for commuting conversion

    let y = (for i. let x = e₁; e₂); e₃  ≡  let (for i. x) = (for i. e₁); let y = (for i. e₂); e₃

is safe, unlike let-fun, because array construction is eager: each `e₁` runs once per index on
both sides. Normalizing with it gives maximal fission. Every loop body is one primitive, so
CSE and loop-invariant code motion become the ANF algorithms. Booleans get a second device:
conditionally defined variables (`let (if e. x)`), which let branches "trickle down" instead of
duplicating the continuation.

**What they mechanize, and in what.** Lean 4. Polara, the surface language, is intrinsically
typed PHOAS. Partial evaluation is NbE, and in it arrays are modelled as functions. AiNF is
first-order syntax, needed for CSE's equality tests. The translation is CPS with "smart
binding", and CSE carries a renaming. Theorems 1–3 are termination, type preservation, and
maximal fission. Each holds *by construction*: Lean's termination checker, intrinsic typing,
and the shape of the `AINF` datatype. There is no semantic-preservation theorem for the
translation or the optimizations, and no dynamic semantics beyond NbE's denotation. Sizes are
static (`n` is part of the type) and the language is pure and total. It has no linearity, no
effects, no mutation, and no aliasing. Polymorphism in `n` comes from the host (a Lean function
from `n` to a term).

**What is not there, and is here.** The paper never meets ownership. Its elements are values to
duplicate or drop at will. The linear reading below is ours.

## 2. The class: the indexed tensor `⊗_{i∈I} A_i`

In the model an indexed tensor is the iterated separating conjunction of its leaves over the
places its index set names (`Index.lean`):

    sepList P [ℓ₁, …, ℓ_k] = P ℓ₁ ⋆ … ⋆ P ℓ_k

The paper's contextual variable `x : (a : Fin n ⊢ A)` *is* the leaf predicate `P` of
`𝒱⟦[L]⟧(ℓ, n) = ⊛_{i<n} 𝒱⟦L⟧(ℓ + i)` (SPEC §9): a family of facts indexed by position.

| instance | index set | leaves | typed today by |
|---|---|---|---|
| record or struct (SPEC §5; `LeafPlaces`) | static list of places, heterogeneous | `Ref A_i` / `Mut 'c A_i` / `Imm 'c A_i` | `⊗` of leaves; family borrows by nested `withbor` |
| array or slice (SPEC §9) | run-time range `[ℓ, ℓ+n)` | homogeneous | `[L]`, the value `(ℓ, n)` |
| matrix, row-major | range of ranges | homogeneous | an array of length `r·c` (a row is a contiguous sub-range; a column is a stride) |
| nested array `Array (Array A)` | dependent | the inner handles are *payloads* of the outer leaves | not one index set: the inner leaves sit behind the outer cells (the parent-cell shape `FrameEnd` excludes), so it flattens only if the storage is flat |

The dual is the `&` over indices: a function `I → A`, observed one index at a time and computed
on demand. In a linear setting only a persistent one can be observed at every index, so the
`&` form is `!(I32 ⇒ A)`. For `Imm` data the two coincide: `[Imm 'x A]` is duplicable
(`array_copy`), and `array_get` observes it at any index.

What makes arrays special is only that `|I|` is a run-time value. A static family's borrow is a
derivation whose depth is `|I|` (`experiments/Places`). A run-time family's borrow is one
constant whose *proof* has depth `|I|`. The proof is the same induction in both cases
(§4).

## 3. The eliminators

### The paper's eliminator, read linearly

`let (for a. x) = f; c` with `x` usable only under an index scope, at a linear `x`, forces:

1. each `x_a` is used exactly once, so exactly one index scope consumes `x`;
2. that scope runs its body once per index, so whatever the body captures is used `n` times
   and must be persistent;
3. the scope's result is indexed again.

Up to the let-for conversion, `c` is therefore `let y = (for a. e(a, x_a)); c′` with `x` not in
`c′`. The eliminator is a **bulk operation, a map**:

    elim : !(I ⊗ A ⊸ B) ⊗ ⊗_{i∈I} A  ⊸  ⊗_{i∈I} B          (I32 for I at run-time n)

The body is the `&` form over the indices, so elimination is a cut between the positive tensor
and a negative family of consumers. With a run-time `n` the body's type is fixed: it cannot
mention `n` variables, and it does not need to, because the index is its argument. This is
**not a fold**. The paper's reductions (`sum`) are separate constants on arrays, not part of
the eliminator. A loop with state carried from index to index is a different eliminator
(*Relation to K0*, below).

### (a) Owned `Array A`

    array_map : !(!(I32 ⊗ A ⇒ B) ⊗ Array A ⇒ Array B)
    term      : tab (n, λi. case idx((ℓ, n), i) { inl c → f (i, free c) | inr _ → () })

It is one `tab` whose tabulator takes the `i`-th element out of the source (`idx` then `free`)
and hands it with the index to `f`. `wpTS_arrayMap` proves it at `wpTS`: from the source's
`n` owned leaves, every element is consumed exactly once, in index order, the results form an
`Array B`, and no source cell remains. The proof is `tabFill_wp` (Core's fill of `tab`) with a
third range, the unconsumed source, shrinking one leaf per step (`mapFill_wp`).

`array_free : !(!(A ⇒ 1) ⊗ Array A ⇒ 1)` (SPEC §9, `arrFree_compatX`) is the instance at
`B = 1`, with the index dropped and the unit results discarded.

`wpTS_arrayMap` carries `arrLen n = n`. `arrMap_compatX` proves the closed constant
`array_map` (the term above under `λp`, two `let`s) sound. It needs `FamLenBound`:
`tab (c, g)` places `arrLen c` cells, `c` when `c < 2³¹` and `0` otherwise, while
`𝒱⟦[L]⟧(ℓ, c)` is `c.toNat` leaves for every `c`. For a family with `c ≥ 2³¹` in the relation,
`tab` would build an empty result and leave the source's leaves, and `B` has no destructor in
general, so nothing could consume them. `FamLenBound` states the missing fact: every family in
the relation has `tab`'s length. §9's clause now carries `⌜c < 2³¹⌝`, and `famLenBound` derives
it. The same fact serves any constant whose result array has its argument's length.

### (b) `Imm`: K2 at `Imm`

    slice_borrow : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B

The eliminator binds an `Imm 'x A` per index. `sliceBorrowI_compatX` proves it with no cell.
Today `[Imm 'x A]` (`ArrayImm`) comes only from `withload` of an `Imm` of a cell holding the
handle. Inside the callback, `⊗` and `&` coincide, so the family is consumed either by a map
whose body reads an `Imm 'x A`, or by random access (`array_get`, after `array_copy`).

### (c) `Mut`: K2 at `Mut`

    slice_borrow : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B

"A borrow distributes over `⊗ⁿ`". `sliceBorrowM_compatX` proves it. The leaves are `mut`
cells at one lifetime, each at the top level of the resource, none below another. Each is used
linearly or forgotten (a `mut` leaf holds no `own` cell).

### Generically over an index set

At the model, one lemma per mode covers every finite index set, with a type per place:

    wpTS_M_frameList :
      ⊛_{ℓ∈I} 𝒱⟦Ref (T ℓ)⟧(ℓ) ⋆ ⋔α. (⊛_{ℓ∈I} ℓ ↦ M_α 𝒱⟦T ℓ⟧ ─⋆ wp(e){Φ})  ⊨  wp(e){Q}
        given  ⊛_{ℓ∈I} 𝒱⟦Ref (T ℓ)⟧ ⋆ Φ ⊨ Q,  Φ ⊨ [β′]Φ,  𝒱⟦T ℓ⟧ ⊨ [β]𝒱⟦T ℓ⟧

and `wpTS_I_frameList` at `Imm`, where the callback runs at every list `Ext`-above the original.
K2 is the instance at `I = [ℓ, ℓ+n)`. The field borrows of a struct are the instance at the
struct's static list of leaves, which `experiments/Places` derives syntactically by nesting.

### Relation to K0 and to finite `for`

There are two eliminators, and a strings plan needs both.

- **Map** (this section) is the paper's `for`: no state flows between indices. It needs no new
  loop primitive, since `tab` is the loop, and it is total.
- **Fold** threads a linear state through the indices in order: `sum`, parsing digits, UTF-8
  decoding, `find`. `tab`'s tabulator is persistent, so it cannot carry linear state. This is
  K0's job (`count_fold`), the eliminator of the index set `Fin n` itself, by counting.

A finite `for` elaborates to a map when its body carries no state from one index to the next,
and to K0 otherwise. Stage 9's "bounded `for` is K0" stays right for the stateful case.

## 4. Proofs

| result | statement |
|---|---|
| `wpTS_M_frameList`, `wpTS_M_frameFam` | `n` Mut Frames around one expression, over a list of places (types per place) and over a range |
| `wpTS_I_frameList`, `wpTS_I_frameFam` | `n` Imm Frames; the callback's list quantified over `Ext`; leaves carry their frames' records |
| `sliceBorrowM_compatX` | K2 at `Mut`: `SemV Δ Γ withbor (sliceBorrowMTy x ⊓Δ A B)` |
| `sliceBorrowI_compatX` | K2 at `Imm`: `SemV Δ Γ withbor (sliceBorrowITy x ⊓Δ A B)` |
| `vP_fam_split`, `vP_fam_join` | `(ℓ, n) ≅ (ℓ, i) ⊗ (ℓ+i, n−i)`, at every leaf type |
| `sepList_partition`, `sepList_unpartition` | any predicate on the places splits the family and joins it back |
| `wpTS_M_framePartial` | lend the places satisfying `p`; the callback owns the rest |
| `wpTS_arrayMap` | the owned eliminator, at `wpTS`, given `arrLen n = n` |
| `arrMap_compatX` | `array_map : !(!(I32 ⊗ A ⇒ B) ⊗ Array A ⇒ Array B)` as a closed constant |

**How the design's named obstacles came out** (`docs/strings-slices-design.md` §5.2 asked to
check them at `n = 2`; the induction settles every `n`):

- *The inner `fresh` with the outer frame's `mut` cell in the resource.* Each inner `⋔` is
  discharged at the bound `@R` of its whole resource (`ResU.exists_atLife`), met with the outer
  frame's lifetime and the callback's bound. No lemma about a particular cell is needed.
- *A `γ` below both frames.* The frames' lifetimes strictly decrease, and the callback runs at
  the innermost. The outer leaves are shortened to it by `[TR]` 6.118/6.114
  (`ptoMutS_antitone`, `ptoImmS_antitone`).
- *The rebox at the outer frames.* Frame `j`'s postcondition is under `[α_j]`, but the callback
  returns in `Res_{α_n}`. The frame lemmas take `Φ ⊨ [β′]Φ` and choose every `α_j ⊑ β′`. K2
  gets that from 6.60 (`vC_outlives`) at `B`'s side condition. The returned leaves' payloads
  need `𝒱⟦A⟧ ⊨ [β]𝒱⟦A⟧`: `MutFrame`'s own premise at `Mut`, and a new side condition at `Imm`.
- *`Imm`'s records.* The hypothesis quantifies over every list `Ext`-above the original. A
  leaf's record survives later frames because `Ext` keeps the records relevant to the leaf's own
  `imm` cell (`immLeaf_ext`). 6.64 wants its postcondition `Ext`-stable, which the nested
  continuation is not, so the induction runs at the stable `⊛ 𝒱⟦Ref A⟧ ⋆ Φ` and weakens after.

**Not derived.**

- K2 as a `CDerives` rule and `fundamentalC` over it, and a closed program using it, run by
  adequacy. That is promotion, and it needs a spec entry first.
- Whether K2's `A`/`B` side conditions can be dropped. The design's fallback (a persistent `B`)
  is not needed: the condition is `VOutlives`, which is weaker.
- An `imm` reborrow of a `mut` family (the design's K2′). It is the same list induction with
  `withbor3`'s anti-frame per leaf, and was not attempted.
- K3 and K5 as constants (the host-comparison terms). K0 and K4 are in `Core/`.
- Map fusion and fission are two-run properties (`experiments/TwoRun`); they were not
  attempted.

## 5. K3: splitting is partitioning the index set

`vP_fam_split` is `⊗ⁿ ≅ ⊗ⁱ ⊗ ⊗ⁿ⁻ⁱ` at the relation, for every leaf predicate at once. It needs
no frame, no lifetime and no model change, because the leaves of a family are at the top level
and no cell owns another. That is exactly why a *borrowed* family splits and a borrowed `Ref`
of a structure does not (`imm_view_rejected`).

K2 and K3 compose in one order: **lend, then split**. The halves of `[Mut 'x A]` are at `'x`,
disjoint, and each a family. An owned split is sound in the model (`vP_fam_split` at
`L = Ref A`). It stays excluded because a block is freed once (design §5.4, block provenance).
The model also has the partial lend (`wpTS_M_framePartial`): lend a sub-family and keep the rest
owned in the callback. For arrays that would need an owned sub-array value, so it too waits on
provenance. For a struct it is the ordinary disjoint field borrow.

**Which partitions are expressible:**

| partition | model | types |
|---|---|---|
| a static subset of a struct's fields | `sepList_partition` | yes: `⊗` of leaves, derivable (`Places`) |
| contiguous run-time ranges | `vP_fam_split` | yes: `(ℓ, i)`, `(ℓ+i, n−i)`; K3 |
| strides (a matrix column, even/odd) | `sepList_partition` at `m ≡ r (mod s)` | no: `[L]`'s value has no stride; a strided family needs `(ℓ, n, s)` and `idx` at `ℓ + i·s` |
| any other predicate | `sepList_partition` | no |

**Partial borrows of structs come from the same machinery as slices.** Rust's view types and
partial borrows (`&mut self.a` while `self.b` stays usable) are a top Rust wishlist item. Here
they are the static instance of the lemma that proves K2: `wpTS_M_frameList` at a subset of the
struct's leaves, with the rest kept (`wpTS_M_framePartial`). At the types, the static instance
is already derivable (`withborF2`, `withborS` in SPEC §5). A surface for "borrow these fields,
keep those" is elaboration over it.

## 6. `tab`, the `&` form, and `idx`

`tab : !(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)` converts the `&` form into the `⊗` form. It observes the
persistent function at every index, eagerly and in order, and stores the results. It is the
paper's `Intro`. The converse, `⊗ → &`, exists only where the leaves are duplicable. At `Imm`,
`array_copy` and `array_get` make `[Imm 'x A]` observable at any index, so the forms coincide.
At owned and `Mut`, the per-index observation is a lens that keeps the rest (`array_replace`,
K5), not a projection.

**`idx` should stay a primitive**, for `Imm` too:

- the eliminator is a traversal, `O(n)` per access, while random access is `O(1)`;
- the paper keeps `get` as a constant beside its positive eliminator (§4.1, `get`), for the
  same reason;
- `idx`'s out-of-range answer is a sum, the only bounds behaviour, and no eliminator
  reproduces it.

## 7. Their compiler and ours

AiNF is ANF closed under let-for and let-if commuting conversions. Each `for` binds one
primitive, so fission is maximal, and CSE, dead-code elimination and loop-invariant code motion
become the plain ANF algorithms. That suits numeric array code: pure, total, static sizes,
bodies with no effects to reorder. Our generator and pipeline fusion suits streaming: a
pipeline runs as one loop with no intermediate arrays, over sources that may not end, with
effects in order. Fission is valid for us only when the bodies' effects commute, which is a
two-run property we do not have (`experiments/TwoRun`). AiNF is worth revisiting only for a
pure sublanguage, `map` bodies at persistent element types (`i32`, `u8`) over arrays. It is
not a backend IR for now.

## 8. Implications for the strings plan

- **S1 (K0, K1).** Unchanged. K0 is still needed: it is the stateful eliminator, and the
  digit loop of P2, `find`, UTF-8 decoding and `utf8-count` all carry state. One refinement: a
  state-free `for` over a view can elaborate to a map (`tab`), with no K0 loop, and is total.
  Add `⌜c < 2³¹⌝` to §9's `[L]` clause before any constant that returns an array of its
  argument's length, such as a map or a clone.
- **S2 (K2).** De-risked. Both compatibility lemmas exist, with the design's type and term.
  The S2 work is now:
  - the spec entry: §9's Open item becomes a constant with the side conditions "`A` and `B`
    outlive a lifetime of `Δ`";
  - the `CDerives` constant and its `fundamentalC` case, ported from `Index`, `FrameFam`,
    `ImmFam`, `K2Mut` and `K2Imm` (about 700 lines with comments);
  - the checker's constant, and the §5.1 lend row.

  The `Imm` lend needs no cell, so `&string` and `lit_view` pay no scoped allocation. The side
  conditions hold for `u8`, `i32` and every result without a borrow. They exclude, for now,
  elements or results holding a borrow that does not outlive any lifetime of `Δ`.
- **S3 (K3–K5).** K3's relation-level content is proved here (`vP_fam_split`, `vP_fam_join`),
  and the constant is the host-comparison term around it. K4 and K5 are unchanged. The order is
  fixed: lend, then split. Owned split stays out, for the lowering reason, not the model's.
- **Beyond strings.** Partial struct borrows and slices are one lemma. A strided view (matrix
  columns) is the next partition. It needs a value form, not a proof technique.

## Open

- Promotion of K2 (spec entry, rule, `fundamentalC` case, checker), and the §9 length bound.
- Whether K2's side conditions are needed.
- K2′ (an `imm` reborrow of a `mut` family) by the same induction with `withbor3`.
- Strided families: a value `(ℓ, n, s)` and `idx` at `ℓ + i·s`.
- Map fusion and fission as two-run laws.
