# Prior art: splitting and projecting borrows

This is a literature survey for the language designer. It records what other systems do; it
decides nothing. It complements `docs/prior-art-memory-model.md`, whose Q1 (same-lifetime field
projection), Q2 (`split_at_mut`) and Q7 (lenses, backward functions, prophecies) are not repeated
here.

The working hypothesis under test is that a few laws would give field projection, lens-style
mutable access and iterator views:

| Law | Statement |
|---|---|
| L1 | `Imm_α (P ∗ Q) ⊣⊢ Imm_α P ∗ Imm_α Q` (Imm distribution) |
| L2 | `Mut_α (P ∗ Q) ⊢ Mut_α P ∗ Mut_α Q`, reassembled when `α` ends (multiplicative split) |
| L3 | `Mut_α (P ∗ Q) ⊢ Mut_α P & Mut_α Q` (additive or lens access: one field at a time) |
| L4 | `Imm_α (A & B) ≅ Imm_α A ⊗ Imm_α B` (a Seely-shaped law for a read mode) |
| L5 | borrowing a computation or codata: views as get/put, iterators as ν-objects |

Priorities, as the user set them: L1 and L3 get the depth. L4 and L5 come after them. L2 is a
stretch goal and appears only as a table column and one line per model.

Citation conventions. `[CONF]` and `[TR]` are Wagner et al. (2025) and its technical report.
Every claim about another paper cites a section, figure or rule name from a full text that was
read, unless it is marked *(unverified)* or *(secondary)*. Sources are listed at the end.

---

## 0. Where BoLo stands on each law

In BoLo, `Imm` is not a modality over propositions. It is a borrowed points-to,
`ℓ ↦I_α P̂` (`[TR]` p. 5: `∃β, v, ρ′. ρ = ℓ ↦ imm(β, v, ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊔β`). So at the
cell level L1 reads as follows. From `ℓ ↦ imm({α}, (ℓ₁, ℓ₂), ρ₁ ● ρ₂)`, where `ρᵢ` owns `ℓᵢ`,
obtain `ℓ₁ ↦ imm({α}, u₁, ρ₁/ℓ₁)` and `ℓ₂ ↦ imm({α}, u₂, ρ₂/ℓ₂)` at the **same** `α`.

What is already printed or already checked:

- **L1 at a fresh, shorter lifetime is printed.** `Imm̲ 'b (T₁ ⊗ T₂) ≜ Imm̲ 'b T₁ ⊗ Imm̲ 'b T₂`
  and `Imm̲ 'b (Ref T) ≜ Imm 'b T` (`[TR]` p. 2, `[CONF]` Fig. 8). Underneath them are
  `↺⋆` (`[TR]` 6.125) and `↺V1` (6.131). The model already splits a witness per location:
  `reb_α(ρ)` (`[TR]` p. 5) chooses a partition `π : dom(ρ′) → Res`, and case 1 turns each owned
  cell into `imm({α}, v, π(ℓ)/ℓ)` with its own piece of the witness. The per-location
  construction exists. It is used only at a fresh `α`, inside a `withload` scope, and the image
  is subtracted before the final `↭` (6.52, 6.59).
- **L1 at the same lifetime is refuted in the current model.** `experiments/Projection` and
  `experiments/Relaxed` refute it. The refutation that survives relaxing the typed world is
  `[TR]` 6.38 (`frame_view_excluded`). When a frame for `ℓ ↦ imm({α}, v, ρv)` ends, `own`
  cells return at every location `ρv` owns. So no resource reached by `↭` may hold a cell at
  those locations, and a projected view is such a cell.
- **Deep immutability is not what blocks L1.** `[CONF]` §5 says BoLo's model "enforces deep
  immutability of the data an immutable borrow points to". A projected `Imm_α A` of an
  already-immutable pointee is consistent with that. The obstruction is the representation: one
  indivisible witness per `imm` cell, plus 6.38's restore.
- **L3 at a fresh lifetime appears to be derivable from the printed axioms (unverified, not
  checked in Lean).** `withswap : Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂` (`[TR]` p. 2)
  hands its callback the owned payload. With `T₁ = Ref A ⊗ Ref B`, the callback can
  `withbor` either component at a fresh `'b` and then return the pair. Nesting two `withbor`s
  gives both components at once, which is an L2 at fresh lifetimes. Neither program has been
  typed or run here.
- **L5 is closed off by `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk`** (`[CONF]` Fig. 8 clause (4)). `SPEC.md` §2
  (`!T`) and `experiments/BorrowedClosures` stage 1 (`reborrow_self_of_imm`) reopen the
  closures that capture nothing linear. `experiments/CBPVWorld` keeps `Imm̲ (U C) = Unk`.
- **L4 has no counterpart yet.** BoCa has no `&`, and in the CBPV core `Imm̲ (U C) = Unk`.

---

## 1. Summary table

"Same `α`" means the parts keep the borrow's own lifetime; "fresh" means a strictly shorter,
scoped lifetime. "n/a" means the system has no such construct.

| | Charguéraud–Pottier RO (ESOP'17) | RustBelt lifetime logic (POPL'18) | Leaf (OOPSLA'23) | Marshall–Orchard (OOPSLA'24) | Pure Borrow (2026) | DRFCaml modes (POPL'25) | BoLo today |
|---|---|---|---|---|---|---|---|
| **L1** | **partial**: `RO(H₁ ∗ H₂) ⊢ RO H₁ ∗ RO H₂` only; the converse is false (§2.1, Fig. 1, fn. 2). No lifetimes; RO cannot leave its block | **yes, same κ, at the type level**: `⟦τ₁×τ₂⟧.shr(κ,t,ℓ) := ⟦τ₁⟧.shr(κ,t,ℓ) ∗ ⟦τ₂⟧.shr(κ,t,ℓ+size)` (§4.3). Fractured borrows (LftL-bor-fracture) are per location | **partial**: `⊢` from Guard-Split (`P ∗ Q ⤔ P`) and persistence of guards. `∗`-recombination is unsound in general (§3.2, App. B.4); only Guard-And for `∧` of point props | **yes, both directions, type level**: `push : &p(A⊗B) → &pA ⊗ &pB`, `pull` (§5.2), at every permission `p`. No lifetimes | **yes (⊢), same α**: `splitPair :: Borrow α k (a,b) ⊸ (Borrow α k a, Borrow α k b)` with `k = Share` (Fig. 12) | **yes by construction**: modes are deep (§2.3); the value relation interprets product components at the product's mode (§5.2). `shared` is a mode, not a lifetime-indexed borrow | **fresh only** (`Imm̲` over `⊗`; `[TR]` 6.125, 6.131). Same `α` refuted (`experiments/Projection`, `experiments/Relaxed`) |
| **L2** | n/a (no mutable borrows) | **yes, same κ**: LftL-bor-split (Fig. 4); inverse LftL-bor-merge (Jung thesis §11.5) | n/a | **yes**: `push` at `p = 1` | **yes**: `splitPair`, `splitAt` at `k = Mut` (Fig. 12) | n/a (modes on GC'd values) | fresh only, and only apparently (withswap+withbor, unverified) |
| **L3** | n/a | **yes**, as a corollary of LftL-bor-split | n/a | yes, via `push` | yes, via split | n/a | fresh only, apparently (withswap+withbor, unverified); same `α` open |
| **L4** | not stated (no additive connective) | not stated | not stated. The nearest is Guard-And for `∧` | not stated. □ᵣ does not distribute in general (fn. 5) | not stated | not stated | no `&` in BoCa; `Imm̲ (U C) = Unk` in the CBPV core |
| **L5** | n/a | function values are `Copy`, with persistent sharing (§4.3); `IterMut` is verified in RustHornBelt, not RustBelt | n/a | refs may not hold functions for preservation (Thm 6.7 caveat) | not checked | closures carry modes (§2.4, §5.2); details unverified | `Imm̲ (⊸) = Unk`; `!T` (spec §2) |

Two constructions support L3 without L2 (§2.7): Fähndrich–DeLine *focus*, and Aeneas
backward functions.

For L4 the only law of the right shape is for a duplicable modality, not for a borrow: the
Seely isomorphism for `!` in linear logic, and Iris's persistence modality `□` (§4).

---

## 2. System by system: what model structure pays for each law

### 2.1 Charguéraud & Pottier, *Temporary Read-Only Permissions for Separation Logic* (ESOP 2017)

- **Laws.**
  - `RO(H₁ ∗ H₂) ⊢ RO(H₁) ∗ RO(H₂)`. The reverse entailment is false (§2.1, Fig. 1).
    Footnote 2 gives the reason: it would give
    `RO(l ↪ v) = RO(l ↪ v) ∗ RO(l ↪ v) = RO(l ↪ v ∗ l ↪ v) = RO[False]`.
  - The information loss can be avoided with
    `RO(H₁ ∗ H₂) = RO(H₁ ∗ H₂) ∗ RO(H₁) ∗ RO(H₂)`.
  - RO commutes with `∨` and `∃`, is idempotent and covariant, vanishes on pure assertions, and
    makes permissions duplicable (Fig. 1). The logic has no additive conjunction.
- **Scope.** RO permissions obey a block discipline: the read-only frame rule has the side
  condition `normal H′`, so "no read-only permissions are allowed to exit the block" (§2.2).
  There are no lifetimes. §6 names lifetime annotations on read-only permissions as open.
- **Model structure (§4.1, Figs. 6–7).**
  - A heap is a pair `(f, r)`: a read-write memory and a read-only memory with disjoint domains.
  - Composition takes the disjoint union of the `f` parts and the *agreeing* union of the `r`
    parts.
  - `RO(H) ≜ λh. h.f = ∅ ∧ ∃h′. h.r = h′.f ⊎ h′.r ∧ H h′`. The whole footprint of `H` is moved
    into the per-location read-only memory, which is why the modality distributes over `∗`.
  - Triples require `h₁′.r = h₁.r` (Definition 1): the read-only part comes back unchanged at the
    end of the block, all at once.
- **L2.** No. C–P has no mutable borrows; read-write permissions are ordinary `∗`.

### 2.2 RustBelt and the lifetime logic (Jung, Jourdan, Krebbers, Dreyer, POPL 2018; Jung PhD thesis 2020, ch. 11)

- **Laws.**
  - LftL-bor-split: `&κ_full (P ∗ Q) ⇛ &κ_full P ∗ &κ_full Q` (Fig. 4), at the same κ.
    LftL-bor-merge is its inverse (thesis §11.5).
  - LftL-bor-fracture turns a full borrow of `Φ(1)` into a persistent fractured borrow
    `&κ_frac Φ`, when `Φ(q₁+q₂) ⇔ Φ(q₁) ∗ Φ(q₂)` (Fig. 5, §5.3).
  - For shared references, each type picks a sharing predicate. Products define it as `∗` of
    the components' predicates at their offsets (§4.3). Simple `Copy` types use
    `∃v. &κ_frac(λq. ℓ ↦^q v) ∗ ▷Φτ(t, v)`. Sharing predicates must be persistent
    (ty-shr-persist).
- **What pays for L1.** Per-location fractions inside fractured borrows. L1 for shared
  references is *definitional* at the type level. It is created from a full borrow through
  `ty-share`, which uses LftL-bor-split and LftL-bor-fracture. So in RustBelt, L1 for shared
  borrows is *built on* L2 for full borrows.
- **What pays for L2 and L3: boxes and slices (thesis §11.6.1, Fig. 11.11).**
  - Each lifetime's invariant holds a borrow box with total content `P = ∗ᵢ Pᵢ`, partitioned
    into slices.
  - Slice-split and Slice-merge re-partition a slice without changing `P`.
  - Box-empty and Box-fill take out or put back *the whole* `P` regardless of how it is sliced.
  - Inheritances (`[†κ] ⇛ ▷P`) live in a second box whose total content mirrors the first.
  - So splitting changes only the slicing, and ending κ restores the whole.
- **L3 and L2 in this structure.** L3 follows from L2, because `P ∗ Q ⊢ P ∧ Q`. So yes, L2
  comes from the same structure.
- **Slices and `split_at_mut`.** The POPL'18 verified libraries do not include slices. The
  `index_mut` walkthrough splits the vector borrow with LftL-bor-split and *drops* the rest
  (§5.1); footnote 9 says this uses affinity. RustHornBelt later verifies `split_at(_mut)`,
  `as_(mut_)slice` and `iter(_mut)` (Matsushita et al., PLDI 2022, §6 list).

### 2.3 Leaf (Hance, Howell, Padon, Parno, OOPSLA 2023)

- **Laws (Fig. 4).**
  - Guard-Split, `P ∗ Q ⤔ P`. With Guard-Trans, `G ⤔ P ∗ Q` gives `G ⤔ P` and `G ⤔ Q`, and
    guard propositions are persistent. That is L1 left to right.
  - The converse, `(G ⤔ A) ∗ (H ⤔ B) ⊢ (G ∗ H) ⤔ (A ∗ B)`, is unsound even with disjoint masks
    (§3.2, App. B.4).
  - Shared pieces are combined with overlapping conjunction instead: Guard-And gives
    `(G ⤔ A) ∗ (G ⤔ B) ⊢ G ⤔ P` when `A ∧ B ⊢ P` and `point(P)`.
- **Model structure.**
  - Guarding is defined in Iris over sets of invariants (§7, "The definition of ⤔").
  - User-defined *storage protocols* derive guard relations; fractional and counting points-to
    are instances (Fig. 2, §3.4).
  - There are no lifetimes and no mutable borrows. Leaf's related work leaves adapting it to
    RustBelt's lifetime logic as future work (§8).
- **L2.** n/a.

### 2.4 Marshall & Orchard, *Functional Ownership through Fractional Uniqueness* (OOPSLA 2024)

- **Laws.**
  - `push : &p (A ⊗ B) → (&p A) ⊗ (&p B)` and `pull` in the other direction are primitive typing
    rules (§5.2).
  - `split : &p A → &(p/2) A ⊗ &(p/2) A` and `join` (§5) handle fractions.
  - `&1` is a mutable borrow and `∗A ≡ &∗ A` is unique ownership.
  - Borrows are created by `withBorrow : ∗A → (&1 A ⊸ &1 B) → ∗B` (§5). The borrow must be
    returned: no lifetimes, and no escape.
- **Model structure.**
  - An operational heap in which references carry a permission annotation, `ref ↦_p id`
    (Lemma 6.8).
  - Metatheory is syntactic: progress (Thm 6.6), preservation (Thm 6.7, with references barred
    from holding functions) and borrow safety (Lemma 6.8, Thm 6.9: permissions to a resource
    keep summing to 1, or to 0 once ownership tracking stops).
- **Relation to L1–L4.** Their L1 and L2 are the same rule (`push`) at different `p`, both
  directions. Footnote 5 says the graded `□ᵣ` does not distribute this way in general (citing
  Hughes et al. 2021a). §7 ("Categorical model") proposes an LNL-style model as future work; none is given.
- **L2.** Yes: `push` at `p = 1`.

### 2.5 Pure Borrow (Matsushita & Ishii, 2026)

- **Laws (Fig. 12).**
  - `splitPair :: Borrow α k (a, b) ⊸ (Borrow α k a, Borrow α k b)`, `splitEither` and
    `splitAt`, for `k ∈ {Mut, Share}`, all at the same `α`.
  - Borrowers are affine: they "can be freely split … and dropped at any time before the end
    of α" (§2).
- **Model structure.**
  - A history model: each update at a borrow path is recorded (`p ← x`), and the dead lifetime
    token `End α` carries the history back to the lender (§5).
  - Leak freedom is Theorem 5.3 (a safe configuration ends with empty memory).
  - The bisimulation linking the mutative and denotational semantics is Conjecture 5.5.
- **L2.** Yes: the same `splitPair` at `k = Mut`.

### 2.6 OCaml modes: Lorenzen et al. (ICFP 2024) and Georges et al., *Data Race Freedom à la Mode* (POPL 2025)

- **Laws.** "By convention, modes are deep": a tuple at mode `m` has components at mode `m`
  (DRFCaml §2.3). The `shared` mode on the contention axis is read-only. So L1 holds by
  construction for `shared`. Modalities `τ @@ m` override the depth for one component.
- **Model structure (DRFCaml §5.2).**
  - An Iris logical relation parameterised by the mode.
  - Products use the same mode for their components.
  - `Mem(ε_mut, ε_ro, q)` grants fraction `q` of the read-only references.
  - This is an affine, garbage-collected setting with no lifetime-indexed borrows.
- **L2.** n/a: these are modes on values, not borrows. Deep uniqueness is Lorenzen et al.'s
  convention; I did not read that paper here.

### 2.7 L3 without L2: additive or lens-shaped access

- **Fähndrich & DeLine, *Adoption and Focus* (PLDI 2002), §2 and §4.2.**
  - `let x = focus e₁ in e₂` gives temporary linear access to one object guarded by key `ρ₁`,
    under a fresh key `ρ`.
  - It removes `ρ₁` from the capabilities during `e₂`, so no alias, and no second object under
    the same guard, can be focused until the focus ends.
  - At the end, `{ρ ↦ τ}` must be back at its original type, and `ρ₁` is restored.
  - This is one-at-a-time access by construction, in a linear setting, scoped. It is the
    clearest precedent that L3 can be had without splitting the guard.
  - L2: no, by design.
- **Aeneas (Ho & Protzenko, ICFP 2022)**, summarised in `prior-art-memory-model.md` Q7.
  - A function returning `&'a mut T` becomes a forward function and a backward function.
  - For a field projection the backward function is the field setter: one put reconstructs the
    whole parent.
  - LLBC does allow two disjoint field borrows at once, so L2 is present at the LLBC level
    *(from the Q1 summary; not re-read here)*.
- **Hylo/Swiftlet mutable value semantics (Racordon et al., JOT 2022).**
  - `inout` arguments are paths.
  - The Law of Exclusivity forbids overlapping ones, but disjoint paths are allowed together:
    `swap(&x[0], &x[1])` is well-typed, `swap(&x[f(0)], &x[1])` is not.
  - References are second-class, so there is no lifetime question.
  - L2 is present for statically disjoint paths.
- **Prophecy systems** (RustHornBelt, Creusot). They do L2 by partial prophecy resolution; see
  `prior-art-memory-model.md` Q1/Q7. Nothing new here.

---

## 3. The linearity question

BoLo proves leak freedom: adequacy ends in empty memory. So its logic is linear for *owned*
cells. The `wp` lets a post-resource discard a fragment `ρ⁺` only if `ρ⁺|own = ∅` (`[CONF]`
§4.3, `[TR]` p. 5). **Borrow cells, `imm` and `mut`, are already forgettable.**

That changes how much of the affine literature transfers.

- **RustBelt relies on affinity in two different places.**
  1. *Dropping a split-off borrow.* `index_mut` drops the full borrow of the rest of the vector
     (§5.1, fn. 9: "Iris is an affine logic"). In BoLo terms this is forgetting a borrow cell,
     which `ρ⁺` already allows. It transfers.
  2. *The model of the lifetime logic.* The borrow and inheritance boxes live inside Iris
     invariants (thesis §11.6). Jung's thesis §6.2 ("Linear impredicative invariants paradox",
     Theorem 2) shows that a linear separation logic with impredicative cancellable invariants
     derives `P ⇛ Emp`, so the invariant construction cannot be reused as-is in a leak-free
     logic.
  - Iron (Bizjak et al., POPL 2019) avoids the paradox by restricting invariants to "uniform"
    propositions, and builds a linear logic (Iron++) on top of affine Iris using fractional
    "trackable" points-to `ℓ ↦_π v` (§1–2).
  - I found no linear version of the lifetime logic.
- **Pure Borrow states the gap directly** (arXiv 2604.15290, related work, RustBelt paragraph):
  "All known separation logics that support borrowing, including Iris, are fundamentally affine
  and do not guarantee leak freedom. There exists a leak-free separation logic that supports
  invariants [Iron], but not yet one that supports borrowing." The paper does cite Wagner et al.
  2025 in a separate paragraph, as "a new separation logic that supports borrowing", discussing it
  only for purity; the general claim does not account for it — BoLo is linear, leak-free, has
  borrowing, and builds its model without invariants. Pure Borrow's own metatheory "works toward"
  safety and leak freedom (§5.5): confluence, well-typedness ⇒ association, and "safety ensures
  leak freedom" are stated as theorems, but progress and bisimulation are "expected", not proved,
  and nothing is mechanized; a semantic soundness proof is left as future work. It gets leak
  freedom with *affine* borrowers: the lender recovers ownership from the history carried by
  `End α`, not from returned borrowers.
- **Charguéraud–Pottier is essentially compatible with linearity.** Footnote 5: with explicit
  deallocation, "one might wish to define GC as `∃H. RO(H)`, which means that read-only
  permissions can be implicitly discarded, but read-write permissions cannot". This is BoLo's
  `ρ⁺|own = ∅`.
- **Leaf** is defined over Iris invariants (§7). I found nothing on a linear version.
- **Marshall–Orchard** is in Granule, a linear-base calculus. Its borrows must be returned
  through `withBorrow`, and the permission-sum invariant (Lemma 6.8) is its accounting. It states
  no leak-freedom theorem in the sense of BoLo's adequacy.
- **Linear forks of Iris.** Iron (above). LinearActris (Jacobs, Hinrichsen, Krebbers, POPL
  2024) *(not read here; cited by `[CONF]` §5 as a linear option)*. Neither has borrowing,
  according to Pure Borrow's related work.

**The common pattern.** In every leak-free design found, only the *owner's* resources are
linear. Borrow pieces may be dropped, because the lender's restore at the end of the lifetime
does not depend on the pieces being returned:

- RustBelt: the inheritance restores the whole `P` (Box-empty).
- Pure Borrow: the history rides on `End α`.
- C–P: the read-only memory is restored wholesale (`h′.r = h.r`).
- BoLo: 6.38 restores from the frame's own witness `ρv`.

Any splitting design for BoLo would have to keep that property: split pieces stay forgettable
(in `ρ⁺`), and the frame's end restores from the frame's record rather than from returned
pieces. *(This is my synthesis of the cited designs, not a result from any one paper.)*

---

## 4. Is L4 real?

**No paper found states `Imm_α (A & B) ≅ Imm_α A ⊗ Imm_α B`, or any Seely-shaped law, for a
borrow, read-only or shared modality.**

What exists nearby:

- **The Seely isomorphism for `!`.** In linear logic, `!(A & B) ≅ !A ⊗ !B` (nLab, *Seely
  isomorphism*). In LNL models, `!` factors as a symmetric monoidal adjunction between a
  cartesian closed category and a symmetric monoidal closed category (Benton 1994). The usual
  derivation of Seely from that factorisation is: the right adjoint preserves products, and the
  left adjoint is strong monoidal. *(Standard; I did not locate the verbatim statement in
  Benton's paper during this survey.)*
- **Adjoint logic.** `!A ≜ ↓ᴸ_S ↑ᴸ_S A` with `σ(S) = {W, C}` (Pfenning, 15-836 lecture 11, §5).
  Two constraints bear on reading `Imm` as a shift into a read mode:
  1. `m ≥ k ⇒ σ(m) ⊇ σ(k)`.
  2. The *principle of independence* (§2): a proof at mode `m` may not depend on antecedents at
     a mode `ℓ` with `ℓ ≱ m`. So a proof in a structural read mode may not depend on linear
     hypotheses.

  A borrow is exactly a read-mode value that depends on a linear owner for the duration of `α`.
  So `Imm` is not a plain `↓↑` pair in Reed/Pfenning adjoint logic. The lifetime would have to be
  what licenses a temporary exception to independence. *(This is an observation about the
  cited rules. No source discusses borrowing in these terms, and I have not derived anything
  from it.)*
- **Adjoint modes as memory regions.** Jang & Pientka, *Polymorphic Metaprogramming with Memory
  Management* (2024), use modes for garbage-free (linear) and garbage-collected regions with an
  accessibility preorder (abstract, §1). No borrow or read-only mode appears in what I read.
- **Iris's persistence modality.** It satisfies `□P ∧ Q ⊢ □P ∗ Q` (a primitive law) and the
  derived `□(P ∧ Q) ⊣⊢ □P ∧ □Q` (Iris 4.1 Reference, "Laws for the persistence modality").
  Together these give `□(P ∧ Q) ⊣⊢ □P ∗ □Q` in affine Iris. This is Seely's shape, with `∧` as
  the additive, for a *duplicable* modality. BoLo's analogue is `!P ≜ emp ∧ P` (`[TR]` p. 5);
  whether BoLo proves the matching law for `!` was not checked. RustBelt's sharing predicates
  are persistent (ty-shr-persist), but Rust has no additive pair to apply them to.
- **Leaf's Guard-And** (Fig. 4) is the closest shared-state rule relating `∧` and `∗`. It
  combines two guards of one source into a guard of an `∧`, only for point propositions. It is
  not L4.
- **Graded push/pull** (Hughes, Vollmer, Orchard 2021) distributes `□ᵣ` over `⊗` and user
  data types. The core calculus has additive sums and no `&`.

So L4 is not established anywhere found. If it is wanted, it would be a new result. The
analogies (`!` in LNL, Iris `□`) both concern modalities that need no lender.

---

## 5. Implications for BoLo's model

Nothing here is decided. Each item is an option with its precedent. The cell vocabulary is
`[TR]`'s: `own(v)`, `imm(β̃, v, ρ)` (a lifetime set, a value, a witness) and `mut(β, v, ρ′, P̂)`
(a lifetime, a value, a witness, an invariant).

### 5.1 L1: Imm distribution at the same lifetime

**Direction.** Every precedent that works at the level of the logic validates only
`Imm(P ∗ Q) ⊢ Imm P ∗ Imm Q`:

- C–P Fig. 1 and footnote 2;
- Leaf §3.2 and App. B.4;
- RustBelt: fractured borrows do not merge.

The `⊣⊢` holds only at the *type* level, where the two components are known to sit at distinct
locations: RustBelt's product sharing predicate, and Marshall–Orchard's `push`/`pull`. BoLo's
`Imm̲ 'b (T₁ ⊗ T₂)` clause is already of that type-level kind.

Options, in increasing order of model change:

- **(a) Keep L1 scoped (no change).**
  - L1 holds only inside a `withload` scope at a fresh `'b`, which is what BoLo has.
  - Precedent: C–P's `normal` side condition keeps RO inside its block.
  - Cost: `&'a self.field` cannot be returned at `'a`.
- **(b) Make the frame's end absorb same-lifetime views.**
  - Generalise the subtraction 6.52 does for reborrows to cells at lifetime `α` located inside
    the frame's witness `ρv`. The frame's end (6.38 and the `↭` in `wp`) would then remove those
    cells before restoring `own` cells.
  - The views stay forgettable in `ρ⁺`. Restore still comes from `ρv`, so the linearity pattern
    of §3 is preserved.
  - Precedents: RustBelt's Box-empty and inheritance restore the whole `P` however it was
    sliced (thesis §11.6.1). C–P's triples restore the read-only memory wholesale (`h′.r = h.r`,
    Definition 1).
  - The per-location view cells would be built exactly as `reb_α`'s case 1 builds them, but at
    `α` itself.
  - `experiments/Relaxed` shows that the typed world's strict bounds were not the obstruction,
    so the change would sit in 6.38/6.29/`↭`.
  - L2 from this structure: unclear. `mut` cells carry the invariant `P̂` as well as a witness.
- **(c) Store a partition in the `imm` cell.**
  - An `imm` cell carries its witness split per sub-location, the `π` of `reb_α`. A projection
    hands out one part with the same lifetime set.
  - 6.37's agreement (`▸◂`) would have to accept a cell together with its projected parts.
  - Precedent: RustBelt's slices (Slice-split changes the partition, not the total), and BoLo's
    own `π`.
  - L2 from this structure: plausible for `mut` witnesses, but `P̂` would also have to split.
    Unclear.
- **(d) Per-location read-only cells (C–P / fractured borrows).**
  - Replace `imm` witness trees by per-location read-only cells composed by agreement. L1 is then
    immediate (C–P Fig. 7).
  - Cost: BoLo's reborrowing and `↭` are defined over witnesses, and `[CONF]` §4 stresses
    witness tracking (for `mut` cells). This is the largest change.
  - L2: no.
- **(e) Fractions in `imm` cells.**
  - Precedents: Marshall–Orchard `&p`, RustBelt `ℓ ↦^q v`, Iron `ℓ ↦_π v`. Fractions give
    `pull` (the `⊣` direction) when the pieces are known to be one resource.
  - Iron shows that fractions are compatible with linearity.
  - BoLo's forgettable borrows lose fractions, so restore would again have to come from the
    frame, as in (b).
  - L2: yes in Marshall–Orchard (`p = 1`).

### 5.2 L3: lens-style `Mut` access, one field at a time

- **Fresh lifetime.** This appears derivable now: `withswap` gives the payload, then `withbor`
  runs on the chosen component (§0). This is *unverified*. A first cheap step would be to type
  and run it in `experiments/`.
- **Same lifetime.**
  - Needed: `Mut_α (Ref A ⊗ Ref B) ⊸ Mut_α A`, with the parent consumed for the rest of `α`.
  - Why it might need no splittable witness: only one sub-view exists at a time. Focus revokes
    the guard key (§2.7). Aeneas reconstructs the parent with a single put.
  - In BoLo terms, the parent `mut` cell's witness would stay one piece. At `ℓ₁` it would hold a
    nested lend instead of an `own` cell. BoLo already allows `mut` cells inside witnesses:
    `reb_α` case 3, and `Mut @a (Mut @b T)`.
  - The lender's frame would restore from its record at `α`'s end, reading back `ℓ₁`'s final
    value. That is the job RustBelt's LftL-reborrow inheritance does, and the job RustHornBelt's
    partial prophecy resolution does for splits.
  - **Caution.** The obstruction the experiments found for `imm` is 6.38: *any* cell at a
    location the frame's witness owns is excluded from the post-resource. A `mut` view at `ℓ₁`
    is such a cell. So same-lifetime L3 very likely meets the same wall unless the `mut` frame's
    end absorbs it, as in 5.1(b). The experiments tested `imm` only. I have not derived this and
    have not verified that any obstruction to L3 is real.
  - Whether L3 is "much weaker" than L2 in BoLo's model is open. The precedents suggest it avoids
    *splitting* the witness. They do not suggest it avoids changing the frame's end.
- **L2 from each structure.**
  - Focus: no.
  - RustBelt boxes: yes (L3 is a corollary of LftL-bor-split).
  - Nested-lend option: no. It gives one sub-view at a time by construction.

### 5.3 L4 and L5

- **L4.** Nothing to adopt; see §4. If pursued, it would be a new result. The adjoint reading
  has to say how a read mode can depend on a linear lender for the duration of `α`.
- **L5.** Two routes are in the repository or the literature.
  1. The `!T` route: `SPEC.md` §2 makes `!(T₁ ⊸ T₂)` borrowable whole. `BorrowedClosures`
     stage 1 proves `[α]P ⊨ ↺α P` for all-`imm` resources.
  2. A method record over a borrowed environment, `∃E. Imm E ⊗ !(Imm E ⊸ A ⊸ B)`, whose `Imm̲`
     would follow from L1 plus `!`. *(My construction, not from a source.)*

  Iterators over `Mut` in the literature need L2: RustHornBelt's `IterMut`, and Pure Borrow's
  `splitAt`. An `Imm` iterator needs only L1. Views as get/put codata match Aeneas's
  forward/backward pair. I found no paper that states lens laws for borrows (as already noted
  in `prior-art-memory-model.md` Q7).

### 5.4 L2 (stretch goal)

Each structure above answers the L2 question in its own line. The shortest precedent path is
RustBelt's: a borrow over a partitioned total that the lifetime's end restores whole (Slice-split
plus Box-empty). BoLo's `reb_α` partition `π` is the local analogue, but at fresh lifetimes
only.

---

## 6. Not read, or not verified

- Lorenzen et al., *Oxidizing OCaml with Modal Memory Management* (ICFP 2024): cited through
  DRFCaml §2.3 only.
- Jacobs, Hinrichsen, Krebbers, *Deadlock-Free Separation Logic* (POPL 2024): not read.
- *Fully-Automatic Type Inference for Borrows with Lifetimes* (PACMPL 2026,
  doi:10.1145/3798221): found by search; the page returned 403 and it was not read.
- Benton 1994: the Seely derivation is attributed as standard; its location in the paper was
  not checked.
- Aeneas's simultaneous field borrows: taken from the earlier survey's summary.
- The BoCa derivation of fresh-lifetime L3 via `withswap` + `withbor` has not been typed or run.
- Pure Borrow's `splitPair` has no merge direction in Fig. 12 as read; a merge elsewhere in the
  paper was not searched for exhaustively.

---

## Sources

- Wagner, Gierczak, Marshall, Li, Ahmed. *From Linearity to Borrowing*. PACMPL 9 OOPSLA2, 415,
  2025. https://dl.acm.org/doi/10.1145/3764117. The technical report is the supplement.
- Charguéraud, Pottier. *Temporary Read-Only Permissions for Separation Logic*. ESOP 2017.
  https://hal.science/hal-01408657
- Jung, Jourdan, Krebbers, Dreyer. *RustBelt: Securing the Foundations of the Rust Programming
  Language*. POPL 2018. https://people.mpi-sws.org/~dreyer/papers/rustbelt/paper.pdf
- Jung. *Understanding and Evolving the Rust Programming Language*. PhD thesis, Saarland
  University, 2020. https://research.ralfj.de/phd/thesis-screen.pdf (§6.2, ch. 11)
- Matsushita, Denis, Jourdan, Dreyer. *RustHornBelt*. PLDI 2022.
  https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf
- Hance, Howell, Padon, Parno. *Leaf: Modularity for Temporary Sharing in Separation Logic*.
  OOPSLA 2023. https://arxiv.org/abs/2309.04851
- Marshall, Orchard. *Functional Ownership through Fractional Uniqueness*. OOPSLA 2024.
  https://arxiv.org/abs/2310.18166
- Hughes, Vollmer, Orchard. *Deriving Distributive Laws for Graded Linear Types*. Linearity/TLLA
  2020 (post-proceedings 2021). https://arxiv.org/abs/2112.14966
- Matsushita, Ishii. *Pure Borrow: Linear Haskell Meets Rust-Style Borrowing*. 2026.
  https://arxiv.org/abs/2604.15290
- Georges et al. *Data Race Freedom à la Mode*. POPL 2025. https://plv.mpi-sws.org/drfcaml/
- Bizjak, Gratzer, Krebbers, Birkedal. *Iron: Managing Obligations in Higher-Order Concurrent
  Separation Logic*. POPL 2019. https://iris-project.org/pdfs/2019-popl-iron-final.pdf
- Fähndrich, DeLine. *Adoption and Focus: Practical Linear Types for Imperative Programming*.
  PLDI 2002. https://www.microsoft.com/en-us/research/wp-content/uploads/2002/05/pldi02.pdf
- Racordon, Shabalin, Zheng, Abrahams, Saeta. *Implementation Strategies for Mutable Value
  Semantics*. JOT 21(2), 2022. https://www.jot.fm/issues/issue_2022_02/article2.pdf
- Pfenning. *Lecture Notes on Adjoint Logic* (15-836, lecture 11), 2023.
  https://www.cs.cmu.edu/~fp/courses/15836-f23/lectures/11-adjoint.pdf
- Jang, Pientka. *Polymorphic Metaprogramming with Memory Management: An Adjoint Analysis of
  Metaprogramming*. 2024. https://arxiv.org/abs/2411.00752
- Benton. *A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models*. CSL 1994.
  https://link.springer.com/chapter/10.1007/BFb0022251
- nLab. *Seely isomorphism*. https://ncatlab.org/nlab/show/Seely+isomorphism
- Iris Project. *The Iris 4.1 Reference*, 2023. https://iris-project.org/
