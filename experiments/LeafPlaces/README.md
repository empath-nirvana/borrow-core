# LeafPlaces: unboxed structs as blocks of leaf locations

**Question.** `experiments/Places` showed that borrowing disjoint places at one lifetime is
derivable when a structure is a family of locations (a tuple of `Ref`s). But in Places each
field is a separate heap box. An unboxed struct is one allocation with one handle, and its
leaves are distinct locations inside it. So the question is: does anything in the model depend
on a location holding a whole value? Concretely, can an owned struct handle be a packed family
of leaf locations, with borrowing going through the family?

Build: `lake build LeafPlaces`. Nothing in `Paper/`, `Support/`, `Examples/` or another
experiment is changed. `LeafPlaces` imports `Places.Programs`.

| file | contents |
|---|---|
| `Layout.lean` | shapes, the block layout, plain types, the leaf formers; the model at `ℕ × List ℕ` |
| `Terms.lean` | `allocS`, `freeS`, `withborS`, `⇓` (`shortenE`) as closed terms; closedness |
| `Typing.lean` | their typing rules, derived in `DerivesWf` by induction on the shape |
| `Weaken.lean` | weakening a derivation by consumed slots at the end of the context |
| `Steps.lean` | unique decomposition of machine steps; inversion of runs through a context |
| `Track.lean` | `withborS_ret`: every run of a borrow returns the handle it was given |
| `Packed.lean` | `Packed`, pack/unpack, block allocation (`wpTS_allocS`), `withborS_packed` |
| `Programs.lean` | checks (b)–(d), and `crossPack` |

## 1. Genericity audit

**The resource model is generic in `Loc`.** `PMap (Loc A : Type)` (`Paper/S5_Model/Definitions.lean:55`),
the cells `CellU Loc Val` (`:237`) and `ResU Loc Val` (`:266`) are all defined under
`variable {Loc Val : Type}` (`:248` and later). So are flattening (`ResU.Flat`, `:1677`), `↭`
(`ResU.UpdV`, `:1740`), `reb` (`ResU.Reb`, `:1249`), and their lemmas in `Support/Model/`
(`Cells.lean:12`, `Flattening.lean:15`, `Update.lean:21`, `Reborrow.lean:22`, …). A resource is a
finite map (`FinDom`, `Support/Model/Prelude.lean:22`). That finiteness is a property of the
map, not of `Loc`.

**What is concrete.** `abbrev Loc := Nat` (`Paper/S1_Syntax/Definitions.lean:33`), which the
syntax uses in `Expr.loc` (`:84`). BoLo and the typed world use
`WRes := ResU BoCa.Loc BoCa.Val` (`Paper/S5_Model/Definitions.lean:494`), and the machine uses
`Heap := Loc → Option Val` (`Paper/S3_Dynamics/Definitions.lean:157`).

**Which properties of `Loc` are used.**

1. *Equality.* It is decided classically (`open Classical`, G8,
   `Paper/S5_Model/Definitions.lean:725–727`, at `ResU.single`). No `DecidableEq` instance is
   required.
2. *Some location is missing from every finite list* (`PMap.Infinite`,
   `Support/Model/CellFacts.lean:16`, used through `exists_fresh`, `:21`). Allocation needs
   this, and only allocation: `wpTS_alloc` (`Support/TypedWorld/Wp.lean:579`) and the printed
   `wp-alloc` rules (`Paper/S6_7_WeakestPreconditionRules/Lemmas.lean:428`, `:460`). For `ℕ` it
   is `loc_infinite` (`Support/Model/Entailments.lean:360`). That is the only proof in the model
   or the typed world that uses `ℕ`'s order.
3. *The interpreter* allocates by bumping a counter (`Mem.alloc`,
   `Support/Dynamics/Interpreter.lean:29`, `next + 1`). No `wp` result uses it.

Nothing else is used: the model and the typed world use no order on locations and no
arithmetic on them. The machine's `alloc↦` takes any `ℓ` with `μ ℓ = none`
(`Paper/S3_Dynamics/Definitions.lean:241`, `:282`).

**What instantiating `Loc := ℕ × Path` would take.** `Loc` occurs in the syntax (`Expr.loc`).
So every file of `Paper/` and `Support/` depends on it, and re-instantiating means forking the
whole library (about 41k lines). The only proofs that would need to change are item 2's
`loc_infinite` and item 3's interpreter. `Layout.lean` checks the model side directly: it
states `updV_trans_blockPath` (6.49), `compS_assoc_blockPath` and `flat_functional_blockPath` at
`Loc = ℕ × List ℕ`, and proves `infinite_blockPath`, the one property allocation needs, there.

**The cheaper route, taken here.** Keep `Loc = ℕ` and lay the block out: a struct allocated at
base `b` has its `i`-th leaf (in order) at `b + i`. The map `(block, path) ↦ b + offset(path)` is
the static layout that a later lowering would use anyway. The model only compares locations for
equality, and distinct leaves of a block are distinct naturals, so this is indistinguishable
from `ℕ × Path` as far as the model is concerned. No fork is needed.

## 2. Design

- **Shapes.** `Shape ::= leaf T | node s₁ s₂`. `{a : A, b : B}` is `node (leaf A) (leaf B)`,
  and `{a : {x, y}, b}` is `node (node (leaf X) (leaf Y)) (leaf B)`. A leaf type is `plainB`:
  built from `1`, `⊕`, `⊗` and `Ref`, so a leaf may itself be a boxed field.
- **The handle type is the leaf family.** `refTy (leaf T) = Ref T` and
  `refTy (node s₁ s₂) = refTy s₁ ⊗ refTy s₂`. `famTy M 'c σ` is the family of leaf borrows,
  `M 'c T₁ ⊗ …`, in the same tree shape.
- **The handle value.** `addr b σ` is the tuple of leaf addresses, `(b, b+1, …)` in the shape
  of the tree. The machine has no address arithmetic, since a value names one location, so a
  one-word handle cannot be a source value. It is a lowering of `addr b σ`, which is sound when
  the tuple is a block's. `Packed σ b` is `𝒱⟦refTy σ⟧` at the handle `addr b σ`; this is the
  semantic one-word handle.
- **Pack and unpack are the identity.** The types agree definitionally
  (`refTy (node s₁ s₂) = refTy s₁ ⊗ refTy s₂`). `packed_node` states the isomorphism: a packed
  node is exactly a packed handle for each child, at the child's sub-block (`b` and
  `b + size s₁`), with the same value and the resource split. A sub-struct handle `s.a` is
  therefore itself a packed handle. So pack and unpack are not primitives: they are the
  identity on terms and on the relation.
- **The operations are derived terms** (`Terms.lean`):
  - `allocS σ` allocates the leaves in order;
  - `freeS σ` frees them all and returns the struct's value;
  - `withborS σ : refTy σ ⊸ (∀'c ⊏ ⊓Δ. famTy M 'c σ ⊸ ['c] T) ⊸ refTy σ ⊗ T` borrows every
    leaf and hands the callback the family at one lifetime. At a node it is Places' `withbor2`
    applied recursively. `⇓s₁` (`shortenE`) moves the outer sub-family from the outer lifetime
    to the inner one, applying `⊑Mut`/`⊑Imm` at every leaf; at run time it is the identity
    (`shortenE_run`).
- **Whole-record load and store** are done per leaf, inside the callback: `readBoth` reads the
  family, and `swapCb` swaps it by `withswap` on each leaf. A generic `loadS`/`storeS` over
  shapes was not built.

**Where this departs from the proposed design, and why.** The proposed primitive
`pack : Ref A ⊗ Ref B ⊸ Ref {a:A, b:B}` is fine in the model but not for a one-word handle.
`crossPack` shows this: it allocates two structs, unpacks both, pairs `a₁` with `b₂`, borrows
that pair as a struct, and frees everything. The program is derivable, runs, and leaks nothing.
But its handle is `(0, 3)`, which is no block's handle (`crossPack_not_packed`). The same
applies to freeing one leaf of a block alone. Neither is a model question: the model accepts
any family. The surface language has to keep owned leaf handles from being re-paired across
blocks or freed singly, for example by handing leaves out only as borrows (`withborS`). That
rule belongs to the checker. Within this discipline, a struct handle is only ever produced by
`allocS` and returned by `withborS`, and both keep it packed.

## 3. Derived vs added

**Nothing is added** to the model, the machine, the typing judgment or the typed world. Every
operation's rule is a derived rule of `DerivesWf`, proved by induction on the shape:

| rule | Lean |
|---|---|
| `allocS σ : valTy σ ⊸ refTy σ` | `allocS_wf` |
| `freeS σ : refTy σ ⊸ valTy σ` | `freeS_wf` |
| `⇓σ : famTy M @b σ → famTy M @a σ` when `Δ ⊨ @a ⊑ @b` | `shortenE_wf` |
| `withborS σ`, at `Mut` and at `Imm`, for every plain shape and plain result `T` | `withborS_wf` (`withborSM_wf`, `withborSI_wf`) |
| weakening by consumed trailing slots | `DerivesWf.append_dead` |

So FP and adequacy cover every program that uses them, with no new case.

**New facts** (lemmas about existing definitions, not new rules):

- `wpTS_allocS` (**block allocation**). At every frame the typed world admits, `allocS σ v` has a
  run that places the leaves at `b, b+1, …` for a base `b` above every allocated location, and
  returns `addr b σ`, packed. `wpTS` chooses its run (`Support/TypedWorld/World.lean:138`), and
  `alloc↦` may take any fresh location, so this run is legitimate. A block allocator is this
  choice. The proof works at one fixed frame (`WpAt`, `wpAt_alloc`, `wpAt_allocS`), because the
  later leaves' freshness is a fact about the whole configuration. A `wpTS` built from single
  `wpTS_alloc`s does not keep that fact, since each of them quantifies over its own frame.
- `withborS_ret` (**borrowing returns the handle it was given**). On every run,
  `withborS σ v g` returns `(v, r)`, and `r` is the result of a run of `g () m` at a closed
  family `m`. The typing rule does not say this, because `refTy σ ⊗ T` holds other handles too.
  The proof uses a small operational toolkit that the library does not have, because its `wp`
  only ever builds runs. The toolkit is in `Steps.lean`: unique decomposition of steps
  (`plug_decomp`), `steps_plug_inv`, and inversions at `β`, `let`, pairs and application.
- `withborS_packed` and `wpTS_allocBorrow` (**borrowing keeps the handle packed**). These are FP
  at the call's derivation, plus `withborS_ret` through `wpTS_track`. After the borrow, the
  handle is the same block's, packed, beside the callback's result.

**Restrictions of the derived rule.** Leaf types and the callback's result `T` are `plainB`.
Places needed `B` and `T` to outlive the outer lifetime. Here the rule is proved generically,
and plain types satisfy that side condition at every level of the tree. A `T` holding a borrow,
a function or `Unk` is not covered, just as in Places. I have not derived the rule at such a
`T` and have not verified that any obstruction is real.

**Semantically**, each leaf is still framed by its own nested `withbor`, at nested lifetimes. The
single lifetime `'c` is a fact about the type, obtained by `⊑`, exactly as in Places. No cell
owns the leaves, so no parent `imm`/`mut` witness exists for `↭` to set a leaf view against.

## 4. Checks

Each program is closed and typed at `1`, and has three checks. `…_runs` is its adequacy
instance: from the empty memory it runs to `()` and the empty memory, so nothing leaks.
`…_eval` is a kernel-checked interpreter run, and `…Obs_eval` checks the struct's contents. The
interpreter allocates by bumping a counter, so its `allocS` lays the leaves out consecutively:
it is a block allocator. `…_block` is the typed-world statement of the program's first half:
allocated as one block and borrowed through the family, the struct comes back as that block's
handle, packed, at every frame.

| | result | Lean |
|---|---|---|
| (a) FP + adequacy with the new operations | **hold, with nothing added**: every operation is a derived rule, so `Fig16.LogRel.Typed.fundamentalProperty` and `adequacy` apply unchanged | `withborS_wf`, `allocS_wf`, `freeS_wf`; every `…_runs` |
| (b) one block; `&mut s.a` and `&mut s.b` together, both updated, repacked, freed whole | **holds**. `blockSwap`: `withborS` hands `swapCb` both leaf borrows at `'c`, which swap them (`(inj₁, inj₂)` becomes `(inj₂, inj₁)`). The handle that comes back is the block's (`blockSwap_block`), and `freeS` frees the block with no leak | `d_blockSwap`, `blockSwap_runs`, `blockSwap_eval`, `blockSwapObs_eval`, `blockSwap_block` |
| (c) nested `{a : {x, y}, b}`: `s.a.x` alone at the lifetime of `s.b` | **holds**. `nestSwap`: the family is `(Mut 'c B ⊗ Mut 'c B) ⊗ Mut 'c B`. `s.a.x` and `s.b` go together to `swapFn : ∀'d. Mut 'd B ⊗ Mut 'd B ⊸ …` at `'c`, and `s.a.y`'s borrow is dropped. `((inj₁, inj₁), inj₂)` becomes `((inj₂, inj₁), inj₁)` | `d_nestCb`, `d_nestSwap`, `nestSwap_runs`, `nestSwap_eval`, `nestSwapObs_eval`, `nestSwap_block` |
| (d) `Imm` of the whole struct, and projection to a leaf at the same lifetime | **holds**. `blockRead`: `s.a` is read alone and the whole struct is read, both at `'c` (Places' `readCb`). `nestRead`: the sub-struct `s.a` is read through its sub-family and `s.b` through its leaf, each at `'c` | `blockRead_*`, `d_nestReadCb`, `nestRead_*` |
| (e) does anything force a location to hold a whole record? | **No.** See below | `wpTS_allocS`, `withborS_ret`, `packed_node`, `crossPack_not_packed` |

**(e).** Nothing in the resource model, the typed world or the machine makes a location hold a
whole record. A cell holds whatever value it is given. `𝒱⟦Ref T⟧` is one location per `Ref`
(`Support/TypedWorld/Relation.lean:89`), so a struct laid out as leaves is a family of leaf
cells. `alloc`, `load` and `store` are single-cell operations, but a struct is simply
`size σ` of them, and the machine and `wpTS` allow those cells to form one block
(`wpTS_allocS`). What the machine lacks is **address arithmetic**: a value names exactly one
location. A one-word struct handle is therefore a lowering of the tuple `addr b σ`, not a source
value. It is sound because allocation produces that tuple and borrowing returns it unchanged.
A surface rule has to stop programs from re-pairing leaves across blocks (`crossPack`).

**Variants (not attempted).** A variant's leaf tree depends on its tag. `Shape` is static, so
`Packed` and `addr` would need a tag-indexed shape, and a union layout would put different
payloads' leaves at overlapping addresses. The model has no notion of overlapping cells: a
location holds one cell. I have not derived anything about variants.

## Axioms and hygiene

`#print axioms` was checked with a scratch file importing `LeafPlaces`:

- `[propext, Classical.choice, Quot.sound]`: every `…_runs` and `…_block` (including
  `crossPack_runs`), `withborS_ret`, `shortenE_run`, `wpTS_allocS`, `wpAt_allocS`,
  `packed_node`, `withborS_packed`, `wpTS_allocBorrow`, `compS_assoc_blockPath` and
  `flat_functional_blockPath`;
- `[propext, Quot.sound]`: `withborS_wf`, `updV_trans_blockPath`, `infinite_blockPath`;
- `[propext]`: `allocS_wf`, `freeS_wf`, `shortenE_wf`, `DerivesWf.append_dead`,
  `crossPack_not_packed` and every `…_eval`.

The directory has no `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or
`unsafe`. `lake build LeafPlaces` adds no warnings of its own, and `scripts/check-hygiene.sh`
passes.
