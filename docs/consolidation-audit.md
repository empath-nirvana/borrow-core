# Consolidation audit: one world from the experiments

Prepares step (A) of the plan: consolidate the experiments into one world, before (B) a
low-level syntax, (C) a parser and (D) a compiler. Read-only audit of `main` at `180ff21`. No
build was run for this audit. Every claim below comes from reading the source, and the file:line
citations are at that commit. **[unverified]** marks a claim that would need a build to confirm.

Delay work in progress: `CTy.delay` and its relation are committed (`ae0e99a`), and so is the
`fixD` rule (`180ff21`). `experiments/CBPVMu/CBPVMu/DelayApprox.lean` is untracked and still
being written. Nothing below depends on it.

## 1. The proposed plan, claim by claim

| Claim | Verdict | Evidence |
|---|---|---|
| Base is the `CBPVMu` fork: CBPV world plus `μ` as a value-type former | **true** | `VTy.tvar`/`VTy.mu` (`CBPVMu/Types.lean`); `vShapeE` with an environment (`World.lean:27-77`); `RefPos.mu`/`MutPos.mu` (`Records.lean:56-58`, `:88-90`); `roll`/`unroll` (`Fundamental.lean:173-177`) |
| Fold rules `foldImm`/`foldOwn`/`foldReuse` | **true** | `CDerives` constructors at `Fundamental.lean:183-195`; soundness in `FoldImm.lean`, `FoldOwn.lean`, `FoldReuse.lean`; covered by `fundamentalC` |
| `Sized.lean`, `Blocks.lean` | **true** | `Sized.lean` (215 lines: `dsize`, `rebChooseTW_sized`, `withload_sized`); `Blocks.lean` (343 lines) |
| Merge `Relaxed`'s non-strict `FrameLife` and `TW.reb` `StratumLe` premise | **true that it transfers; no consumer exists.** Correction below | §2.1 |
| `!T` is present in the CBPV world | **true** | `VTy.bang`; `bangThunkF`, `bangThunkV`, `bangE`, `copyBang`, `forgetBang` (`CBPVMu/Fundamental.lean:114-127`); `Imm̲ (!A) = !A` (`Types.lean:1070`); `VOutlives.bang` (`Types.lean:1320`). Promotion is of thunks only (`!U C`), matching `SPEC.md` §2's "promotion is for `λ` and `Λ` only" |
| Records/variants as derived forms, on the base BoLo calculus | **true** | `recTy`/`varTy` at `Ty` (`Records/Encoding.lean:37-45`); every rule is a `DerivesWf` lemma; semantic facts at the library's typed world (`Records/Borrows.lean`, `Typed.*`) |
| `withbor2` family borrows (`Places`) on the base calculus, using `⊑Mut` subsumption | **true** | `Places/Family.lean:170` (`.mutSub`), `:174` (`.immSub`); `withbor2_wf` `:249`, `withborM2_wf` `:270` |
| LeafPlaces' block view partly ported to `CBPVMu/Blocks.lean`; `withborS` not ported | **true** | Ported: `Shape`, `size`, `refTy`, `valTy`, `addr`, `allocS`/`freeS`, `d_allocS`/`d_freeS`, `Packed`, `packed_node`, `WpAt`, `wpAt_alloc`, `wpAt_allocS`, `wpTS_allocS` (`Blocks.lean:39-343`). Not ported, with no occurrence anywhere in `CBPVMu/`: `famTy`, `shortenE`, `withborS`, `withborS_wf`, the `Steps`/`Track` toolkit, `withborS_ret`, `withborS_packed`, `wpTS_allocBorrow`, `DerivesWf.append_dead`, `crossPack` |
| ν with `close` and the delay type are hand-written relations in `Recursion`, not a `CTy` former | **partly outdated.** Correction below | §2.4 |
| Drop `FrameEnd`'s frame-end change (no gain) | **true** | `FrameEnd/README.md` §1: at 6.64's end the subtraction is empty (`frame_image_empty`). §2–4: projection, L3 and L2 are still refuted, by `↭` at the projecting run (`imm_view_rejected`, `mut_view_rejected`). Its only planned consumer is option B (`docs/scope-deep-freeze.md:138`) |
| Drop option B (never built) | **true** | `six38_img`, option B's first work item (`docs/scope-deep-freeze.md:217`, `:248`), does not occur in any `.lean` file |
| `CBPVMu` omitted CBPVWorld's embedding files | **true** | `CBPVMu/README.md:10-12`; `CBPVMu.lean` imports neither `Embedding` nor `EmbeddingExamples` |
| Re-port the embedding, so BoLo-derived rules (Records, Places, LeafPlaces) transfer via `embed` | **the re-port is mechanical, but `embed` transfers much less than claimed.** Correction below | §2.3 |
| Block provenance (`crossPack`, reuse holes) is a design decision: checker rule or types | **true** | `LeafPlaces/Programs.lean:352` (`crossPack`), `:391` (`crossPack_not_packed`); `CBPVMu/Blocks.lean:21-24`; `CBPVMu/README.md`, "Not done" under *The owned fold with reuse* |

## 2. Corrections

### 2.1 `Relaxed` transfers cleanly, but nothing uses it

`Relaxed` is a fork of the **library's** typed world (`Support/TypedWorld/*`, at `Ty`), not of
CBPVWorld (`Relaxed/README.md:9-11`). Its whole diff against the library is about 20 lines.
Diffing `Relaxed/Relaxed/*.lean` against `Support/TypedWorld/*.lean` gives exactly these
changes:

- `FrameLife.2`: `x ⊏ α` becomes `x ⊑ α`.
- `StratumLe` and `stratumLe_of_inStratum` are added.
- `TW.reb`'s premise changes.
- `frameLife_reb_like`'s `hβα` becomes `β ⊑ α`, proved by contradiction.
- `lt_trans` becomes `lt_of_lt_of_le` in `lifeBound_of_tagged` and `witLB_of`.
- `lt_asymm` becomes `lt_irrefl` in `not_rel_lineage`.
- `stratumLe_of_inStratum` is passed at `Reborrow.lean` `:84` and `:168-169` and at `Wp.lean:357`.

Every corresponding site in `CBPVMu` is textually the library's code at `VTy`:

| Site | `CBPVMu` location |
|---|---|
| `FrameLife` | `Records.lean:167-172` |
| `TW.reb` premise `W.InStratum β` | `World.lean:111` |
| `frameLife_reb_like` | `Wp.lean:201-230` (`hβα` at `:221`) |
| its `rebDeep` call in `TW.linLife` | `Wp.lean:357` |
| `lifeBound_of_tagged` | `Wp.lean:420`, strict step at `:433` |
| `not_rel_lineage` | `Wp.lean:486`, strict step at `:496` |
| `witLB_of` | `RelationFacts.lean:1387`, strict step at `:1405` |
| `tagged_reb`, `rebChooseTW_top` | `Reborrow.lean:49-52`, `:84`, `:168` |

**No μ, fold, block or delay proof uses the strict inequality.** The Relaxed-changed names
(`FrameLife`, `lifeBound_of_tagged`, `not_rel_lineage`, `witLB_of`, `frameLife_reb_like`,
`tagged_reb`, `TW.linLife`, `InStratum`/`TW.reb`) occur only in the files `CBPVMu` shares with
CBPVWorld: `Records`, `World`, `Wp`, `RelationFacts`, `Reborrow`, `FrameRules`, `Invariant`.
None of them occurs in `Sized`, `FoldImm`, `FoldOwn`, `FoldReuse`, `ShapeMu`, `RelMu`,
`Blocks`, `CommonList`, `ReuseList`, `Folds`, `Count`, `CountFree`, `MapMut`, `Lists`, `Fix`,
`Delay` or `DelayRel`.

- `Sized.lean:160-161` calls `rebChooseTW_top`/`rebChooseTW_deep`. Relaxed leaves their
  signatures unchanged, since they still take `W.InStratum β` and weaken it internally.
- `Blocks.lean:155`/`:168` mentions `Tagged`/`TW` only through `wpTS`'s frame, and Relaxed
  does not change `wpTS`.
- The μ-driven edits to `Images.lean` and `Invariant.lean` (219 and 214 changed lines against
  CBPVWorld) contain no occurrence of `FrameLife`.

`ti_endReb` is **FrameEnd's** change, not Relaxed's (`FrameEnd/README.md`, the table in §1).
`Relaxed` does not touch it.

**Correction.** The merge is mechanical, but **no result in any experiment needs it**. Its
README says the same-lifetime projection is still refuted, by 6.38 rather than by the strict
bound (`Relaxed/README.md`, *Result*). The only planned consumer is option B:
`docs/scope-deep-freeze.md:96-97` and `:136` list `Relaxed`'s `StratumLe` and non-strict
`FrameLife` as option B's prerequisites. The plan drops option B, so merging `Relaxed` weakens an
invariant for nothing. Either merge it knowingly as harmless slack, since FP holds with it, or
leave it out until a rule needs it. This is a design decision, not a work item.

### 2.2 No real incompatibility found

| Suspected pair | Finding |
|---|---|
| `Relaxed` × μ/folds | None. See §2.1 |
| `Relaxed` × `FrameEnd` | Moot, because `FrameEnd` is dropped. It builds on `Relaxed` (`FrameEnd/README.md:22`) |
| `LeafPlaces` block view × `foldReuse` | Semantically compatible: the model accepts any family of leaves (`LeafPlaces/README.md` §2). The two conflict only at the **lowering**: a reuse token (`Ref 1`) may be refilled into another node, and `crossPack` re-pairs leaves across blocks. Either breaks the one-word handle. This is the provenance decision in §4, not a soundness conflict |
| Records' encoding × LeafPlaces' `Shape` | **Two record encodings that differ** (§2.5). A design decision, not a semantic conflict |
| `Ref (A ⊗ B)` as one cell × `refTy` block | Both exist in `CBPVMu`. `L′ = μX. 1 ⊕ Ref (N ⊗ X)` uses one cell holding a pair (`MapMut.lean`), and `CommonList.lean` uses `refTy (node …) = Ref N ⊗ Ref X`. They are different types with different layouts, so they do not conflict. The surface syntax must say which one `Box<struct>` means |
| `CDerives` × subsumption and `!` | Present: `immSub`/`mutSub` (`CBPVMu/Fundamental.lean:131-134`) and the `!` rules (`:114-127`) |
| `embed` × every `DerivesWf` rule | Complete. `DerivesWf` (`Support/Statics/Presupposed.lean:631-~727`) has 33 constructors. `embed` (`CBPVWorld/Embedding.lean:232-319`) has a case for each, including `immSub`/`mutSub` (`:275-276`), `boxIctx` (`:273`), `bangLamI`/`bangAllI`/`bangE` (`:308-317`) and all ten axioms |

Name clashes to settle when merging, which are not semantic:

- `withbor2` is both the `CDerives` axiom constructor (`Fundamental.lean:148`) and Places' family
  term (`Places/Family.lean`).
- `Shape` is in `LeafPlaces/Layout.lean:85` (at `Ty`) and in `CBPVMu/Blocks.lean:39` (at `VTy`).
- `famTy` is in both Places and LeafPlaces.
- `Records` is the experiment's name and also `CBPVMu/Records.lean`, the typed world's frame
  records.

### 2.3 `embed` transfers typings at `cbv` images only

`embed : DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → CDerives Δ (cbvCtx Γ) e (.val (cbv T))`
(`CBPVWorld/Embedding.lean:232`). `cbv : Ty → VTy` (`:31`) produces no `tvar`, `μ` or `delay`,
and no thunk outside the `U(A ⊸ F B)` / `U(∀. F A)` shapes. So `embed ∘ withborM2_wf` is a
`CDerives` rule only at payloads that are `cbv` images. That covers no list, no tree, no `D A`,
and no `N`. Moreover:

- **Semantic facts do not transfer.** `embed` maps derivations, not `wpTS` facts. The following
  are stated at the library's typed world and must be re-proved at `CBPVMu`'s `wpTS`/`vC`:
  - `loadField_sem`, `swapField_sem`, `reborrow_vShape_recTy`, `vX_outlives_recTy`
    (`Records/Borrows.lean`);
  - `withborM2_sem` (`Places`);
  - `withborS_packed`, `wpTS_allocBorrow`, `blockSwap_block` (`LeafPlaces/Packed.lean`,
    `Programs.lean`).

  `Blocks.lean` already did this for `wpTS_allocS`.
- **The derived rules the consolidated world needs are at `VTy` payloads.** Examples are records
  with list fields, a family borrow over `μX. 1 ⊕ (Ref A ⊗ X)`
  (`docs/ideas-pointers-and-lifetimes.md`, *Family borrows*), and blocks whose leaves are lists
  (`CommonList.lean`). These must be re-derived in `CDerives`, by the same induction as the
  `DerivesWf` versions.

What the re-port does give: `adequacy_of_derivesWf` (`Embedding.lean:323`), the baseline
programs through the consolidated world (`EmbeddingExamples.lean`), and a check that the world
still interprets BoLo. The re-port is mechanical. Every induction in `Embedding.lean` is on `Ty`,
not `VTy`, and CBPVMu's `VTy.immReborrow`/`applyLSub` are CBPVWorld's clause for clause at the
old formers (`CBPVMu/Types.lean:1060-1073`, `:1158-1186`). **[unverified]**: no build.

### 2.4 The delay type is now a `CTy` former; general ν is not

- `CTy.delay A` is in `CBPVMu/Types.lean:67-68`. Its relation is the greatest fixed point
  `delayRel` of `delayF` (`Relation.lean:100-113`, clause `:160`), with `cC_delay_iff`
  (`DelayRel.lean`), `delayIn`/`delayOut` (`Fundamental.lean:197-200`) and `fixD`
  (`Fundamental.lean:201-203`, `Delay.lean`). These are `ae0e99a` and `180ff21`.
- `D A` is a **fixed** instance of `ν`, not a binder: there are no computation-type variables.
- Streams `νX. F(A ⊗ U X) & F 1`, with `close` and coiteration (`unfold_sem`), are still
  hand-written in `Recursion/Nu.lean` (414 lines, over `CBPVWorld`, predicate `stRel`).
- `docs/scope-recursion.md` §3.1 recommends a general `νX. B : CTy` with an environment.

So the ν item is a design decision: either a general `ν` with `CTy` variables, or further fixed
formers (a `stream`) beside `delay`.

### 2.5 Two record encodings

- Records: `{l₁ : T₁, …} ≜ T₁ ⊗ (… ⊗ (Tₙ ⊗ 1))`, with a trailing `1` (`Records/Encoding.lean:37-39`).
- LeafPlaces/Blocks: a binary `Shape` tree with no unit leaf
  (`valTy (node s₁ s₂) = valTy s₁ ⊗ valTy s₂`, `CBPVMu/Blocks.lean:56-59`).

Laid out as a block, Records' trailing `1` would be a `Ref 1` leaf, a wasted cell. Pick one
encoding before porting `recI`/`recE`/`getAt`.

## 3. Divergence between the forks

### 3.1 `CBPVMu` against `CBPVWorld`

Changed-line counts from `diff` with the namespace normalised:

| File | Changed lines | Beyond μ/delay? |
|---|---|---|
| `Compat`, `Compatibility`, `FrameRules`, `Reborrow`, `Wp` | 0 | — |
| `Examples` | 3 | `bindE` moved to `FoldImm.lean` |
| `Records` | 13 | no: `RefPos.mu`, `MutPos.mu`, `TyEq` at `tvar`/`mu`/`delay` |
| `Computation` | 30 | no: the `delay` cases of `sS`, `cC_iff_stacks`, `cC_step`, `cC_bind` |
| `Fundamental` | 51+ | no: `roll`/`unroll`, the three folds, `delayIn`/`delayOut`/`fixD` |
| `World` | 65 | no: `SEnt`, `vShapeE` |
| `ReborrowShapes` | 66 | no: 6.131 by the induction principles |
| `Relation` | 113 | no: `vCE`, `delayF`/`delayRel` |
| `Invariant` | 214 | no: position inductions (`CBPVMu/README.md`, table) |
| `Images` | 219 | no: same |
| `RelationFacts` | 879 | no: re-proofs by `vC_ind` |
| `Types` | 1080 | no: `tvar`, `μ`, substitution, `immG`, `NoMut`, `delay` |

Missing from `CBPVMu`: `Embedding.lean` and `EmbeddingExamples.lean`. `TW`, the invariants and
the choosers are unchanged (`CBPVMu/README.md:47-49`).

The spot-check was of `Records`, `World`, `Computation`, `Fundamental` and `Examples`. In them I
found no divergence that is not a μ/delay addition. `Images`, `Invariant` and `RelationFacts` were
checked only for `FrameLife`-family names, not line by line. **[unverified]**: those three
contain nothing but μ re-proofs.

### 3.2 Definitions the other experiments changed or assumed

- **`Relaxed`**: `FrameLife`, `TW.reb` (§2.1). Nothing else.
- **`FrameEnd`**: on top of `Relaxed`, it changes `TW.immEnd` and adds `ti_sub`,
  `single_imm_get`, `linLife_sub` and `frame_image_empty`, and weakens `ti_endReb`'s premise
  (`FrameEnd/README.md`, §1 table). It is dropped.
- **`Records`, `Places`, `LeafPlaces`**: no definition changed. They assume BoLo's `Ty`,
  `DerivesWf` and the library's typed world (`Typed.fundamentalProperty`, `Typed.adequacy`).
  - LeafPlaces restricts leaves to `plainB` (`1`, `⊕`, `⊗`, `Ref`; `Layout.lean`). CBPVMu's
    `Shape.leaf` takes any `VTy`. Allocation and free need no restriction there, but
    `withborS`'s outlives side condition will.
  - Places' family rule needs `Δ, 'a ⊢ B ⊐ 'a` and `Δ, 'a ⊢ T ⊐ 'a` (`Places/README.md` §1).
    `VOutlives` has `.mu` and `.tvar` (`CBPVMu/Types.lean:1326-1329`), so list-typed leaves are
    admissible there. **[unverified]**: not derived.
- **`Recursion`**: over `CBPVWorld` unchanged. `Fix.lean` is already ported
  (`CBPVMu/Fix.lean`), and so are `ImmMu.lean`'s syntax (`CBPVMu/Types.lean`) and `Mu.lean`
  (subsumed by `RelMu`/`Lists`). `Nu.lean` is not ported.

## 4. Work list for (A), in order

Sizes are source lines of the code to port or write, measured with `wc -l`.

| # | Item | Kind | Size |
|---|---|---|---|
| 1 | Fix the base: `CBPVMu` after the delay work lands (`DelayApprox.lean`). Choose the consolidated library's name and namespace, and rename the modules | mechanical | 0 new lines; a namespace pass over ~20k lines |
| 2 | Re-port `Embedding.lean` and `EmbeddingExamples.lean` (§2.3) | mechanical **[unverified]** | 329 + 58 |
| 3 | Decide `Relaxed` (§2.1). If kept: the edits at the sites in §2.1's table | design decision, then mechanical | ~20 |
| 4 | Decide the record encoding (§2.5), the meaning of `Ref (A ⊗ B)` (one cell or block), and the names in §2.2 | design decision | — |
| 5 | Records at `VTy` in `CDerives`: `recI`, `recE`, `getAt`, `injAt`, `vcase`, `loadField`, `loadCase`, `swapField`, `Splits`. Semantic facts as instances of `CBPVMu`'s `reborrow_vShape`/`vC_outlives`. `Affine`/`dropT` at `μ` is new work (§5) | mostly mechanical; real at `Affine` | `Encoding` 381 + `Borrows` 250 + `Splits` 94; programs 413 optional |
| 6 | Places' family borrow in `CDerives` at `VTy`, with `VOutlives` side conditions | real (re-derivation, same proof shape) | `Family.lean` 310; programs 562 optional |
| 7 | LeafPlaces' `famTy`, `shortenE`, `withborS`, `withborS_wf` and `append_dead` in `CDerives`. Port `Steps.lean`/`Track.lean` (they mention no types; only `Shape`'s leaf type changes) for `withborS_ret`. Port `withborS_packed`/`wpTS_allocBorrow` by `fundamentalC` | `Steps`/`Track` mechanical; typing and `packed` real | `Terms` 270 + `Typing` 223 + `Weaken` 98 + `Steps` 296 + `Track` 168 + rest of `Packed` ~150; programs 400 optional |
| 8 | ν: a general `νX. B : CTy` with `CTy` variables, or `stream` as a second fixed former. Port `Nu.lean`'s `stRel`, `unfold_sem` and `take2Close` accordingly | design decision, then real | `Nu.lean` 414 to port as a fixed former; a general `ν` is larger and **[not estimated]** |
| 9 | Block provenance: `crossPack` and reuse tokens moving across nodes. Choose between a checker rule (as LeafPlaces and FoldReuse assume now) and a type-level block index | design decision; belongs with (B) | — |
| 10 | Regression: every existing `CBPVMu` program plus `EmbeddingExamples`, with axiom checks | mechanical | — |

Before any of this lands in `Paper/`/`Support/`, `CLAUDE.md` requires a `SPEC.md` entry.
`SPEC.md` §1's baseline theorems are stated at `DerivesWf`/`SemX`. A CBPV world preserves
adequacy through `embed` (`adequacy_of_derivesWf`), and FP only as `fundamentalC ∘ embed` at
`vC`, which is not the baseline's `SemX`. The entry has to say which statement counts as
"preserved".

## 5. Loose ends to record

- **Outlives at `U C`/`Unk`.** `VOutlives` has no rule at `U C` or `Unk`
  (`CBPVMu/Types.lean:1314-1329`), as BoLo has none at `⊸`/`∀`/`Unk`. This has three
  consequences:
  - `[]I` cannot box a context holding a thunk that is not under `!`;
  - Places'/LeafPlaces' family result `T` cannot hold one (`Places/README.md` §1,
    `LeafPlaces/README.md` §3);
  - `foldImm`'s `R` must outlive every lifetime (`Fundamental.lean:183-186`, `hR`), so a fold
    returning a borrow into the structure is not covered.
- **Positivity `NoMut`** (`CBPVMu/Types.lean:482`): the recursion variable may occur under no
  `Mut` payload. `U C` is a leaf for type variables, so `X` under a `U`-codomain is unbound. W-types
  and free monads through `U` are therefore not expressible (`CBPVMu/README.md`, Step 1), and
  total deep handlers wait on it (`docs/scope-recursion.md` §7).
- **The fold class `FShape`** (`FoldImm.lean:29-34`) allows closed leaves, `Ref X`, guarded
  `X`, `⊗` and `⊕`. It excludes:
  - `X` under `Ref` of a compound (`L′`, where `MapMut`'s `mapInc` stays a hand proof);
  - `X` under `Imm`, `Mut`, `!` or `[@a]`;
  - `X` under `U`.

  A borrowed fold at `Ref S` with `X` inside a compound `S` is not derived.
- **Variants in place.** `Ref` does not distribute over `⊕`, because the leaf layout depends on
  the tag (`CBPVMu/README.md`, *The common list shape*; `LeafPlaces/README.md` §4). Borrowing a
  payload place while the tag is fixed is open (`docs/dream-properties.md` P6).
- **`Affine` at `μ` and `U`.** `Affine` (`Records/Encoding.lean:228-235`) has no `μ` or `U`
  case. `affine_immReborrow` holds at BoLo's `Ty`, but `Imm̲ 'b N = μY. 1 ⊕ Y` needs a recursive
  drop (a `foldOwn`). So "project one field of an `Imm` record" at μ-typed fields needs a new
  lemma. **[unverified]**: not attempted.
- **Reuse tokens.**
  - A `foldReuse` token is not tied to its node.
  - Leaf size is uniform in the model, so a token of `Ref 1` can be filled at any type.
  - A sized layout would need the token to carry its size (`CBPVMu/README.md`, *The owned fold
    with reuse*).
- **Same-lifetime projection (P2).** Still refuted, by `Projection`, `Relaxed` (6.38) and
  `FrameEnd` (`imm_view_rejected`, `mut_view_rejected`). External iterators over a borrowed
  boxed structure wait on it (`docs/scope-recursion.md` §7). Family borrows are the proposed way
  around it (`docs/ideas-pointers-and-lifetimes.md`), and nothing has been built for them.
- **The delay type.**
  - The cancellable `bind` needs continuations that are `!` or finalizable
    (`docs/scope-recursion.md` §4).
  - Adequacy without `close` needs a `theorem32` with a non-pure postcondition (same section).
  - A direct `fix : !U(U(D A) ⊸ D A) ⊸ D A` is not derived. `fixD` takes a step
    `S ⊸ F(A ⊕ S) & F 1` instead.
- **From `CBPVWorld/README.md`, Open**:
  - agreement with the old world on translated types is not attempted;
  - the embedding goes into the value judgment through three derived forms (`lolliE`, `allEV`,
    `ofRet`);
  - axioms have call-by-value types, not natively curried CBPV types.
- **From `SPEC.md` §2, Open**: promotion at every value; conservative extension (F3).
- **Machine.** There is no address arithmetic, so a one-word block handle is a lowering of
  `addr b σ` (`LeafPlaces/README.md` §4(e)). `Loc = ℕ` is fixed in the syntax. Re-instantiating
  `Loc` means forking about 41k lines (`LeafPlaces/README.md` §1).
