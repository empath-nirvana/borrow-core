# Core: the consolidated world

One CBPV typed world holding what the experiments built separately: `μ` and the three folds,
blocks, records and variants, family borrows, block borrows, the delay type with `fixD`, and the
stream type with `unfoldS`. It is `SPEC.md` §3–§7 as an experiment; nothing here is in the
library yet.

Build: `lake build Core` (a non-default `[[lean_lib]]`). Namespace `BoCa.Fig16.LogRel.Core`,
the namespace depth of the fork it starts from, so every name resolves as it did there. Core
imports only `Paper`, `Support` and `Examples`, and no other experiment.

Every declaration's axioms are `[propext, Classical.choice, Quot.sound]` or a subset. This was
checked for all 4361 declarations of the `Core.*` modules at once, with
`scripts/CheckAxioms.lean` pointed at `Core`. The directory has no `sorry`, `axiom`,
`native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe` outside comments.

## What it contains

### Types

    A ::= 1 | A ⊗ A | 0 | A ⊕ A | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk | X | μX. A
    C ::= F A | A ⊸ C | C & C | ⊤ | ∀'a ⊏ @b. C | D A | Str A

`D A = νX. F(A ⊕ U X) & F 1` and `Str A = νX. F(A ⊗ U X) & F 1` are fixed formers. Each is
interpreted as a greatest fixed point (`delayRel`, `strRel`) and is equal to its unrolling
(`cC_delay_iff`, `cC_str_iff`). There is no general `ν`.

### The judgment `CDerives Δ Γ e j`

`Fundamental.lean`. It has the CBPV formers, the lifetime `∀`, the `!` rules, `[]I`/`[]E`,
`⊑Imm`/`⊑Mut`, and one constant per borrow axiom at arbitrary value-type payloads. It also has
three call-by-value forms (`lolliE`, `allEV`, `ofRet`), `roll`/`unroll`, the folds `foldImm`,
`foldOwn` and `foldReuse`, `delayIn`/`delayOut` with `fixD`, and `strIn`/`strOut` with
`unfoldS`:

    fixD    : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)
    unfoldS : !U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Str A)

### Theorems

- **Fundamental Property.** `fundamentalC : CDerives Δ Γ e j → SemJ Δ Γ e j`, by induction
  over every constructor.
- **Adequacy.** `adequacyC` (with `theorem32` and `corollary33`): a closed computation of `F 1`
  runs to `()` and leaves memory empty.
- **Embedding.** `embed : DerivesWf Δ Γ e T → CDerives Δ (cbvCtx Γ) e (.val (cbv T))` for every
  `DerivesWf` rule, and `adequacy_of_derivesWf`. `EmbeddingExamples.lean` runs BoLo's baseline
  programs through it.
- Weakening by consumed trailing slots: `CDerives.append_dead`.

### Derived rules

These are theorems about `CDerives`, not constructors, so `fundamentalC` covers each of them
with no new case.

| rule | file |
|---|---|
| records as `Shape.valTy` (a binary tree of `⊗`, no unit leaf) and variants as `Shape.sumTy` (a tree of `⊕`), fields and cases named by a path: `recI`, `recE`, `getAt_wf`, `injAt_wf`, `vcase_wf`, `loadField_wf`, `loadCase_wf`, `swapField_wf` | `Records.lean` |
| `Imm̲`, outlives, 6.131 and 6.60 at records and variants: `immReborrow_valTy`/`_sumTy`, `outlives_valTy`/`_sumTy`, `reborrow_vShape_valTy`/`_sumTy`, `vC_outlives_valTy`/`_sumTy` | `Records.lean` |
| family borrow `withborF2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. M 'c A ⊗ M 'c B ⊸ ['c] T) ⊸ …`, `M = Mut`/`Imm`: `withborM2_wf`, `withborI2_wf` | `Family.lean` |
| block borrow `withborS σ : refTy σ ⊸ (∀'c ⊏ ⊓Δ. famTy M 'c σ ⊸ ['c] T) ⊸ refTy σ ⊗ T`, `shortenE`: `withborS_wf`, `withborSM_wf`, `withborSI_wf`, `shortenE_wf` | `BlockBorrow.lean` |
| block allocation and free: `allocS`, `freeS` (`d_allocS`, `d_freeS`) | `Blocks.lean` |

These facts are stated at the typed world:

- `wpTS_allocS`: a block is allocated at consecutive locations.
- `withborS_ret`: a block borrow returns the handle it was given, on every run.
- `withborS_packed` and `wpTS_allocBorrow`: after the borrow, the handle is packed again at the
  same block.

### Programs

Each program below is a closed `CDerives` derivation. It is run by adequacy, and also by the
interpreter (`…_eval`, kernel-checked by `decide`) with its result checked (`…Obs_eval`).

| file | programs |
|---|---|
| `Examples.lean` | `cImmBorrow`, `cBang`, `cRecBorrow` |
| `EmbeddingExamples.lean` | the ten `Paper/Examples/Programs.lean` and `Examples/Closures.lean` programs, through `embed` |
| `Lists`, `Count`, `CountFree`, `MapMut`, `Folds`, `CommonList`, `ReuseList` | lists built and freed; borrowed counts; the in-place map; the folds' programs; the common list as blocks; the in-place map by `foldReuse` |
| `DelayPrograms`, `DelayNaive` | the driver and its adequacy for `D 1`/`D N`; `fixD` loops; `later (g d)` refuted as a guardedness condition |
| `RecordPrograms.lean` | `readFields`, `mutFields`, `matchSome`, `bagProg` (a record with a list field, pushed through `swapField`) |
| `FamilyPrograms.lean` | `swapBothB` and `swapBothL` (`mem::swap` of two leaves, at `1 ⊕ 1` and at the common list), `readFamily`, `splitFour` (two nested families) |
| `BlockPrograms.lean` | `blockSwap`, `nestSwap`, `blockRead`, `nestRead` (each with a `…_block` typed-world fact), `bagBlock` (a block with a list leaf), `crossPack` |
| `StreamPrograms.lean` | `take_runs` (every closed `U(Str 1)` observed `n` times and closed), `takeCloseR`, `natsSum` (`0 + 1 + 2 = 3`) |

## Where it came from

| from | into `Core/` |
|---|---|
| `CBPVMu` | the base: every `CBPVMu/` file, renamed (`Records.lean` became `FrameRecords.lean`, the typed world's frame records) |
| `CBPVWorld` | `Embedding.lean`, `EmbeddingExamples.lean` (only the namespace changed) |
| `Relaxed` | `FrameLife.2` non-strict (`FrameRecords.lean`); `StratumLe` and `TW.reb`'s premise (`World.lean`); `frameLife_reb_like` (`Wp.lean`); the `lt_of_lt_of_le`/`lt_irrefl` steps (`Wp.lean`, `RelationFacts.lean`); `tagged_reb`/`rebChooseTW_top` (`Reborrow.lean`) |
| `Records` | `Records.lean`, `Splits.lean`, `RecordPrograms.lean`, re-derived in `CDerives` at `VTy` in the binary-tree encoding |
| `Places` | `Family.lean`, `FamilyPrograms.lean`, re-derived in `CDerives` at `VTy` payloads |
| `LeafPlaces` | `Steps.lean` (step inversions; `DelayNaive.lean` uses it too), `Weaken.lean`, `BlockBorrow.lean` (plain types, `famTy`, `shortenE`, `withborS`, typing), `BlockTrack.lean` (`withborS_ret`, `withborS_packed`, `wpTS_allocBorrow`), `BlockPrograms.lean` |
| `Recursion` (`Nu.lean`) | `StrRel.lean`, `Stream.lean`, `StreamPrograms.lean`, and the `str` cases of `Types`, `FrameRecords`, `Relation`, `ShapeMu`, `RelationFacts` and `Computation`, built the same way as `delay` |

## Decisions taken

1. **Relaxed is included.** `FrameLife.2` is `x ⊑ α`, and `TW.reb` asks `StratumLe W β`. No
   rule in Core uses the slack yet (`docs/consolidation-audit.md` §2.1).
2. **Records are binary trees of `⊗` with no trailing unit.** A record is `Shape.valTy`, the
   same tree as a block. Variants are `Shape.sumTy`. A field is a path (`FPath`).
3. **`Box<struct>` is the block form.** An owned struct is `refTy σ`, the family of its leaf
   references, handled by `allocS`/`freeS`/`withborS`. The one-cell `Ref σ.valTy` is a separate
   type (`MapMut`'s `L′`).
4. **Codata is two fixed formers.** `D A` with `fixD`, and `Str A` with `unfoldS`. There is no
   general `ν`.

Name collisions settled:
- Places' family term is `withborF2` (with `famTy2`, `cbTy2`), because `withbor2` is the
  `CDerives` constant of the paper's second `withbor` axiom.
- `Shape` is `Blocks.lean`'s alone.
- LeafPlaces' `famTy` is `Shape.famTy`.
- The typed world's frame records are `FrameRecords.lean`, which frees the name `Records`.

## Open

- **Block provenance** (deferred to the syntax design; `SPEC.md` §5).
  - Leaves of different blocks can be joined into one handle: `crossPack` is typed and runs,
    but its handle is no block's (`crossPack_not_packed`).
  - A `foldReuse` hole can be refilled into another node.
  - Neither is excluded by typing. The model is sound either way, but lowering a handle to one
    word needs both excluded.
- **Records.**
  - `getAt`/`loadField` need the dropped fields `Affine`. `Imm̲ 'b A` is shown affine only when
    `A`'s `⊗`/`⊕`/`[@a]` spine holds no `μ` or type variable (`affine_immReborrow` with
    `VTy.SpineMuFree`), because `Affine` has no `μ` case. So an `Imm` record cannot yet be
    projected past an unboxed `μ`-typed field. `swapField`, `recE` and `loadCase` do not need
    this: `bagProg` updates a list field through `Mut`.
  - Variants in place: `Ref` does not distribute over `⊕`.
- **Family borrows.**
  - `withborF2`'s `B` and `T` must outlive the outer lifetime (`VOutlives`, which admits
    `0`/`μ`/`X`, but has no rule at `U C` or `Unk`).
  - A generic n-ary family over a list of leaf types, or over `μX. 1 ⊕ (Ref A ⊗ X)`, is not
    built. Nesting is written out per program (`splitFour`).
- **Block borrows.** `withborS`'s leaves and result are `plainV`: `1`, `0`, `⊗`, `⊕`, `Ref`, `!`,
  `X` and `μ`, with no lifetime and no `U C`. That is narrower than `withborF2`, which admits
  `Imm @e`/`Mut @e`/`[@e]` leaves and results that outlive the outer lifetime. I have not
  derived `withborS` at such leaves, and I have not verified that any obstruction to it is real.
- **Streams.** Only `A = 1` has a generic consumer with a stated adequacy theorem (`take_runs`).
  Every other stream program is a single closed derivation.
- **From the audit** (`docs/consolidation-audit.md` §5), still open:
  - outlives at `U C`/`Unk`, so a `foldImm` result that borrows into the structure is not
    covered;
  - the positivity condition `NoMut`, and `X` under `U` (no W-types);
  - the fold class `FShape`: `X` under `Ref` of a compound, or under `Imm`, `Mut`, `!`, `[@a]`
    or `U`, is excluded;
  - reuse tokens are not tied to their node, and a sized layout would need them sized;
  - same-lifetime projection (P2);
  - the delay type: the cancellable `bind`, adequacy without `close`, and a direct `fix`;
  - from `CBPVWorld`: no agreement with the old world, the three derived forms, and
    call-by-value axiom types;
  - from `SPEC.md` §2: promotion at every value, and conservative extension;
  - the machine has no address arithmetic, and `Loc = ℕ`.
