# Core: the consolidated world

One CBPV typed world holding `μ` and the three folds, blocks, records and variants, family
borrows, block borrows, the delay type with `fixD`, the stream type with `unfoldS`, and the
integer types with the host operations. It is the library's implementation of `SPEC.md` §3–§8
and §10; code an entry adds is tagged `[spec §N]` (each file's heading, and the main
definitions, rules and theorems).

Build: `lake build` (`Core` is a default target) or `lake build Core`. Namespace
`BoCa.Fig16.LogRel.Core`, so names of the typed world in `BoCa.Fig16.LogRel` resolve
unqualified. Core imports only `Paper`, `Support` and `Examples`.

`scripts/check-hygiene.sh` covers `Core/`: no `sorry`, `axiom`, `native_decide`,
`implemented_by`, `opaque`, `partial` or `unsafe` outside comments, and every declaration's
axioms among `[propext, Classical.choice, Quot.sound]` (`scripts/CheckAxioms.lean`).

## What it contains

### Types

    A ::= 1 | A ⊗ A | 0 | A ⊕ A | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk | X | μX. A
        | I32 | I64
    C ::= F A | A ⊸ C | C & C | ⊤ | ∀'a ⊏ @b. C | D A | Stream A

`I32` and `I64` are one constructor, `VTy.int w` (`Integers.lean`, `[spec §8]`). The relation
holds a literal of the width at `∅`, so they are persistent, `Imm̲ 'b I = I`, and they outlive
every lifetime.

`D A = νX. F(A ⊕ U X) & F 1` and `Stream A = νX. F(A ⊗ U X) & F 1` are fixed formers. Each is
interpreted as a greatest fixed point (`delayRel`, `streamRel`) and is equal to its unrolling
(`cC_delay_iff`, `cC_stream_iff`). There is no general `ν`.

### The judgment `CDerives Δ Γ e j`

`Fundamental.lean`. It has the CBPV formers, the lifetime `∀`, the `!` rules, `[]I`/`[]E`,
`⊑Imm`/`⊑Mut`, and one constant per borrow axiom at arbitrary value-type payloads. It also has
three call-by-value forms (`lolliE`, `allEV`, `ofRet`), the integer literal `lit` and the host
operation `hostOp` (below), `roll`/`unroll`, the folds `foldImm`,
`foldOwn` and `foldReuse`, `delayIn`/`delayOut` with `fixD`, and `streamIn`/`streamOut` with
`unfoldS`:

    fixD    : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)
    unfoldS : !U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)

Its context premises are `Ctx.SplitP`, `Ctx.DeadP` and `Ctx.SoloP` (`Persistent.lean`,
`[spec §10]`), which extend the paper's `Ctx.Split`, `Ctx.Dead` and `Ctx.Solo`: a live slot of
persistent type (`VTy.persistent`: `1`, `0`, `Unk`, `I32`, `I64`, `!A`, and `⊗`, `⊕`, `[@a]`,
`μ` over persistent types) may go to both sides of a split and may be dropped at a leaf. The
relation holds such a value only at `∅` (`vP_empty_of_persistent`).

### Integers and the host  `[spec §8]`

The term language has two more constants, `Prim.lit c` (`i32[n]`, `i64[n]`) and `Prim.host op`,
one `HostOp` per Wasm integer instruction at each width: `bin w o` (`add sub mul and or xor shl
shr_s shr_u rotl rotr`), `div w o` (`div_s div_u rem_s rem_u`), `un w o` (`clz ctz popcnt
extend8_s extend16_s`), `eqz w`, `rel w o` (`eq ne lt_s lt_u le_s le_u gt_s gt_u ge_s ge_u`),
and `wrap`, `extend_s`, `extend_u`, `extend32_s` (`Support/Syntax/Integers.lean`).

The machine (`BoLo.Head`) has one more step, `op v ↦ r` when `ℍ.call op v = some r`
(`Paper/S3_Dynamics/Definitions.lean`). A `Host` (`Support/Dynamics/Host.lean`) gives each
operation a Lean function of its type (`UInt32 → UInt32 → UInt32`, `… → Option UInt32` for the
partial ones, `… → Bool` for the tests), and `Host.call` decodes the argument and encodes the
answer: a literal, `inj₁ ()`/`inj₂ ()` for false/true, `inj₁ n`/`inj₂ ()` where Wasm traps. An
ill-shaped argument is stuck.

The host is threaded as `{ℍ : Host} [HostIs ℍ]`, a section variable of every file over the
machine; `HostIs` carries no data and has no global instance. So every theorem over the
machine — the relation, `fundamentalC`, `adequacyC`, every `*_runs` — holds at every host, and
the machine is deterministic at each. `wasmHost` is Wasm's semantics on `UInt32`/`UInt64`; it
is the interpreter's default host (`eval e (H := wasmHost)`) and nothing else uses it.

Typing: `CDerives.lit c : I` at a consumed context, and one rule `CDerives.hostOp op :
!(hostArg op ⊸ F (hostRes op))`, the table of `SPEC.md` §8. `hostOp_compatX` proves every
operation sound by one host step, using only that `Host.call` answers at the stated type
(`host_call_sound`).

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
| destructors `dtorE T : T ⊸ F 1` at every `HasDtor T` (forgettable types, `Ref`, `⊗`/`⊕`/`[@a]`, fold-class `μ`, codata by `close`), and the drop `dropE T i e = (dtorE T xᵢ; e)`: `dtor_wf`, `drop_derives` (SPEC §12) | `Dtor.lean` |

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
| `StreamPrograms.lean` | `take_runs` (every closed `U(Stream 1)` observed `n` times and closed), `takeCloseR`, `natsSum` (`0 + 1 + 2 = 3`) |
| `IntPrograms.lean` | `sumToProg` (`fixD` over `I32 ⊗ I32`, `1 + … + 10 = 55`), `sumListProg` (`[100, 20, 3]` as `μX. 1 ⊕ Ref (I32 ⊗ X)`, read by `withload` inside an immutable borrow, `foldImm` sum `123`), `signProg` (`div_s`/`div_u` of `-7` by `2`, a wrapping `mul`, `div_u` by zero taking the error branch) |

The `IntPrograms.lean` runs are theorems at every host; the interpreter's results are at
`wasmHost`.

## Where it came from

| from | into `Core/` |
|---|---|
| `CBPVMu` | the base: every `CBPVMu/` file, renamed (`Records.lean` became `FrameRecords.lean`, the typed world's frame records) |
| `CBPVWorld` | `Embedding.lean`, `EmbeddingExamples.lean` (only the namespace changed) |
| `Relaxed` | `FrameLife.2` non-strict (`FrameRecords.lean`); `StratumLe` and `TW.reb`'s premise (`World.lean`); `frameLife_reb_like` (`Wp.lean`); the `lt_of_lt_of_le`/`lt_irrefl` steps (`Wp.lean`, `RelationFacts.lean`); `tagged_reb`/`rebChooseTW_top` (`Reborrow.lean`) |
| `Records` | `Records.lean`, `Splits.lean`, `RecordPrograms.lean`, re-derived in `CDerives` at `VTy` in the binary-tree encoding |
| `Places` | `Family.lean`, `FamilyPrograms.lean`, re-derived in `CDerives` at `VTy` payloads |
| `LeafPlaces` | `Steps.lean` (step inversions; `DelayNaive.lean` uses it too), `Weaken.lean`, `BlockBorrow.lean` (plain types, `famTy`, `shortenE`, `withborS`, typing), `BlockTrack.lean` (`withborS_ret`, `withborS_packed`, `wpTS_allocBorrow`), `BlockPrograms.lean` |
| `Recursion` (`Nu.lean`) | `StreamRel.lean`, `Stream.lean`, `StreamPrograms.lean`, and the `stream` cases of `Types`, `FrameRecords`, `Relation`, `ShapeMu`, `RelationFacts` and `Computation`, built the same way as `delay` |

## Decisions taken

1. **Relaxed is included.** `FrameLife.2` is `x ⊑ α`, and `TW.reb` asks `StratumLe W β`. No
   rule in Core uses the slack yet (`docs/consolidation-audit.md` §2.1).
2. **Records are binary trees of `⊗` with no trailing unit.** A record is `Shape.valTy`, the
   same tree as a block. Variants are `Shape.sumTy`. A field is a path (`FPath`).
3. **`Box<struct>` is the block form.** An owned struct is `refTy σ`, the family of its leaf
   references, handled by `allocS`/`freeS`/`withborS`. The one-cell `Ref σ.valTy` is a separate
   type (`MapMut`'s `L′`).
4. **Codata is two fixed formers.** `D A` with `fixD`, and `Stream A` with `unfoldS`. There is no
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
- **Integers.** `plainV` does not include `I32`/`I64`, so they are not yet `withborS` leaves.
  The `experiments/` libraries over the machine do not take the host parameter and do not
  build.
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
