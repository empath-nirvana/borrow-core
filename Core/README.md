# Core: the consolidated world

One CBPV typed world holding `μ` and the three folds, blocks, records and variants, family
borrows, block borrows, the delay type with `fixD`, the stream type with `unfoldS`, the
integer types with the host operations, and arrays. It is the library's implementation of `SPEC.md` §3–§8
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
        | I32 | I64 | U8 | [A] | Input | Output
    C ::= F A | A ⊸ C | C & C | ⊤ | ∀'a ⊏ @b. C | νX. C

`I32`, `I64` and the byte `U8` are one constructor, `VTy.int w` (`Integers.lean`, `[spec §8]`);
the byte has only its conversions `wrap8`/`extend8_u`, and the grouped operations at `w8` take
`0`. The relation
holds a literal of the width at `∅`, so they are persistent, `Imm̲ 'b I = I`, and they outlive
every lifetime.

`Input` and `Output` are one constructor, `VTy.opq k` (`Opaque.lean`, `[spec §11]`): a leaf with
no rule, whose relation is the model `k.Holds` in both modes (a byte list; a descriptor and the
bytes written), with `Imm̲ = Unk`, not persistent and with no destructor.

`νX. C` (`[spec §7]`) has `U X` as the type variable `0` of `C`'s value types, and at a positive
`C` (`CTy.NuOk`) is interpreted as a greatest fixed point equal to its unrolling (`NuRel.lean`,
`cC_nu_iff`). `D A`, `Stream A` and `Iter A R R'` are abbreviations over it (`CTy.delay`,
`CTy.stream`, `CTy.iter`). An observation may take a closed argument, `A ⊸ D`, and the rest may be
boxed, `[@a] U X` (`[spec §22]`); the affine closure `Aff^c A B = νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`
is the instance that uses both, with its relation clause, coinduction and observable-view facts
in `Aff.lean`, its derived rules (introduction, call, call through `Mut`, close, the two
coercions) in `AffRules.lean`, and its programs in `AffPrograms.lean`.

### The judgment `CDerives Δ Γ e j`

`Fundamental.lean`. It has the CBPV formers, the lifetime `∀`, the `!` rules, `[]I`/`[]E`,
`⊑Imm`/`⊑Mut`, and one constant per borrow axiom at arbitrary value-type payloads. It also has
three call-by-value forms (`lolliE`, `allEV`, `ofRet`), the integer literal `lit` and the host
operation `hostOp` (below), `roll`/`unroll`, the folds `foldImm`,
`foldOwn` and `foldReuse`, and `nuIn`/`nuOut` with coiteration (`Nu.lean`):

    unfoldN : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)

`fixD`, `unfoldS` and `delayIn`/`delayOut`/`streamIn`/`streamOut` are these rules at the delay
and stream bodies. `Loop A B = νX. F(A ⊕ U X) & F B` (`CTy.loop`) is the loop whose `close`
returns a residual, and `D A = Loop A 1`; the driver `driveE n` is typed at every loop
(`d_driveL`, `DelayPrograms.lean`).

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

### Arrays  `[spec §9]`

`[L]` (`VTy.fam L`, `Types.lean`) is the run-time family `⊛_{i<n} L` of leaf places: a value
`(ℓ, n)` whose leaf `i` is the location `ℓ + i`. The relation and the shape relation read it as
the iterated separating conjunction `sepRange` (`SepRange.lean`) of `L`'s clause at the leaf
locations. `Array A = [Ref A]`; `ArrayImm @a A = [Imm @a A]` is `Imm̲ 'a (Array A)`, the family
`withload` gives at a borrow of a cell holding an array. `RefPos`/`MutPos` have the leaf
positions of a family, and every lemma proved by induction on types or positions has its `[L]`
case (6.131 `reborrow_vShape`, 6.60 `vC_outlives`, the images and invariants of reborrowing).

The machine's steps `tab`, `idx`, `drop` (`Paper/S3_Dynamics/Definitions.lean`,
`Support/Dynamics/Arrays.lean`) are put in front of `wpTS` by `wpTS_tab` (`n` of `TW.alloc` at the
allocator's block, `alloc_block`), `wpTS_idx` and `wpTS_dropStep` (`ArrayWp.lean`). The constants and
their compatibility lemmas are `Arrays.lean`: `array_new` (`tabFill_wp`), `array_free`
(`dropFill_wp`), `array_size`, `array_replace`, and on families `array_len`, `array_get`,
`array_copy`, `array_forget`. `HasDtor` has `Array A`, `ArrayImm @a A` and `ArrayMut @a A` (`Dtor.lean`).
`ArrayPrograms.lean` runs one program by adequacy and by the interpreter. The relation's
clause carries the length bound `c < 2³¹`, so a family has `tab`'s length (`arrLen_of_bound`).

An owned array is lent as a family of leaf borrows with no cell by `slice_borrow_mut` and
`slice_borrow_imm` (`Slices.lean`, `withbor`'s term): one Mut or Imm Frame per leaf around the
one callback, by induction on the list of places (`wpTS_M_frameList`, `wpTS_I_frameList`,
`SliceFrames.lean`, with the split `vP_fam_split`/`vP_fam_join`). On `[Mut @a A]`,
`slice_get_mut` (`idx`) and `slice_len_mut` (`array_size`'s term). `SliceOps.lean`: a
borrowed family is split at a run-time index by the step `split` (`famSplit_compatX`, from
`vP_fam_split`), `(0, 0)` is the empty family (`famEmpty_compatX`), and a `mut` family is
written at an index by Mut Anti-Frame on the leaf (`sliceReplaceM_compatX`,
`sliceSwapM_compatX`, two leaves by `sepRange_pick2N`). `HasDtor` has `ArrayMut @a A`, derived
from `slice_get_mut` and `forget`.

### Standard I/O  `[spec §11]`

`Stdio.lean`. The capabilities and their operations are externs, hypotheses of the end-to-end
theorem. `Bytes = μX. 1 ⊕ (I32 ⊗ X)` and `I32 ⊗ Bytes` are the representations of `Input` and
`Output`, and the relation at each is the opaque type's (`vC_bytes`, `vC_outRep`). The model of
`read_byte`, `write_byte` and the harness `mk_input`, `mk_output`, `take_input`, `take_output`
is core terms at the representation, typed in `CDerives` (`d_readByte`, …), so each meets its
extern's contract (`readByte_meets`, …, by `meets_of_derives` and the transparency). End to end:
`externs_every_run`/`externs_safe` (every implementation meeting the contracts, `ExternsMeet`)
and `io_every_run` (the model, `stdModel`) run a checked `run_io : Bytes ⊸ F R` from the empty
memory under every allocator to a value at the empty memory; `externs_main_safe` is
`fundamentalD` at `main`; `externs_loop_every_run`/`io_loop_every_run` cover a `run_io` that returns
a loop, one prefix `driveE n` at a time (`d_ioLoop`); `wpTSD_frame_own` keeps a frame's cell as it was (no capability, no
effect).

### Theorems

- **Fundamental Property.** `fundamentalC : CDerives Δ Γ e j → SemJ Δ Γ e j`, by induction
  over every constructor.
- **Adequacy.** `adequacyC` (with `theorem32` and `corollary33`): a closed computation of `F 1`
  runs to `()` and leaves memory empty.
- **Every run** (`SPEC.md` §13, `Alloc.lean`, `Demonic.lean`). `wpTS`'s run is an allocator run
  (`ARun`) under every allocator (`Alloc`: at the `k`-th allocation from memory `μ`, a free
  block at `pick k μ n`). Every run of the machine is an allocator run of the allocator that
  replays it (`steps_replay`), and allocator runs are deterministic (`AStep1.deterministic`), so
  `wpTS` implies the demonic `wpTSD` (`wpTS_demonic`): every run continues to a value run that
  lands in the postcondition. `fundamentalD` is the Fundamental Property at `wpTSD`;
  `adequacyD`: every run of a closed `F 1` program from empty memory continues to `()` at empty
  memory, so none is stuck (`adequacyD_safe`) and a value run ends at `()` with nothing
  allocated (`adequacyD_val`). `mapProgC_every_run` is the `withswap` window under a reusing
  allocator. The previous run conjunct is `wpTSAngelic` (`wpTS_angelic`). A borrowed `!` closure is in the
  relation only if it is safe under every allocator: `λ_. staleL`, which loads a location it
  freed, is in `wpTSAngelic` (`staleL_angelic`) but outside the relation at `!U(1 ⊸ F 1)`
  (`staleClosure_not_vC`, `Stale.lean`; #41).
- **Runs through a context, closed runs, computed runs** (`Steps.lean`, `Closed.lean`,
  `Run.lean`). A run of `K[e]` is `K` around a run of `e`, or it runs `e` to a term that takes no
  step and goes on from `K` around that term (`steps_plug_split`, `step1_plug_of_step`); a
  context is determined by the non-value it holds (`plug_inj_ctx`). A typed term is closed at its
  context (`closedAt_of_derives`), and a run from a closed term whose stored values are closed
  keeps both closed (`closed_steps`). `runM` computes a run at a finite memory, `look` deciding
  each step that leaves the memory alone (`look_sound`; a row of them is a chain of head steps,
  `lookRun_sound`); every run `runM` computes is a run of the machine (`runM_sound`), so a closed
  program's run to a value is proved by `rfl` (`runM_val`).
- **The handler laws as machine lemmas** (`SPEC.md` §19 *Laws*, §25, `EffMachine.lean`), in every
  context, each step its configuration's only step (`Step1Only`, `step1Only_plug`) but an
  allocation. H-ret (`catch_ret`); H-op: the catch hands the clause `kappa` at an unrestricted
  operation (`catch_unr`), and at a linear or affine one allocates `κ`'s cell at a free location and
  hands `kappaC` there (`catch_cell`), every run from the catch a prefix of those three steps or
  going on from them (`catchEv_cell`); resuming `kappaC` releases the cell and runs `hnd H K[w]`
  (`kappaC_resume`), an affine cancel releases it and cancels (`kappaC_cancel`), a linear cancel has
  no step (`kappaC_cancel_lin`), and on a run to a value a use of `κ` releases its cell three steps
  later (`use_frees_cell`); H-fwd (`catch_fwd`, `fwd_resume`, `fwd_abort`); `[unwind]`, `[then]` and
  `[finalise]` (`catch_abort`, `then_ret`, `then_fin`). A2: `raise p` under frames that catch
  nothing of its name steps, in every context, as `raise p` does (`abort_absorbs`, `abort_to`,
  `abort_app`).
- **Totality** (`SPEC.md` §14, `Totality.lean`). A closed computation of `F A` terminates on every
  run: under every allocator its run reaches a value (`total_every_alloc`), every run under an
  allocator is a prefix of it (`total_run_prefix`), every run continues to a value
  (`total_every_run`), and there is no infinite run (`total_no_infinite_run`, through the
  allocator `Alloc.ofRun` built from the run).
- **Effect safety** (`SPEC.md` §19 *Laws*, `EffSafety.lean`). Every configuration a typed closed
  program reaches from the empty memory is a value or steps, and is no operation that no live frame
  catches: no `K[perform p]` with `K` free of a handler of `p`'s name, no `K[raise p]` with `K`
  catching nothing of it (`effSafe_closed`). Each such configuration is `LiveOK`: its term and
  stored values are closed, and it goes on (`liveOK_closed`), so it holds no stuck redex
  (`LiveOK.not_stuck`). At a persistent answer a run to a value ends at the empty memory, every
  continuation's cell released (`leakFree_closed`, `EffPrograms.lean`).
- **Decision R: one signature per operation** (`SPEC.md` §19 *Typing*, `Tied.lean`). An effect
  context `Ξ` gives each name its signature; a row is tied to `Ξ` when every operation it finds is
  at `Ξ`'s signature (`RowAt`). `CDerivesAt Ξ` is `CDerives` with `RowAt Ξ` at `[perform]`,
  `[raise]` and `[handle]`, every other rule verbatim; a tied derivation is a `CDerives` derivation
  (`CDerivesAt.toCDerives`), and one of a term with no `perform`, `raise` or `hnd` is tied at every
  context (`CDerivesAt.ofEffFree`). At a handler its signature is a prefix of `Ξ`'s
  (`sig_prefix_of_rowAt`, `hndTags_of_rowAt`). `EffCtx.NoUnrExn`: no abortive operation is
  unrestricted (§18); in a row tied to such a context an unrestricted operation resumes
  (`abort_false_of_rowAt`). The checker builds every derivation tied (`Frontend/Check/Tied.lean`).
- **The names a run raises** (`SPEC.md` §19 *Typing*, `RaiseNames.lean`). `Expr.RaiseOK P`: every
  raise of a term is of a name in `P` or a cancel, every cancel state keeps none or a raise of a
  name in `P`, and `cfin` holds only a cancel state. No step leaves it, nor stores a value that
  does (`HeapRaiseOK`), when `0` is not in `P` (`raiseOK_step1`, `raiseOK_steps`). A tied term
  is at its effect context's names, `EffCtx.Names` (`raiseOK_of_derivesAt`; `rcE` decides it), so
  every configuration its runs reach from the empty memory is at them (`raiseOK_reach`), and at
  every cancel of `κ` they reach, the cancelled region's running finalisers keep none or an error
  of such a name (`CancelsNamed`, `cancelsNamed_of_derivesAt`).
- **The unwind and the cancel, on every run** (`SPEC.md` §19 *Laws* items 5 and 6,
  `EffCancelRuns.lean`). A step at a raise is the step of the innermost frame that stops it
  (`step1_raise`, `innerCatch_unique`). Read over paths (`Path`), prefix-closed: from a raise
  pending under frames with no running finaliser's `cfin`, every path is a prefix of the unwind
  trace (`unwind_prefix`, `UnwindTr`): the finalisers fire innermost first, each running alone, one
  that returns `()` hands the raise on and one whose raise escapes supersedes it. From the start of
  a continuation's cancel run, `kappa H K` or `kappaC aff ℓ H K` after its cell's release, in a run
  of a tied term, every path is a prefix of the cancel trace of `K†` (`cancel_prefix`,
  `CancelTr`): `K`'s finalisers fire innermost first, a running finaliser's `cfin` is passed by
  `[cfin-cancel]`, the first kept error wins, and the canceller gets `()` or the kept error, of a
  name of the effect context. The hypothesis is each finaliser's typing at a row of abortive
  operations (`FinRow`), which makes it run alone from every finite memory (`finAlone_of_finRow`,
  `finOK_of_finRow`, through `ownWorld` and `wpG_seg`). On complete runs, given that each fired
  finaliser runs alone to a value or an uncaught raise (`FinAloneAt`): `finaliserOrder_at`
  (`CancelRun`, `UnwindRun`). `progOutT` meets `cancel_prefix`'s hypotheses
  (`progOutT_cancel_prefix`), and so does `progOutTA`, the same program at an affine raise, typed
  at an effect context with no unrestricted abortive operation (`progOutTA_cancel_prefix`).
- **Inversions, and what no derivation types** (`SPEC.md` §19 *Laws* item 4 and *Programs*,
  `Inversions.lean`, `Rejections.lean`). Each inversion is an induction on `CDerives` that carries a
  class of judgements through the rules concluding with their premise's term: a variable is read at
  a view of its live slot's type (`der_var`), an application is typed by a rule that concludes with
  one (`der_app`), a λ-value through the rule that types its body or as a constant (`der_lam`),
  `swap` at its axiom alone (`der_swap`), and every free variable of a typed term has a live slot
  (`fv_live`). A clause's linear or affine `κ` is neither dropped nor used twice, nor cancelled at a
  linear operation (`refuses_R_clauses`, `clauseRefusals_pinned`), and `at05`, `at06`, `at08` and
  `at13` have no derivation at all (`not_der_at05`, …). `at08Once`, `at08` with the copy used once,
  is typed and every run of it ends at `()` (`d_at08Once`, `at08Once_runs`; the kernel program
  `at08-once`). A rule added to `CDerives` adds a case to each inversion.
- **What §27's typing rejects** (`SPEC.md` §19 *Laws* item 6, §27 *Programs*,
  `EffCancelTyped.lean`). `[handle]`, `[then]`, `[perform]`, `[raise]`, `[let]` and `bind` are
  read with their premises at their conclusions, and the rules that conclude with their premise's
  term only grow rows (`der_hndJ`, `der_thenJ`, `der_performJ`, `der_raiseJ`, `der_letJ`,
  `JR.rowLe`, `Inversions.lean`). So a finaliser's raise is recorded in the cancel row of the
  operations its computation performs, and the clause that cancels reads it at its own row:
  `progT` has no derivation at a row without `2` (`not_der_progT`), `progNCrecT` none at all
  (`not_der_progNCrecT`), and E7c (`e7c`) none at a row without `exnᵢ` (`not_der_e7c`), while at
  the row of `exnᵢ` it is typed by a tied derivation (`dAt_e7c_lift`, `d_e7c_lift`).
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

- `wpTSAngelic_allocS`: on some run, a block is allocated at consecutive locations. `allocS` is a
  sequence of `alloc`s, so under an allocator that does not place them consecutively the leaves
  are not one block (`SPEC.md` §13).
- `withborS_ret`: a block borrow returns the handle it was given, on every run.
- `withborS_packed` (every run) and `wpTSAngelic_allocBorrow` (some run): after the borrow, the
  handle is packed again at the
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
| `ArrayPrograms.lean` | `arrProg`: `array_new` of three elements, `array_replace` at index 1, `array_size`, `array_free`; observed `(inl 11, 3)` and no cell left |

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
| `LeafPlaces` | `Steps.lean` (step inversions; `DelayNaive.lean` uses it too), `Weaken.lean`, `BlockBorrow.lean` (plain types, `famTy`, `shortenE`, `withborS`, typing), `BlockTrack.lean` (`withborS_ret`, `withborS_packed`, `wpTSAngelic_allocBorrow`), `BlockPrograms.lean` |
| `Recursion` (`Nu.lean`) | `StreamPrograms.lean`; the stream former it gave became an instance of the general `νX. C` (`NuRel.lean`, `Nu.lean`) |
| `FnMut` (#236, #239) | the positivity relaxation (`Types.lean`, `Relation.lean`, `RelationFacts.lean`, `NuRel.lean`, `Computation.lean`, `Nu.lean`); `Aff.lean`, `AffRules.lean`, `AffPrograms.lean` (the programs in the sub-namespace `Aff`) |

## Decisions taken

1. **Relaxed is included.** `FrameLife.2` is `x ⊑ α`, and `TW.reb` asks `StratumLe W β`. No
   rule in Core uses the slack yet (`docs/consolidation-audit.md` §2.1).
2. **Records are binary trees of `⊗` with no trailing unit.** A record is `Shape.valTy`, the
   same tree as a block. Variants are `Shape.sumTy`. A field is a path (`FPath`).
3. **`Box<struct>` is the block form.** An owned struct is `refTy σ`, the family of its leaf
   references, handled by `allocS`/`freeS`/`withborS`. The one-cell `Ref σ.valTy` is a separate
   type (`MapMut`'s `L′`).
4. **Codata is one former, `νX. C`.** `D A`, `Stream A` and `Iter A R R'` are abbreviations, and
   `fixD`/`unfoldS` are coiteration at their bodies (`docs/decisions.md` 26).

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
- **Arrays.** `split_at` (K3), the writes that keep a `mut` family (K5), `iter`/`iter_mut`,
  `Vec`, `Str` are not built, and `[Mut @a A]` has no destructor (`SPEC.md` §9 Open). `[L]` is not
  in `SpineMuFree`, so an `Imm` record cannot be projected past an array field.
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
