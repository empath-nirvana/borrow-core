# ProbeD1: the D1 tractability probe

The design is `DESIGN.md`; its §15 is the build's outcome in full. This file says what was asked,
what was proved, what was not, and what that does and does not tell us.

Build with `lake build ProbeD1`. There is no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`,
`unsafe` or `implemented_by`, and every result's `#print axioms` is within
`[propext, Classical.choice, Quot.sound]`.

## The question

Synthesis §11 asks whether the fundamental lemma at W (D1's world: rows, and ghost end at a stop,
with a lend re-lent at a fresh lifetime at each resume) is provable for exactly the rules `genSelf`
and `reconB′` use, at one world, with the arising guard read from `TW`, with one future-world
quantifier, and with no relation family beside W.

Statement 0 comes first. It fixes W's `U`, `⊸` and `∀` clauses together, in one `mutual` block,
at three candidate placements of the future-world quantifier: `cbpv` (at `U` and the stop's share,
OQ-8 option 2), `binder` (at `U`, the share, `⊸` and `∀`, option 3) and `binder0` (GhostEnd's
`vRLk`: at `∀` only, the own lend there). Its outcome was to decide OQ-8, and with it whether D1
meets "two algebras with interactions only at cuts".

## Statement 0: the outcome

**The shared lemmas hold** (`statement0Shared`): W's order is a preorder, a re-lend of a future is a
future of a re-lend, a future at a resource is one at its parts, avoidance composes, the share over
futures gives GhostEnd's piece at the stack itself, and at `σ = []` W's computations are Core's at a
data answer. So the stop rule's shared clause does not fire.

**Per placement:**

| fact | `cbpv` | `binder` | `binder0` |
|---|---|---|---|
| `MonoOwnG` (a context across the callback's own lend) | proved | proved | not derived |
| `MonoV`, `MonoG` (values and contexts along W's order) | proved | proved | not derived |
| `CallbackExtMut`, `CallbackExtImm` (the callback at `σ·y`) | proved when the bound does not mention the binder | proved | proved |
| `ForceRow`, `ThawRelend` | proved | proved | proved |
| `ThunkFRow`, `ThunkVRow`, `BangThunkFRow`, `BangThunkVRow` (the `U` introductions) | not derived | not derived | not derived; proved given the thaw of the row's own context (`CtxRelendableAt`), where re-lends keep `Δ`'s models (`ReLendModels`); `ThunkFRow` with that hypothesis discharged at `Γ = []` and at a `U` slot |

No fact of statement 0 was refuted (the hypothesis `CtxRelendable` the `U` rows first took was; see
below). `MonoHide` holds at `cbpv` and `binder` through `MonoHideFromMonoV`, which holds
at every placement.

**The own lend.** At the design's first `FutStep`, whose inserted variables had to be names no
program binds, the push of the callback's own lend (named by a program binder) was no future of the
stack, and `MonoOwnG` was not derived at a thunk slot at any placement. That is the case the design's
§13 step 2 provides for, and the build followed it: `FutStep` now admits any variable new to the
stack and to the reading substitution, the clause's own type avoiding it. The push is then a
one-step future, and at `cbpv` and `binder` `MonoOwnG` is `MonoG`'s instance there. `MonoOwnG` gained
one hypothesis, `δ.find? e.x = none`, which is the step's `vars_sub` at the push and holds at every
use. The cost the design named in advance stands: `BindersLow` no longer keeps an inserted variable
off the binders of the code that runs at the future, and `StackJ` admits a future's entry only under
such a name. A row that calls its premise at a future inserting another name meets the renaming
lemma.

**The `U` introductions are not derived at any placement.** Each owes the closure's body at every
re-lend of the stack (and at `cbpv` and `binder` at every future of the re-lend). GhostEnd proved
the clause's half from two hypotheses, the context re-lendable and the body at every re-lend. Both
are needs at every placement; `cbpv` and `binder` have further needs of their own:
- **the context's thaw under the table** (`CtxRelendableAt`, `Thunk.lean`);
- **the body at a re-lend**: the premise's `SemS` asks `Δ.Models` at the re-lent stack, and a
  re-lend need not keep it (`models_reLend_fails`): a variable of `Δ` off the stack, bounded by a
  stack variable, keeps its lifetime while the stack's is re-lent below it;
- at `cbpv` and `binder`, the context carried to a future that inserts between lenders, and the
  premise at a future whose inserted name `StackJ` does not admit. Neither is derived.

At `binder0` the first two are all that is missing: given `CtxRelendableAt` at the row's context,
the four rows hold at the configurations whose re-lends keep `Δ`'s models (`thunkFRow_binder0_at`
and its three siblings, with statement 1's `TabRelend` proved on the way).

## The two needs, settled at `binder0` (`Relendability.lean`)

**Q1, the context's thaw.**
- **The global hypothesis the rows first took is false**: `not_ctxRelendable_binder0`. So the four
  results stated with it were vacuous, as the content review suspected. They are replaced by the
  per-row forms above.
- **The refuting configuration `k`**: one `mut` entry lending the place `0` at `'0`, payload type
  `Unk`; the context `r : Mut '0 1` holding `0 ↦ mut(α, (), ∅, 𝒱⟦1⟧)` at the entry's own lifetime.
  The table admits the cell (it asks only the stratum `↓α` at a stack place), and no split of
  `RelendableS` places it (`k_not_relendableS`): it is not the entry's view, and it is not strictly
  above the outermost lend.
- **Restricting to the row's context and `SemS`'s index does not exclude `k`**:
  `not_ctxRelendableAt_k`, with `k_index` (`k` meets every index hypothesis `SemS` has, at
  `Δ = '0 ⊏ ⊤`).
- **Does `k` arise?** Its world does: `k_world_TW` (`alloc`, then `mutFold`), tagged. Its stack and
  context are reached by `binder0`'s own clauses from a closed derived term (`k_reached`):
  `Λ'0. λr. thunk (return r)` at `∀'0 ⊏ ⊤. Mut '0 1 ⊸ F (U (F (Mut '0 1)))`. The `∀` clause owes
  the body at every own lend `OwnPush` admits, `k`'s entry among them, and the `⊸` clause at every
  related argument, `r` at `k`'s cell among them. At `k`'s resource the `U` clause fails for every
  closure (`k_thunk_not_vRL`). Whether the closed term's own clause fails, through `wpTS`'s update
  of the answer's resource, is not derived. `ThunkFRow binder0` is not refuted.
- **What excludes `k` from a run is the lend's step, not `TW`.** `TW` does not see the stack.
  `PlaceViews` (every `mut` cell at a stack place is the innermost lending entry's view) fails at
  `k` (`not_placeViews_k`). A 6.65 lend opens with it at its place (`lendMut_placeView`), and `↭`
  keeps a `mut` cell's lifetime and predicate (`ResU.UpdMut`). That it holds at every `Arises`
  configuration is not proved. Neither `TabAtS` (so `SemS`'s index admits `k`) nor `OwnOK` (so
  `binder0`'s `∀` clause reaches `k`) carries it.
- **Where the restricted hypothesis holds**: `ctxRelendableAt_nil` (every placement) and
  `ctxRelendableAt_thunk` (`binder0`). So the rows are not vacuous: `thunkFRow_binder0_nil` and
  `thunkFRow_binder0_thunk` hold outright at the configurations whose re-lends keep `Δ`'s models.
  `CtxRelendableAt` is not proved at the contexts `PlaceViews` would restrict to.

**Q2, `Δ`'s models at a re-lend.**
- **What the rows need** is `ReLendModels Δ δ σ αs`: every re-lend of the stack models `Δ`. It is
  `SemSR`'s added hypothesis.
- **A sufficient condition**: `BoundsStackFree Δ σ`, no bound of `Δ` mentions a stack variable
  (`reLendModels_of_boundsStackFree`).
- **The failing configuration is reached by typing** (`q2_reached`): `Λ'0. Λ'1 ⊏ '0. thunk (return ())`
  is derived closed, its `U` introduction at `Δ = '0 ⊏ ⊤, '1 ⊏ '0`. At `binder0` the outer `∀`
  pushes the own lend of `'0`, and the inner `∀` instantiates `'1` below it. At that index `Δ`
  holds, `BoundsStackFree` fails, and the re-lend of `'0` at `'1`'s lifetime breaks `'1 ⊏ '0`, so
  `ReLendModels` fails. The `U` clause quantifies over that re-lend; the premise's `SemS` is not
  available there. Whether the clause fails there for some body is not derived.
- So this is a real obligation of the route, not an artefact of `SemS`: a `U` introduction inside
  `Λ'1 ⊏ '0` within a lend of `'0` is not covered by the rows as proved. Two ways to meet it, neither
  built: the re-lend also lowers every variable bounded by a stack variable (re-lend substituting
  the bound), or the `U` clause quantifies only over re-lends that keep the bounds. Either changes
  W's `U` clause, which is ours; neither changes a printed BoLo definition.

## What statement 0 decides

- **OQ-8: not decided.** No placement survives statement 0 and nothing is refuted, so W is neither
  decided nor provisional. The design's rule (§3) draws no consequence from "not derived".
- **The cuts question: nothing follows.** Whether D1 meets "interactions only at cuts", and D1's rank
  against D2a and D3, are where they were before the probe.
- **What the placements show apart from that.** `cbpv` and `binder` carry monotonicity at `U` by
  construction, the own lend's transport (after the `FutStep` change), the thaw and `[force]`.
  `binder0` stops at its own monotonicity, as the design expected: its `U` clause ranges over the
  stack itself, so a `U` value's computation must be carried along a future, and at `⊸` the old clause
  is read under the old stack's stronger guard. This is evidence about the proof routes, not a
  decision: a placement counts against itself only through a refutation that passes the arising check.
- **Failures (b) and (d)**: neither occurred. No guard beside `TW` and no relation family beside W was
  introduced, and no clause was changed to reach another stack by any means but `FutQ` and `OwnPush`.
  The `FutStep` change widened the futures `FutQ` ranges over; it added no way to reach a stack.

## Statements 1–7

Not attempted. The stop rule stops the probe after statement 0 when `Statement0 p` is proved at no
placement. OQ-58's facts (`NilAgrees` and the three beside it) wait on a bundle that holds, so they
were not attempted either. `reconB′`'s term was not committed, since statement 2 was not reached.

## What it means for D1, and for the fallback

- **D1's tractability is not settled by this probe.** Statement 0's per-placement facts that carry
  the quantifier's cost on the value side (monotonicity at `U`, the own lend's transport, the thaw,
  `[force]`, the callback at `σ·y`) are proved at `cbpv` and `binder`. The `U` introductions are not
  derived anywhere, and what they still need is named.
- **Q1 says the guard is missing a conjunct, not that the route fails.** The context's thaw fails at
  a configuration that `SemS`'s index admits and that `binder0`'s own `∀` clause reaches
  (`not_ctxRelendableAt_k`, `k_reached`). Its world is a `TW` world. What keeps it out of a run is
  `PlaceViews`, which a lend's step establishes and which `TabAtS` and `OwnOK` do not carry. Adding
  it to the guard and to the own lend is a change to W's definitions (statement 1 would then owe
  its preservation). Whether that is enough for the thaw at every context is not derived.
- **Q2 says the re-lend is missing something.** A `U` introduction inside `Λ'1 ⊏ '0` within a lend of
  `'0` is reached by typing at `binder0`'s own clauses, and there a re-lend of `'0` breaks
  `'1 ⊏ '0` (`q2_reached`). The rows as proved do not cover it. D1's ghost-end route needs the
  re-lend to keep such bounds: either it also lowers the variables bounded by stack variables, or
  the `U` clause quantifies only over re-lends that keep them (`ReLendModels`). [unchecked] A resume
  re-lends at a fresh lifetime, below every lifetime in the world, so the second option would
  exclude the very resumes D1 needs whenever such a variable is in scope, and the first is the
  likelier route. Neither is built.
- **The fallback is not triggered.** D3, then D0, follow a machine-checked failure: (a) a refutation
  at a configuration that arises, (b) a guard beside `TW` or a second relation family, or (d) two
  quantifiers. None occurred: no row is refuted, and `k_thunk_not_vRL` is a failure of the `U`
  clause at `k`'s resource, not of a row. Nothing here is evidence that D3 or D0 is needed, and
  nothing is evidence that it is not. D3 keeps the closure's lifetime across the stop, so Q2's
  re-lend does not arise there [unchecked].
- **The next step** was to add `PlaceViews` to the guard and to `OwnOK` and retry the thaw, and to
  choose how a re-lend treats the variables bounded by stack variables. The freeze-binder unit below
  did both at `binder0`. What remains is listed there: R1, the revised relation's obligations at the
  other rows, and the names the changed `FutStep` gives (a `StackJ` that admits them with a hygiene
  the rows can discharge, or the renaming lemma).

## The freeze binder (`BINDER.md`): the outcome

The unit after statement 0 reads its two shared needs through the binder: a place the stack lends
is bound, and a borrow cell there is the binder's view (PlaceViews); a resume instantiates every
internal lifetime, preserving their order. `BINDER.md` is the design, and its §11 is the build's
outcome in full. Every refutation below is at a configuration not shown to arise, so each is a fact
about our statement and decides nothing by itself.

- **PlaceViews.**
  - The guard's facts are proved at a part, a lend's start and end, a handler, the resume and an
    instantiation.
  - Along `↭` and a run they are proved at a stack whose places are distinct (`pvlUpdN`,
    `pvlRunsN`), and every `ArisesI` stack has distinct places (`placesNodupArises`).
  - PlaceViews holds at the world of every `ArisesI` configuration (`pvArises`), so `k` is not in
    `ArisesI` (`kNotInArises`). That is not a proof that `k` does not arise.
  - Not derived: the run facts at repeated places. Not attempted: `PVLFut`, which `binder0` does not
    read.
- **The lifetime binder.**
  - The re-lend is an order-preserving instantiation at the stack's cut. It keeps every `Δ`'s models
    (`reLendModelsI_of`), so Q2 is settled with no condition on `Δ`.
  - Three steps of the design's plan were refuted: `ExtInst`, `CohEInst` at an outermost lend at `⊤`,
    and `MutPayloadInst`'s support conjunct.
- **`mut_not_natural`.**
  - Whether its witness arises is still undetermined. The `TW`-history check below tells nothing,
    because `mutFold` accepts any predicate. The `ArisesI`-level check (`InternalPayloadArises`,
    `MutWitnessThawsInhabited`) was not attempted.
  - Its witness is a part of a tagged `TW` world (`notVDenNaturalArises`). `mutFold` takes any
    predicate, so that is not arising.
  - At the view slot the instantiation re-establishes the slot from the handed view
    (`mutWitnessThaws`).
  - At the retained part its mechanism appears as the refuted support conjunct, which is evidence and
    not an obstruction.
- **The `U` introductions.**
  - The design's targets are refuted as stated.
  - The build revised the draft relation (`vRLJ`) in three places, each answering a refuted step:
    `KeepsT`, `RetainedPay` and `OuterBelowTop`.
  - **At `vRLJ`, the four `U` introductions, the context's thaw and `ThawInstJ` are proved at
    `binder0` at every `CtxThawFree` context** (`statement0UThawFreeJ`). No `ReLendModels`
    hypothesis remains.
  - Not derived: the thaw at a `μ` or `fam` slot (guarantee gap R1), and the revision's obligations
    at the other rows.
- **What it decides.**
  - Statement 0's two shared needs are met at `binder0`, at the revised relation `vRLJ`, at
    `CtxThawFree` contexts, conditional on `RetainedPay`, `KeepsT` and `OuterBelowTop`, which are
    owed at the other rows. `RetainedPay` moves `mut_not_natural`'s retained-part case into the rows
    that introduce a `Mut` or `Imm` value; it does not settle it. The result is partial (R1), and
    `binder0` still stops at its own monotonicity.
  - OQ-8 is not decided. No failure of type (a), (b) or (d) occurred, and the fallback is not
    triggered.

## Files

| file | contents |
|---|---|
| `DESIGN.md` | the design; §15 the outcome; *Unresolved* the second review's findings, answered and not reviewed again |
| `ProbeD1/World.lean` … `Programs.lean` | the definitions and `def … : Prop` statements |
| `ProbeD1/Order.lean` | `extPreW`, `futPart`, `futAvoidsTrans`, `futReLend`; a step keeps the stack in shape |
| `ProbeD1/Bridge.lean` | `openSFBridge`, `nilSoundRet` |
| `ProbeD1/Shared.lean` | `statement0Shared` |
| `ProbeD1/Views.lean` | a future's views, outermost lend and reading substitution (`vwS_fut`, `stratS_fut`, `extS_find_fut`) |
| `ProbeD1/Mono.lean` | `monoV_cbpv`, `monoV_binder`, `monoG_*`, `monoHideFromMonoV`, `monoHide_*` |
| `ProbeD1/Own.lean` | `ownPush_futStep`, `monoOwnG_of_monoG`, `monoOwnG_cbpv`, `monoOwnG_binder`, `monoOwnG_uFree` |
| `ProbeD1/Rows0.lean` | `forceRow`, `thawRelend`, `callbackExt*` |
| `ProbeD1/Thunk.lean` | `CtxRelendable`, `CtxRelendableAt`, `models_reLend_fails`, `tabRelend`, `SemSR`, the four `U` introductions at `binder0` given `CtxRelendableAt` |
| `ProbeD1/Relendability.lean` | Q1: `not_ctxRelendable_binder0`, `not_ctxRelendableAt_k`, `k_index`, `k_world_TW`, `k_reached`, `k_thunk_not_vRL`, `PlaceViews`, `lendMut_placeView`, `not_placeViews_k`, `ctxRelendableAt_nil`, `ctxRelendableAt_thunk`, `thunkFRow_binder0_nil`, `thunkFRow_binder0_thunk`; Q2: `ReLendModels`, `BoundsStackFree`, `reLendModels_of_boundsStackFree`, `q2_reached` |
| `BINDER.md` | the design of the freeze-binder unit: PlaceViews in W, the re-lend as an order-preserving instantiation, the arising check of `mut_not_natural`, the `U` introductions retried; §11 the build's outcome; *Unresolved* the four review findings and their status |
| `ProbeD1/Binder.lean` | that design's relation-independent definitions and `def … : Prop` statements, and the revised own lend, futures and arising set (`OwnPushI`, `FutI`, `ArisesI`); no proofs |
| `ProbeD1/BinderW.lean` | the design's revised relation (`vRLI`, `cRLI`, `gRLI`, `SemSI`) and the `U` introductions retried at it (`Statement0UFull`); no proofs |
| `ProbeD1/BinderInst.lean` | the instantiation's bookkeeping, readings, records and freshness: `instModels`, `reLendModelsI_of`, `instComp`, `keepsSComp`, `subOutsideInst`, `instFreshExists` |
| `ProbeD1/BinderPV.lean` | the guard's local facts: `pvlParts`, `pvlStart`, `pvlEnd`, `pvlHide`, `pvlResume`, `guardInst` |
| `ProbeD1/BinderPVRun.lean` | the guard along `↭` and a run at distinct places: `pvlUpdN`, `pvlRunsN` |
| `ProbeD1/BinderRefute.lean` | `not_extInst`, `not_cohEInst`, `not_mutPayloadInst`, `not_instEquivLeaf`, `not_statement0UThawFree`, `not_statement0UFull` |
| `ProbeD1/BinderJ.lean` | the draft relation as the build revises it (`vRLJ`, `RelendJ`, `SemSJ`) and the `U` introductions at it |
| `ProbeD1/BinderRows.lean` | the thaw (`relendJ_value`, `ctxRelendsThawFreeJ`), `thawInstJ`, the four rows, `statement0UThawFreeJ` |
| `ProbeD1/BinderArise.lean` | the arising check of `k`: `pvArises`, `arisesInv`, `kNotInArises`, `kSlotNotW`, `placesNodupArises` |
| `ProbeD1/BinderRisk.lean` | `notVDenNaturalArises`, `mutWitnessThaws`, `mutWitnessThaws_met`, `viewSlotInstCS`, `viewTypeCoincidence` |
