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

## The instantiation's gap at `∀` (`GAP.md`): the outcome

`GAP.md` takes the step `BINDER.md` §11.2 left: `TyEqInst` at every type. Its §8 is the build's
outcome in full. Statements are in `ProbeD1/Gap.lean`; proofs in `GapWitness.lean`,
`GapCover.lean`, `GapRows.lean`, `GapPos.lean` and `GapRoom.lean`. No relation changed.

- **Proved: `TyEqInst` at every type** (`tyEqInst`). `TyEq` is a conjunction of equalities of
  lifetime terms under an unbounded `∀`, and an equality on a chain is decided threshold by
  threshold. So `TyEq` holds at every pair a family of `TyEq` pairs covers threshold by threshold
  (`tyEqOfCover`); an instantiated pair is covered by its source (`coverInst`), and an instance in
  the instantiation's gap by the image instances (`coverGap`, `tyEqGapStep`). `TyEq` is invariant,
  both ways, under every order embedding fixing `⊤`, those that open a gap included
  (`tyEqRoomBlind`).
- **Proved: the thaw and the four `U` rows at every payload type** (`statement0UThawFreeKJ`, at
  `binder0`). The `CoreStable` restriction on `Mut` and `Imm` payloads is gone (`cohEInstOB`,
  `viewSlotInstOB`, `relendJValueK`): the result holds at every `CtxThawFreeK` context, which
  excludes only slots with a `μ` or `fam` type outside a `Mut` or `Imm` payload (R1) and strictly
  contains `CtxThawFree`.
- **Proved: Core's `∀` reads the room between lifetimes.** At `∀'0 ⊏ ⊤. F (Mut '0 1)` the clause
  holds at a `mut` cell at `1`, adjacent to `⊤`, and fails at every `mut` cell at `2` with an empty
  witness, its image under `shift ⊤ 1` among them (`coreAllAdjacent`, `coreAllNotNatural`). So
  Core's relation is not invariant under an embedding that opens a gap.
- **The position-`∀`, both readings.**
  - (B), every cut below the stack's cut, realised by an instantiation: proved realisable
    (`instRealisesCut`), transported along instantiations (`allPosJTransport`), and Core's clause
    at `σ = []` both ways (`allPosJNil`). **W's `U` clause implies it for the body at a `U (∀…)`
    type** (`wU_allPosJ`; one way, and W's clause is strictly stronger). At the configuration where Core's `ℕ`-`∀` reads adjacency, W's `U` clause reads
    the cut and excludes the closure that Core's `U` clause admits (`adj_not_wU`, `adj_core_U`).
  - (A), every cut of the whole order, realised by renaming the configuration: one-way at
    `σ = []` (`cutAllNilSound`; the converse is refuted, `not_coreAllImpCutAll`). Not adopted.
- **`cRLJ`'s own `∀` is unchanged.** No statement carries a computation across an instantiation
  outside `U`, so (B) is not put there (`GAP.md` §3.4).
- **Open.** R1, the thaw at a `μ` or `fam` slot (`Statement0UFullJ`), not attempted here: its route
  is W reading `μ` and `fam` itself, in its own unit. `ViewSlotInst` without `OuterBelowTop` (every
  `SemSJ` index carries it). Everything else `BINDER.md` §11 lists as owed is unchanged.
- **What it decides.** The gap `BINDER.md` §11.2 left is closed with no relation changed, and the
  thaw's only guarantee gap is R1. OQ-8 is not decided. No failure of type (a), (b) or (d)
  occurred, and the fallback is not triggered.

## R1 and `binder0`'s monotonicity (`R1MONO.md`): the outcome

`R1MONO.md` takes four items at `binder0`:
- R1;
- `binder0`'s own monotonicity;
- the three obligations the freeze-binder unit left;
- statement 0 at the revised relation.

Its §8 is the build's outcome in full. Statements are in `ProbeD1/R1.lean`; proofs in
`R1Thaw.lean`, `R1Mono.lean`, `R1Owed.lean`, `R1Stmt0.lean` and `R1AllI.lean`. The one draft
relation is now `vRLM`: `vRLJ` with Core's `tvar`, `μ` and `fam` clauses read at W's formers.
`LendMutI` and `LendImmI` carry H4's consequence `α < ⊤`. Nothing in `Core/` or in a printed
definition changed. Every refutation below is at a configuration not shown to arise, so each is a
fact about our statement.

- **R1 is closed at `binder0`** (`statement0UFullM`).
  - The thaw holds at every type (`relendMValueE`), by structural recursion with the environment
    generalised. At `μ` it uses the fixed point's own induction; there is no step index.
  - The four `U` introductions hold at every context.
  - `vRLM` is `vRLJ` wherever no `μ`, `fam` or type variable occurs outside a borrow payload
    (`relMAgreesJ`, as proved at `5210cf1`). After the next unit's edits it is restated at types
    with no lifetime `∀` and no persistent thunk.
  - The `μ` slot at which Core's `μ` admits a closure by adjacency is no `vRLM` value
    (`muAdjNotVRLM`, proved at `5210cf1`). After (E1) the closure is a `vRLM` value
    (`muAdjVRLME1`), and `muAdjNotVRLM` is withdrawn.
- **Monotonicity at `binder0`.**
  - The record half is proved (`monoExtM0`).
  - The own push is proved at contexts reaching no `U` (`monoOwnGUFreeMA`). It needs one added
    hypothesis, `StackPayAvoids`: the pushed variable is free in none of the entries' payload
    types. Every `SemSM` index gives it for a variable new to `Δ` and to the stack
    (`stackPayAvoids_of_stackJ`). `MonoOwnUFreeME` and `MonoOwnGUFreeM` as stated lack it and are
    not derived.
  - **The unrestricted `MonoOwnGM`, `MonoGM` and `MonoVM` are refuted** at the configuration `gd`
    (`notMonoOwnGM0`, `notMonoGM0`, `notMonoVM0`).
    - In `gd` the closure `λg. return g` at `U(U(F 1) ⊸ F([@'1] U(F 1)))` is a value at the stack
      because the guard boxes every argument above `'1`.
    - After the own lend's push, an argument holding the pushed view is returned boxed at `'1`,
      and no run meets that (`gdNotPushed`).
    - Its closure is no Core value (`gdNotCore`), and its index fails the record invariant
      (`gdNotRecsInsideOwn`). Whether `gd` arises was not attempted.
- **The `∀I` row, the lemma's only consumer.**
  - Proved at every context whose live slots reach no `U`, at every index whose stack does not
    name the binder (`allIRowMNKUFree0`).
  - Carrying the premise to its two places shows that the row reads three transports of its
    context: across the push, to the reading extended at the binder, and to the pushed variable's
    reading (`allIRowMNKAt0_of`). All three hold at contexts reaching no `U`
    (`vRLM_reading_uFree`).
  - At `gd`, a `U` slot, the row's conclusion holds at a derivable body that hands `gdF` a thunk
    holding the argument and forces what comes back (`gdMtDerivable`, `gdAllIHoldsAtMt`), the
    pushed stack included. `gdM` itself applies `f` to a thunk literal, which the rules do not
    take [unchecked].
  - Not derived: the row at a live `U` slot; and at an index whose innermost entry is named by the
    binder, where `SubOutside` at the extended reading is not given (`not_subOutsideExtendAny`).
    The second has since been proved at contexts reaching no `U` (`allIRowMUFree0`).
  - The restricted route (each live slot also a Core value) excludes `gd` (`gdCtxNotCore`). It is
    met at `gd`'s index with a `U` slot (`gdRestrictedMet`) and proved at contexts reaching no `U`
    (`monoOwnGMCUFreeA`). Its step at a `U` slot was not attempted in Lean.
- **The three obligations.**
  - `OuterBelowTop`: proved at every lend and at the arising set (`outerBelowTopArises`).
  - `RetainedPay`:
    - proved at the lend's view, the transports and `∀E` at an instance with no join;
    - at a `Mut` read-out, proved at a retained view. At a bound view it reduces to
      `EntryPayLeaves` (the entry's payload type's leaves), the expected stop
      (`retainedPayLoadMutRowNJ_of_entry`);
    - `withload` at a payload with two `Mut` or `Ref` leaves side by side (`Ref 1 ⊗ Ref 1`) is
      outside the guard. Its reborrow makes their cells `imm` cells exactly at the own lend's
      lifetime, at places no entry of the old stack lends. The pushed entry lends at most one, and
      the table excludes the other (`loadGuardFails2`). So, like the slice rows, it is not covered at
      W [unchecked: the argument holds the two cells at the top, and the callback's guard reads
      them with the closure's resource]. The `Imm` read-out at the payloads the guard admits was
      not attempted. Since then, the unchecked step is proved at an arising configuration at
      `withloadU`'s type, on [TR] 6.175's route (`withloadUPairGapReal`); no `withloadU` row is
      refuted. Under the corrections of 2026-10-08 it is treated as a defect of the draft, not a
      restriction; that its cause is the single-place stack entry is [read]. The designed fix is a
      block (`NEXT.md` §1.6), which is not built;
    - the slice rows at two or more elements: their family fails the guard at every single push
      (`sliceGuardFails`); no slice configuration is shown to arise (`SliceUGapReal` is not
      built).
  - `KeepsT` at the share: proved from `LineageUnique` (`shareKeepsT_of`), which is not derived,
    and `FramesKept`, which statement 2 supplies.
- **Statement 0 at `binder0`.**
  - Every fact beside monotonicity is proved (`statement0MBesideMono0`): the shared lemmas at the
    revised futures, `[force]`, the callbacks at `σ·y`, and the `U` side.
  - `statement0MAtConsumers0_iff` holds by the definition of our own conjunction. That `AllIRowM`
    and `MonoExtM` are all of statement 0's consumers is [unchecked]: `MonoHide` at `vRLM` was not
    stated, and the inventory (`NEXT.md` §4.2) was not written. The row is proved where its
    context reaches no `U`.
  - The bundle as stated is refuted with the unrestricted monotonicity statements
    (`not_statement0M_binder0`). That is not `binder0`'s status.
- **What it decides.**
  - R1 is closed at `binder0`.
  - What statement 0 there reduces to is not established, because its consumers were not
    inventoried.
  - On [TR] 6.175's route, the guard and the stack entry do not cover `withload` at a payload
    with two references side by side (`loadGuardFails2`; at an arising configuration at
    `withloadU`'s type, `withloadUPairGapReal`). That the cause is the single-place entry is
    [read]. Under the corrections of 2026-10-08 it is treated as a defect of the draft, to fix
    (item 1b). The slice rows' family fails the guard at every single push (`sliceGuardFails`),
    but no slice configuration is shown to arise (`SliceUGapReal` is not built).
  - OQ-8 is not decided: no refutation passed DESIGN §11, and `cbpv` and `binder` were not redone
    at `vRLM`.
  - No failure of type (a), (b) or (d) occurred, and the fallback is not triggered.

## The guard gap, `VRLMUnroll`, the `∀I` row, `MonoHide`, and the floor (`NEXT.md`): the outcome

`NEXT.md` takes four items at `binder0`:
- the two-cell guard gap the R1 unit left unchecked;
- `VRLMUnroll`;
- the `∀I` row's two open cases;
- `MonoHide` at `vRLM`, and the consumers check.

The user's corrections of 2026-10-08 (`NEXT.md` §10) added a floor:
- borrow-only programs are proved in Core, and the draft must reproduce them;
- a gap on a borrow-only program is a defect of the draft, not a restriction or a cost;
- persistent resource-free values must be monotone by construction;
- test programs are written as the language writes them.

`NEXT.md` §9 is the outcome in full, §10 the corrections, and *Unresolved* the four review findings
still open. Statements are in `ProbeD1/Nx.lean`. The proofs are in `NxGuard.lean`,
`NxGuardPair.lean`, `NxUnroll.lean`, `NxE1.lean`, `NxAllI.lean`, `NxHide.lean`, `R1Box.lean`,
`NxFloor.lean` and `NxRecon.lean`. Nothing outside ProbeD1 changed.

The draft relation changed twice:
- (E1)–(E4) (`NEXT.md` §3.1):
  - (E1): the `∀` clause's first conjunct reads only instances in scope;
  - (E2): its own lend is at `OwnPushM`;
  - (E3): `SemSM` reads `StackJM`;
  - (E4): the callback statements take `¬ VFree y T`.
- The persistence box. `vRLM`'s `!` clause reads a persistent thunk at every instantiation of
  the stack, every list kept outside, and every finite sequence of own pushes at the empty
  resource under reserved names (`NsVar`). The pushes are a new reach of the `!` clause: no
  `binder0` clause pushes under a reserved name.

The statement changes are listed in `NEXT.md` §9.

- **The two-cell gap is real at `withloadU`, on [TR] 6.175's route** (`withloadUPairGapReal`).
  - The configuration arises: three allocations and a 6.64 lend. Its view arises, and the
    judgement's index holds there.
  - The program is typed at `withloadU`'s type. [TR] 6.150's `TW.reb` reborrows the payload at
    an own push's lifetime into a tagged typed world.
  - At every reading `CbReading` lists (each instantiation of the stack, then each instance
    below the bound or each single own push), the pair reborrowed at the reading's own
    lifetime fails the guard. No `withloadU` row is refuted: another argument might meet the
    table at a non-identity instantiation (`PairArgCellsLe`, not built). The non-vacuity push
    `pEn` lends place 3 at type `1`, unrelated to the payload.
  - At `withload`'s own thunked type, the statement is refuted at the same configuration
    (`not_withloadPairGapInst`). The answer's `U` clause moves the lend below the cells, where
    they meet the table.
  - After (E1) the route fails at the empty stack too (`withloadUPairGapNilE1`), but at a view
    not shown to arise (no `ArisesVI` witness). That is not evidence of a defect, and not a
    trigger to revisit (E1). `pairNilOldGuardHolds` says only that the table at `[]` holds of
    every resource.
  - Under the corrections this is treated as a defect of the draft on a borrow-only program,
    not a restriction. That its cause is the single-place stack entry is [read], not a theorem.
    The designed fix is item 1b's block, which is not built. The slice gate is not built either.
- **`VRLMUnroll` is proved** (`vRLMUnroll`), with `vRLM`'s substitution lemma and the roll and
  unroll rows at every placement.
- **The `∀I` row.**
  - It is proved at every context whose live slots reach no `U`, at every index, the binder-named
    index included (`allIRowMUFree0`).
  - At a live `U` slot it is not derived. The planned route to the reading transports does not pass
    the `F_Σ` clause (`not_readEquivRelend`, a fact about our `ReadEquiv`). The push's steps at a
    `U` slot were not attempted.
- **`MonoHide`.**
  - Proved where the hidden names cross no entry (`monoHideGMHandle0_noCross`,
    `allRHideM0_noCross`).
  - Statement 4's `AllRMonoM0`: its record-order half is proved (`allRExtM0`), and its thaw half at
    the empty resource (`allRThawM0Empty`). The rest is not derived.
  - The consumers inventory was not written, so no claim is made about what statement 0 at
    `binder0` reduces to.
- **The floor.**
  - Before the box, `vRLM`'s `!` clause did not carry persistent values across a push by
    construction, with or without (E1). At `vRLJ`, a persistent closure at a type with no
    lifetime `∀` is related at a stack and not after the own lend's push (`gdBangJ`). That is
    at `gd`, which is not shown to arise, and `gdF` is no Core value, so it is not evidence of a
    defect on a borrow-only program.
  - (E1) was kept, and the `!` clause gained the persistence box. The clause is not fixed. The
    box carries a persistent thunk across instantiations and own pushes at the empty resource
    under reserved names (`NsVar`) only (`persistentPushN`, `monoOwnGMAtBoxN`). The two `!U`
    rows are re-proved at it (`statement0UFullM`).
  - Two pushes are outside the box: the push `gdBangJ` fails at (`gdY`, named `2`, no reserved
    name), and the `∀` clause's own push, named by the type's binder (`OwnPushI`, `e.x = x`).
    The second is correction (i)'s case, a lifetime-polymorphic `!U` combinator carried into a
    lend's callback. Both wait on `VRLMStackRename` (stated, not derived) and a reduction that
    is not built. No `binder0` clause makes a reserved-name push, so the carrying proved may
    have no consumer yet. The user's example was not built, so it is unchecked that `withload`
    of a pair is the only borrow-only program (E1) affects.
  - Open:
    - the `∀I` row's binder-named push at a persistent context (`VRLMStackRename` and the
      reduction);
    - the reading transports at a `!U` slot;
    - a persistent slot reaching `U` below its top;
    - linear closures across a push;
    - the floor's own statement at `σ = []` (OQ-58's statements, not attempted).
- **`reconB′`, as the language writes it** (`reconB'`).
  - `retry` is a handler installed around the lend, and the callback performs `wait`. It runs to
    `(tt, ff)` with no cell left (`reconB'_eval`).
  - Its callback is closed [read]. `reconCb_allI` is `allIRowMUFree0 []` under a
    program-specific name. The typing is not built.
  - What it owes beyond that row is [unchecked]. Its lend is `lendCell`, whose term is
    `withborUE dFlag`, which only the unwinding rules type, and those do not admit `wait`. Which
    typing rule and which callback row apply (`CallbackExtImmM` at the `.arr` shape, or the
    thunked `CallbackExtImmMF`, stated and not proved, a borrow-level obligation and not tier 2)
    is open. The suspension inside the lend (tier 2) is among what it owes.
- **What it decides.**
  - OQ-8 is not decided. The gate's gap is on [TR] 6.175's route; that it lies in the stack
    entry and the guard, which the placements share, is [read]. No refutation of a placement's
    statement passed DESIGN §11, and `cbpv` and `binder` were not redone at `vRLM`.
  - No failure of type (a) or (b) occurred.
  - (d), reported against both of DESIGN §12.2's readings:
    - **The design's reading** (was a clause changed to reach a stack other than its own by
      something other than `FutQ`?). Yes: `vRLM`'s `!` clause gained the persistence box. It
      reads a persistent thunk at every instantiation of the stack and at own pushes at the
      empty resource under reserved names (`NsVar`), not through `FutQ`. The reserved-name
      pushes are a new reach of the clause, beyond `FutQ` and beyond the type it reads.
      Statement 0 is not established at `binder0` (it does not yet hold), with the box or
      without it. The bundle as stated is refuted with the unrestricted monotonicity
      statements at `gd`, which is not shown to arise and is not `binder0`'s status
      (`not_statement0M_binder0`, `monoUnrestrictedRefuted0`). The consumer form waits on the
      `∀I` row (`Statement0MAtConsumers0`, `AllIRowM .binder0`). So (d) has not occurred. If
      statement 0 comes to hold only with the box, (d) under this reading applies.
    - **The synthesis's wording** (was `OwnPush` at `U` needed, and how did `MonoOwnG` come
      out?). `binder0` has no own push at `U` (`uOwn .binder0 = false`); its own push is the
      `∀` clause's. `MonoOwnG` at that push is not derived. Unrestricted
      (`MonoOwnGM .binder0`) it is refuted at `gd`, not shown to arise
      (`monoUnrestrictedRefuted0`). Its restrictions are proved at contexts whose live slots
      reach no `U` (`monoOwnGUFreeMA`, which `allIRowMUFree0` reads) and, at persistent
      contexts, across pushes under reserved names (`monoOwnGMAtBoxN`). It is not derived at a
      live `U` slot, nor at the binder-named push at a persistent context (`VRLMStackRename`,
      stated). No push was made a future: `binder0` reads none.
  - The fallback is not triggered.

## Grounding, the regression suite and the block (`GROUND.md`): the outcome

`GROUND.md` plans four parts. `LEDGER.md` holds the ledger, the suite's results (§10) and the
block's outcome (§11).
- **(0) The doc fixes** the guard-gap unit's content review asked for: made (`2d6b0ae`).
- **(1) The grounding ledger** (`LEDGER.md` §1–§9, `GroundLedger.lean`). Every draft definition
  with a Core counterpart is set against it, and "agrees" is written only where a named theorem
  proves it. The draft relation is Core's at flat types at every stack (G1), inside Core's at
  first-order arguments (G2), and Core's at `NilTy` at the empty stack (G3). At a first-order
  judgement Core's derivation gives the draft's judgement at every index (G5), and at the empty
  stack at `NilComp` judgements, constants included (G5′).
- **(2) The regression suite** (`LEDGER.md` §10, `GroundRegress.lean`). Each borrow-only
  program's obligation is `DraftFL` at every node of its derivation, at every index. Each entry is
  PROVED, NOT BUILT with its missing lemma, or FAILS with an arising configuration. No entry is
  FAILS. The roots, the first-order callbacks and the constants Core derives at first-order types
  are PROVED. The borrow constants' rows, the glue at `U` slots and the persistent slot across the
  binder-named push are NOT BUILT. No program is claimed to meet the floor.
- **(3) The block** (`LEDGER.md` §11). It is built in place, beside the single push: `cRLM`'s `∀`
  clause reads a block of two or more entries at one lifetime at a callback whose argument fits
  them (`OwnPushB`, `BlockFits`, `CbArg`, `Block.lean`), and `SemSM`, `SemSMC`, `SemIdxM` admit
  stacks holding blocks. The gate is proved, and so are the block gates at the pair and at an
  array of `I32`, at the empty stack, both shapes (`loadGateNilB_pairTy`,
  `loadGateNilB_arrayI32`), with `FreePlaceExists` (`freePlaceExists`). Every row is re-proved,
  and every theorem proved before is proved after. The statements whose text changed are listed
  with their reasons (§11.4). Among them is `forceRowM`, now at `binder0` only: at `cbpv` and
  `binder` the `U` clause reads `ReLend`'s reflexive re-lend, which a block stack's chain is not. This meets the
  stop rule's general clause at placements that are not the draft's, and the fallback was not
  applied (§11.3).
- **The rows at the empty stack** (§11.5). `Withbor1NilRowM`, `WithloadNilRowM` and
  `WithloadUNilRowM` are attempted and none closes. `withbor` (1) stops at the payload in 6.64's
  frame (`NilPayloadCore`), and at a flat payload next at the own push's `placeFree`
  (`ImmFramePlaceFree`). Both `withload` rows stop at (l3): the block gate reads the reborrow's
  structure and the callback's freedom at the reborrowed places, which [TR] 6.150's rule does not
  hand its continuation (`LoadGateNilBI`). None of these is derived, and no obstruction is
  verified.
- **So the pair and slice entries read**: the gates PROVED; K2 and K2′ at the empty stack NOT BUILT
  at (l3); at every index NOT BUILT.
- **D12**, the block's divergence at a stop, reaches no program of Core or of the suite. It owes
  two obligations before a program with a stop at a stack holding a block is claimed (§11.7).

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
| `GAP.md` | the design for `TyEqInst` at every type and the position-`∀`: the diagnosis, the threshold cover, the two readings of the position-`∀`, the agreement with Core at `σ = []`, R1, the literature; §8 the build's outcome |
| `ProbeD1/Gap.lean` | that design's definitions and `def … : Prop` statements; no proofs |
| `ProbeD1/GapWitness.lean` | `coreAllAdjacent`, `coreAllNotNatural`, `not_coreAllImpCutAll`: Core's `∀` reads the room between lifetimes |
| `ProbeD1/GapCover.lean` | the threshold cover: `interpCollapse`, `eqOfCollapse`, `tyEqOfCover`, `coverInst`, `coverGap`, `tyEqInst`, `tyEqGapStep`, `tyEqRoomBlind` |
| `ProbeD1/GapRows.lean` | the leaves and rows at every payload type: `cohEInstOB`, `viewSlotInstOB`, `relendJValueK`, `ctxRelendsThawFreeKJ`, `statement0UThawFreeKJ` |
| `ProbeD1/GapPos.lean` | the position-`∀`: `instRealisesCut`, `allPosJNil`, `allPosJSelf`, `allPosJTransport`, `cutAllNilSound` |
| `ProbeD1/GapRoom.lean` | W's `U` clause as reading (B): `wU_allPosJ`, `adj_core_U`, `adj_not_wU` |
| `R1MONO.md` | the design of R1 and `binder0`'s monotonicity: `vRLM` (W reading `μ`, `fam` and type variables), the monotonicity statements and the configuration `gd`, the consumer and the restricted route, `RetainedPay` row by row, `KeepsT` at the share, statement 0 at `vRLM`; §8 the build's outcome; *Unresolved* the second review's major finding after the build |
| `ProbeD1/R1.lean` | that design's definitions and `def … : Prop` statements; no proofs |
| `ProbeD1/R1Thaw.lean` | R1: `relMAgreesJ` (restated, see `NEXT.md` §9), `vRLMMonoAt`, `vRLMRoll`, `relendMValueE`, `ctxRelendsAllM`, `thawInstM`, `thunkFRowM`, `thunkVRowM`; the persistence box's local facts (`pBox_mono`, `pBox_inst`, `pBox_env`). The two `!U` rows and `statement0UFullM` are in `R1Box.lean`; `muAdjNotVRLM` (proved at `5210cf1`) is withdrawn |
| `ProbeD1/R1Mono.lean` | monotonicity: `monoExtM0`, `monoOwnUFreeMEA`, `monoOwnGUFreeMA` (`StackPayAvoids`), `futPartI`, the instance lemmas, the configuration `gd` (`gdIndex`, `gdRelated`, `gdNotPushed`, `notMonoOwnGM0`, `notMonoGM0`, `notMonoVM0`, `gdNotCore`, `gdNotRecsInsideOwn`, `gdIdxNotArisesOf`, `gdRowRefutation`), the restricted route (`gdCtxNotCore`, `gdRestrictedMet`, `monoOwnGMCUFreeA`) |
| `ProbeD1/R1Owed.lean` | the three obligations: `outerBelowTopArises`; `RetainedPay` by row (`retainedPayViewRow`, the transports, `retainedPayInstRow`, `payLeavesOfTyEq`, `retainedPayLoadMutBound`, `retainedPayLoadMutRowNJ_of_entry`, `sliceGuardFails`, `loadGuardFails`, `loadGuardFails2`, `rebGuardFails`, `thawLeafP`); `KeepsT` at the share (`relAboveOfTagged`, `extKeepsTInst`, `shareKeepsT_of` and its chain from `LineageUnique`) |
| `ProbeD1/R1Stmt0.lean` | statement 0 at `vRLM`: `vRLMDataE`, `nilSoundRetM`, `statement0SharedM`, `forceRowM` (at `binder0`), the callbacks, `statement0MBesideMono0`, `not_statement0M_binder0`, `statement0MAtConsumers0_iff` |
| `ProbeD1/R1AllI.lean` | the `∀I` row at `binder0`: `allIRowMNKAt0_of` (one context, five transports, the block conjunct among them), `vRLM_reading_uFree`, the transports at contexts reaching no `U`, `allIRowMNKUFree0`, `allIRowMNKNil0`, `cRLM_step`, `not_subOutsideExtendAny`; the test at `gd` (`gdMtDerivable`, `gdAllIHoldsAtMt`) |
| `NEXT.md` | the design of the guard-gap unit: the two-cell gap and its arising check, `VRLMUnroll`, the edits (E1)–(E4) and the `∀I` row's open cases, `MonoHide` and the consumers, the block; §9 the build's outcome; §10 the corrections of 2026-10-08 (the floor, the persistence box, `reconB′`); *Unresolved* four review findings |
| `ProbeD1/Nx.lean` | that design's definitions and `def … : Prop` statements; no proofs |
| `ProbeD1/NxGuard.lean` | the guard lemmas: `pairRebCells`, `pairCallbackGuardFails`, `pairCallbackGuardFailsLe`, `sliceCallbackGuardFails`, `pairBoundBelow`, `pairNilOldGuardHolds` |
| `ProbeD1/NxGuardPair.lean` | the pair configuration in the typed world and `ArisesI` (`pc_arises`, `pairCfg`), the program at `withloadU` and `withload` (`pairWithloadUTyped`, `pairWithloadTyped`), `TW.reb` at an own push's lifetime, link (d) (`pairGuardRejectsU_of`, `sliceGuardRejectsU_of`), the gate `withloadUPairGapReal`, `not_withloadPairGapInst` |
| `ProbeD1/NxUnroll.lean` | `vRLMSome`, `vRLMRename`, `vRLMSubst`, `vRLMInst`, `vRLMUnroll`, `rollRowM`, `unrollRowM` |
| `ProbeD1/NxE1.lean` | `muAdjVRLME1`; the gate after the edits (`pairGate_afterEdits`); item 1a′ (`withloadUPairGapNilE1`, `not_withloadPairGapNilInstE1`) |
| `ProbeD1/NxAllI.lean` | the binder-named index, a block at the head (`subOutsideExtendNamedB`, `stackJBase_allNamed`, `allIRowMAt0_of`, `ctxExtendNamedMBAt_uFree`), `allIRowMUFree0`; `not_readEquivRelend` |
| `ProbeD1/NxHide.lean` | `hideInvisible`, `monoHideGMHandle0_noCross`, `allRHideM0_noCross`, `allRExtM0`, `relendJInter_empty`, `allRThawM0Empty` |
| `ProbeD1/R1Box.lean` | the persistence box: the index facts along it (`BoxIdx`, `boxIdx_inst`, `boxIdx_steps`, `stackJ_of_boxIdx`), its transitivity (`boxSteps_inst`, `pBox_worldB`), a persistent context at every box world (`gRLM_boxWorld`), the two `!U` rows at the box (`bangThunkFRowM`, `bangThunkVRowM`, `statement0UFullM`) |
| `ProbeD1/NxFloor.lean` | the floor: `inScope_top_none`, `gdBangJ`, `persistentBoxWorld`, `persistentPushN`, `monoOwnGMAtBoxN`; `VRLMStackRename` (stated) |
| `ProbeD1/NxRecon.lean` | `reconB′` as the language writes it (`reconB'`, `reconB'_eval`), `reconCb_allI` |
| `GROUND.md` | the design of the grounding unit: the doc fixes, the ledger, the regression suite, the block; §8 the review findings not edited in, and what part (3) left open |
| `LEDGER.md` | the grounding ledger (§1–§9), the regression suite's results (§10), the block's outcome (§11) |
| `ProbeD1/GroundLedger.lean` | the grounding theorems G1–G12 (`vRLMFlat`, `vRLMFOArg`, `coreToSemSM`, `coreToSemSMConst`, `coreToSemSMNil`, `adequacyNilM`, …), the empty-stack unfoldings, and the rows of `fundamentalC` as statements |
| `ProbeD1/GroundRegress.lean` | the producer lemmas, the gate at `1` (`loadGateNil_unit_of`), the seeds (`pairLoad`, `pairLoadU`, `bangUse`), P56 by the checker route, and the suite's entries |
| `ProbeD1/Block.lean` | the block's definitions: `blockL`, `StackOKB`, `BlockFits`, `CbArg`, `OwnOKB`, `OwnPushB`, `StackJBase`, `StackJB` |
| `ProbeD1/R1Block.lean` | the block's shape facts (`stackOKB_of_ok`, `instStackOKB`, `stackJBaseIff`), `StackJBase` along the rows, and the guard at an instantiated block stack (`guardInstB`) |
| `ProbeD1/R1MonoB.lean` | a context reaching no `U` across a block push (`monoOwnGUFreeMB`) and across a single push onto a stack with blocks (`monoOwnGUFreeMA_len`) |
| `ProbeD1/GroundBlock.lean` | the block's gate (`blockFitsLeafLe`, `blockFitsReb`, `pvlStartB`, `pairGuardHoldsB`, `loadGateNilB_pairTy`, `loadGateNilB_arrayI32`), `freePlaceExists`, and the rows attempted at the empty stack with their missing steps (`NilPayloadCore`, `ImmFramePlaceFree`, `LoadGateNilBI`) |
