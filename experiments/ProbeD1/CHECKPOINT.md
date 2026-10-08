# ProbeD1: checkpoint

This is a plain-language summary of where the D1 tractability probe stands. The full outcome is in
`README.md` and `DESIGN.md` §15. The Lean is in `ProbeD1/`, and `lake build ProbeD1` builds it.

> [!NOTE]
> **All verifiers passed on the gap unit (`GAP.md`).** The hygiene review checked every declaration
> in the six `Gap*` files: none uses `sorry` or a forbidden keyword, and every axiom set is within
> `[propext, Classical.choice, Quot.sound]`. The content review passed with three minor wording
> findings, each addressed:
> - "W's `U` clause *is* the position-`∀`" overstated `wU_allPosJ`, which proves one direction only.
>   README, DESIGN §15.8, GAP.md §0, §1.4, §3.4 and §8 now say W's `U` clause *implies* the
>   position-`∀` for its body at a `U (∀…)` type. W's clause is strictly stronger, because `RelendJ`
>   also quantifies over record extensions. The same claim for a `∀` nested deeper is marked
>   [unchecked].
> - GAP.md §0's sentence placing OQ-58 in outcome (c) is now conditional. It holds only if reading
>   (A) were adopted, and only subject to §3b's [unchecked] identification of W's `∀` at `σ = []`
>   with `CutAllC`.
> - `InstRealisesCut`'s docstring now says the proof does not use the no-lifetime-between hypothesis,
>   and that nothing ties `L` to the lifetimes an index reads.
>
> The freeze-binder unit's verifiers also all passed, and its findings were addressed. The
> statement-0 unit's minor wording findings are still open: the "only with" claim in DESIGN §2.2, the
> unmarked prose reasons in DESIGN §15.2 and the README, `MonoHide binder0`'s status, and the
> README's "no way to reach a stack" sentence. They are listed under option 1 below.
>
> The R1 unit (`R1MONO.md` §8) has been through the verifiers. One passed, and one did not; see
> the warning below.

> [!WARNING]
> **The R1 unit's content review did not pass. It raised two major findings.** They are now
> corrected in README, DESIGN §15.9 and `R1MONO.md` §8, with the guard-gap unit's results
> (`NEXT.md` §9).
> - **Major: "statement 0 at `binder0` is exactly its `∀I` row" overclaims.**
>   `statement0MAtConsumers0_iff` holds by definition. `Statement0MAtConsumers0` is our own
>   conjunction `BesideMono0 ∧ MonoExtM ∧ AllIRowM`, and its first two conjuncts are proved. The
>   claim actually rests on `AllIRowM` and `MonoExtM` being *all* the consumers of `MonoOwnGM`,
>   `MonoVM` and `MonoGM` at `binder0`, and `R1MONO.md` §4.1 marks that [unchecked]. Also, the
>   handler's `MonoHide` at `vRLM` is not stated. The handler row's context transport came from
>   `MonoHide` through `MonoHideFromMonoV`, so from `MonoV`, and unrestricted `MonoVM .binder0` is
>   refuted here. `MonoHide` at `vRLM .binder0` is now on the tier-2 list below.
> - **Major: the `withload` gap was stated without its condition.** `loadGuardFails2` is a proved
>   fact about the guard: a resource with two shared cells at exactly the new lend's lifetime, at
>   distinct places the old stack does not lend, meets the guard at no pushed stack. Whether
>   `withload`'s reborrowed argument at `Ref 1 ⊗ Ref 1` has that shape at the callback's guard is
>   [unchecked], and no such configuration is shown to arise. I have not verified that any
>   obstruction is real. No change to the draft definitions should follow until that step is
>   proved in Lean, ideally at an `ArisesI` configuration.
> - Minor: R1 was closed by changing the draft relation at `μ`. `vRLM` reads `μ` itself and is
>   strictly smaller than Core's relation there (`muAdjNotVRLM`). The unroll row at `vRLM`
>   therefore owes `vRLM`'s substitution lemma (`VRLMUnroll`, `vCE_subst`'s analog), which was not
>   attempted. It is now on the tier-2 list.
> - Minor: `retainedPayInstRow` also assumes that no stack entry is named by the instantiated
>   variable (`x ∉ σ.map LEnt.x`), besides "no join".
> - Minor (from the review that passed): `OuterBelowTop` across the arising set comes from [TR]
>   6.64/6.65 H4's consequence, `∀ α ∈ c'.αs.head?, α < ⊤`. That consequence is now recorded as a
>   field of the draft arising-set definitions `LendMutI` and `LendImmI` (`Binder.lean`). This is
>   the unit's only edit to an existing Lean file's definitions. It is disclosed in `R1MONO.md`, but
>   the builder's summary left it out.
>
> - Since (`NEXT.md` §9):
>   - The `withload` step is proved at an arising configuration at `withloadU`'s type
>     (`withloadUPairGapReal`). Under the user's corrections of 2026-10-08 it is a defect of the
>     draft's stack entry.
>   - `VRLMUnroll` is proved.
>   - `MonoHide` at `vRLM` is stated, and proved where the hidden names cross no lend.
>   - `muAdjNotVRLM` (proved at `5210cf1`) is withdrawn after (E1).
>
> The hygiene review passed: no `sorry` or forbidden keyword, and every axiom set is within
> `[propext, Classical.choice, Quot.sound]`.

> [!NOTE]
> **The guard-gap unit (`NEXT.md`) has not been through the verifiers.** Four major findings of
> its design reviews were answered in the text and not reviewed again (`NEXT.md`, *Unresolved*).

## The question

D1 is the design built on rows and ghost end. At a stop, the lend is re-lent at a fresh lifetime
each time the computation resumes. The question is whether the fundamental lemma can be proved at
D1's world W under four conditions:
- it covers exactly the rules that the two test programs (`genSelf` and `reconB′`) use;
- it uses one world, with the arising guard read from `TW`;
- the quantifier over future worlds appears once;
- there is no second relation family beside W.

Statement 0 comes first. It defines W's clauses at `U` (thunks), `⊸` (functions) and `∀` together.
It tries the future-world quantifier at three places:
- `cbpv`: at `U` and the stop's share (OQ-8 option 2);
- `binder`: at `U`, the share, `⊸` and `∀` (option 3);
- `binder0`: at `∀` only, as in GhostEnd.

Its outcome was meant to settle OQ-8 (where the quantifier goes). With that, it would settle whether
D1 meets "two algebras that interact only at cuts".

## Statement 0: what happened

**`Statement0 p` was not proved at any of the three placements. No fact of statement 0 was refuted.**

- **Proved at every placement:** the shared lemmas (`statement0Shared`), `ForceRow`, `ThawRelend`,
  `MonoHideFromMonoV`.
- **Proved at `cbpv` and `binder`:**
  - monotonicity along W's order (`MonoV`, `MonoG`, `MonoHide`);
  - carrying a context across the callback's own lend (`MonoOwnG`).

  `MonoOwnG` needed one change that the design had planned for (§13 step 2): `FutStep` now accepts
  any variable new to the stack. The design named the cost of this change in advance.
- **Callback at `σ·y`:** proved at `binder` and `binder0`. At `cbpv`, proved only when the bound
  does not mention the binder.
- **Not derived at `binder0`:** monotonicity (`MonoOwnG`, `MonoV`, `MonoG`). The design expected
  this placement to stop here.
- **Not derived anywhere:** the four `U` introductions (`ThunkFRow`, `ThunkVRow`, `BangThunkFRow`,
  `BangThunkVRow`). Two needs are common to every placement:
  - **the context's thaw** (`CtxRelendableAt`): fails at a configuration W's own clauses reach
    (see the follow-up questions);
  - **Δ's models at a re-lend** (`ReLendModels`): fails at a configuration typing reaches (see the
    follow-up questions).

  `cbpv` and `binder` have further needs of their own. One is the context carried to a future that
  inserts between lenders. The other is the names `StackJ` admits after the `FutStep` change.
- **At `binder0`**, the four `U` rows are proved given `CtxRelendableAt` at the row's own context,
  at the configurations whose re-lends keep Δ's models. Statement 1's `TabRelend` was proved on the
  way.

## The two follow-up questions (`Relendability.lean`, DESIGN §15.6)

**Q1. Can the context always be re-lent?** No, not as `SemS` stands.
- The configuration `k`: a lend of place `0` whose entry says the payload type is `Unk`, while the
  context holds `r : Mut '0 1` pointing at place `0` with a cell that stores `1`.
- The table allows it, `SemS`'s index allows it, and no split puts the cell anywhere, so the context
  cannot be re-lent there (`not_ctxRelendable_binder0`, `not_ctxRelendableAt_k`, `k_index`).
- Its world arises in `TW` (`k_world_TW`). Its stack and context are reached by binder0's own `∀`
  and `⊸` clauses, starting from a closed typed program (`k_reached`). There the `U` clause fails
  for every closure (`k_thunk_not_vRL`).
- It is still not an obstruction. No row is refuted: whether the program's own clause fails, once
  `wpTS` may update the answer's resource, is not derived.
- **What keeps `k` out of a real run** is the lend's step, not `TW`. A lend opens with the cell at
  its place equal to the entry's view (`lendMut_placeView`), and `↭` keeps that cell's predicate.
  `PlaceViews` names this, and `k` breaks it (`not_placeViews_k`). W's guard (`TabAtS`) and its own
  lend (`OwnOK`) do not carry it. That `PlaceViews` holds at every arising configuration is not
  proved.

**Q2. Do Δ's models survive a re-lend?** Not always, and typing reaches the failing case.
- The rows need `ReLendModels`: every re-lend of the stack models Δ.
- `BoundsStackFree` (no bound of Δ mentions a stack variable) is enough
  (`reLendModels_of_boundsStackFree`).
- The program `Λ'0. Λ'1 ⊏ '0. thunk (return ())` is typed closed. Read by binder0's own clauses, its
  thunk is introduced at an index where `'1 ⊏ '0` holds and a re-lend of `'0` breaks it
  (`q2_reached`). So `ReLendModels` fails at a configuration typing reaches.
- This is a real obligation. The re-lend has to keep those bounds: either it also lowers the
  variables bounded by stack variables, or the `U` clause only quantifies over re-lends that keep
  them. Neither is built.

**What it decides:**
- **OQ-8: not decided.** No placement got through statement 0, and none was refuted. The design's
  rule draws no conclusion from "not derived".
- **"Interactions only at cuts": not decided.** D1's rank against D2a and D3 is where it was before
  the probe.
- **No failure of type (b) or (d) occurred.** No second guard, no second relation family, and no
  second quantifier.

## Statements 1–4

Not attempted. The design's stop rule halts the probe after statement 0 when `Statement0 p` is
proved at no placement. The one exception is statement 1's `TabRelend`, proved on the way at
binder0. Statements 5–7 and OQ-58's facts were not attempted either, and `reconB′` was not built.

## What this says about D1's tractability

The probe still leaves it open. Most of the value-side cost of the quantifier is proved at `cbpv`
and `binder`: monotonicity at `U`, the own lend, the thaw and `[force]`. The open part is the `U`
introductions, and the two follow-up questions locate both of their shared needs:
- **The thaw** fails at a configuration W's guard admits and W's own clauses reach. What excludes
  it in a real run (`PlaceViews`) is missing from W's guard and own lend. This is a fix to our
  definitions, not evidence against D1.
- **The models** fail at a configuration typing reaches. D1's ghost-end route therefore needs its
  re-lend to keep the bounds of variables bounded by a lend variable. [unchecked] A resume re-lends
  at a fresh lifetime, below everything, so restricting the re-lends would exclude the resumes D1
  needs; lowering the bounded variables along with the stack is the likelier route.

No row is refuted and no fallback is triggered. Nothing here is evidence that D1 cannot be made to
work, and nothing is evidence that it can.

## The freeze-binder unit (`BINDER.md`)

This unit took both of statement 0's shared needs and treated the stop as a binder. A place the
stack lends is bound, and a borrow cell there is that binder's view (PlaceViews). A resume
instantiates every lifetime the frozen computation made, keeping their order. The design is
`BINDER.md`, and its §11 has the outcome in full. A refutation below is a fact about one of our
statements: none is at a configuration shown to arise, so none is an obstruction.

**What was proved.**
- **PlaceViews holds at every configuration of the revised arising set** (`pvArises`). So `k` is not
  in that set (`kNotInArises`). This does not show that `k` never arises, because the set is not
  known to cover everything that arises.
- **The guard's views are kept by the steps `binder0` reads**: a part, a lend's start and end, a
  handler, the resume, an instantiation, and `↭` and a run when the stack's places are distinct.
  Every stack the arising set reaches has distinct places. The step to a future (`PVLFut`) was not
  attempted; `binder0` does not read it.
- **The re-lend as an instantiation keeps `Δ`'s models with no condition on `Δ`.** This settles Q2.
- **At the revised relation, the four `U` introductions are proved at `binder0`.** The proof also
  covers the context's thaw at every context without `μ` or `fam` slots, and the rule that an
  instantiated `U` value is a `U` value. The rows no longer need a hypothesis about the re-lend's
  models.
- **Whether `mut_not_natural`'s witness arises is still undetermined.** It is part of a `TW` world,
  but `TW` accepts any stored predicate, so that tells nothing. The check at the arising set
  (`InternalPayloadArises`) was not attempted. At a view slot the instantiation rebuilds the view and
  never meets the witness.

**What the build had to change.** The design's own targets were refuted as stated, and so were three
steps of its plan:
- an extension of the record list loses the records' tags;
- coherence is not kept when the outermost lend is at `⊤`;
- a cell kept across the stop can lose its stored invariant's support when its payload type reads a
  lifetime the instantiation moves. That last one is `mut_not_natural`'s mechanism.

The revised relation (`vRLJ`) fixes each:
- the extension keeps the tags;
- the outermost lend is below `⊤`;
- a kept cell's payload type reads only lifetimes the instantiation fixes.

Nothing in `Core/` or in a printed definition changed.

**What is still open.**
- The thaw at a `μ` or `fam` slot (guarantee gap R1). So the result is partial.
- The revision's obligations at the other rows:
  - every row that makes a `Mut` or `Imm` value must give the payload condition;
  - the share at a resume must keep the tags;
  - every lend must open below `⊤`.
- `binder0`'s own monotonicity (`MonoV`, `MonoG`, `MonoOwnG`), as before.
- The guard's run facts at a stack with a repeated place.
- Whether a kept cell with the refuted shape arises.

**What it decides.** Both shared needs of statement 0 are met at `binder0`, at the revised relation
`vRLJ`, for contexts without `μ` or `fam`. This is conditional on three added hypotheses that the
other rows still owe: `RetainedPay`, `KeepsT` and `OuterBelowTop`. `RetainedPay` does not settle the
`mut_not_natural` risk. It moves the retained-part case out of the thaw and into every row that makes
a `Mut` or `Imm` value. OQ-8 is still undecided, because `cbpv` and `binder` still owe their own
`U` rows. No machine-checked failure occurred, and the fallback is not triggered.

**What it means for D1's tractability.** The lifetime half of the freeze binder now has a proof
behind it at `binder0`: a resume that re-lends every internal lifetime as one order-preserving
instantiation keeps `Δ`'s models with no condition on `Δ`, and the four `U` introductions go through
with it. Both blockers the previous unit found turned out to be fixes to our definitions, which is
the outcome that favours D1. D1 is not yet shown tractable. The added hypotheses are owed at every
other row, R1 is open, `binder0`'s own monotonicity is not derived, and the `mut_not_natural` risk
has moved rather than gone.

## The instantiation's gap at `∀` (`GAP.md`)

This unit took the one step the freeze-binder unit left open in the lifetime half: that the
comparison of types up to the reading (`TyEq`) survives a resume's instantiation at every type, not
only at types with no thunk. The design is `GAP.md`, and its §8 has the outcome in full. Nothing in
`Core/`, in a printed definition, or in any ProbeD1 relation changed.

**Why it was hard.** Lifetimes are the naturals, so an instantiation that moves internal lifetimes
down can leave a gap: lifetimes nothing is sent to. A `∀` over lifetimes on the instantiated side
then ranges over the gap, where the old fact says nothing. And Core's relation really does notice
gaps: at `∀'0 ⊏ ⊤. F (Mut '0 1)` the closure `Λ. return ℓ₀` is related over a cell at `1`, next to
`⊤`, and not over the same cell moved to `2` (`coreAllAdjacent`, `coreAllNotNatural`). So
"invariance under every order embedding" is false for the relation, not just unproved.

**What was proved.**
- **`TyEq` does not notice gaps, so `TyEqInst` holds at every type** (`tyEqInst`). `TyEq` only
  compares lifetime terms for equality, and an equality on a chain can be checked one threshold at a
  time; at each threshold a lifetime in a gap behaves like `⊤` or like a lifetime below the
  threshold, and both exist. This is the "threshold cover" (`tyEqOfCover`).
- **The thaw and the four `U` rows hold at every payload type** at `binder0`
  (`statement0UThawFreeKJ`). The restriction on borrow payloads (no thunk, `μ` or `fam` inside)
  is gone. The only slots still excluded hold a `μ` or `fam` type outside a borrow's payload (R1).
- **The direction given with the task, made exact.** Quantifying over positions among the lifetimes
  in play, each realised by an instantiation, is a combinator (`AllPosJ`) that is realisable
  (`instRealisesCut`), carried along instantiations (`allPosJTransport`) and equal to Core's clause
  when nothing is lent (`allPosJNil`). **W's `U` clause implies this quantifier for the body of a
  thunk whose type is `U (∀…)`** (`wU_allPosJ`). This is one way only: W's clause is stronger,
  because it also quantifies over record extensions. At the configuration where Core's `∀` holds
  by adjacency, W's `U` clause rejects the closure that Core's accepts (`adj_not_wU`, `adj_core_U`). Quantifying over every position of
  the whole order instead, by renaming the configuration, would agree with Core only one way
  (`cutAllNilSound`, `not_coreAllImpCutAll`), and it is not adopted.

**What is still open.**
- R1: the thaw at a `μ` or `fam` slot. Its route is for W to read `μ` and `fam` itself, so that a
  thunk inside is W's `U`, which reads every position below the stack's cut by construction. Not
  attempted here.
- `ViewSlotInst` without the "outermost lend below `⊤`" hypothesis, which every index the relation
  reads has.
- Everything else the freeze-binder unit listed: `binder0`'s own monotonicity, the revision's
  obligations at the other rows, the guard at repeated places, and whether a kept cell with the
  refuted shape arises.

**Is the `∀` gap closed?** Yes, for the statement that was open. `TyEqInst` now holds at every
type, and so the thaw and the four `U` rows hold at every borrow payload type. No relation changed
to get there. The fix was an argument about `TyEq` alone, which compares lifetimes only for
equality and so never sees the gaps. The relation's own `∀` is a different matter: Core's relation
does see gaps, so it is not invariant under every order embedding, and nothing here claims it is.

**What the stronger invariance gives.**
- `TyEq` is invariant under every order embedding that fixes `⊤` (`tyEqRoomBlind`), not just under
  the one instantiation a resume uses. Every row that compares types across a resume can use it.
- The position-`∀` (`AllPosJ`) is invariant under instantiations by transport
  (`allPosJTransport`), and it agrees with Core both ways when nothing is lent (`allPosJNil`). So
  if a later statement needs a computation at `∀` carried across an instantiation outside `U`,
  `AllPosJ` is ready, and adopting it restates no use of agreement with Core.
- W's `U` clause already reads the top-level `∀` of a thunk at every position an instantiation can
  open (`wU_allPosJ`, one way). So the adjacency effect that makes Core's `∀` sensitive to gaps does
  not reach the thaw at a `U` slot.

**What it decides.** The lifetime half of the freeze binder no longer depends on the payload
types. The thaw's only guarantee gap is R1. OQ-8 is still undecided, no machine-checked failure
occurred, and the fallback is not triggered.

## R1 and `binder0`'s monotonicity (`R1MONO.md`)

This unit took the four things the gap unit left at `binder0`:
- R1, the thaw at `μ` and `fam` slots;
- `binder0`'s own monotonicity;
- the three obligations the revised relation took;
- statement 0 at the revised relation.

The design is `R1MONO.md`, and its §8 has the outcome in full. Nothing in `Core/` or in a printed
definition changed. The draft relation is now `vRLM`, which reads `μ`, `fam` and type variables
itself instead of handing them to Core.

**R1 is closed.** Core's relation reads a thunk inside a `μ` value with its own `U` and `ℕ`-`∀`,
which notice adjacency. Once W reads `μ` itself, the thunk is read by W's `U` clause. The thaw then
holds at every type, by induction on the data with no step index (`relendMValueE`), and with it the
four `U` introductions at every context (`statement0UFullM`). The adjacency closure that Core's `μ`
admits is not in `vRLM` (`muAdjNotVRLM`).

**Monotonicity: the lemma as stated fails, the row it was for mostly holds.**
- The configuration `gd` is a closure `λg. return g` that is a value at the stack only because the
  stack's guard keeps every argument above a lifetime `'1`. When the own lend pushes a new entry,
  an argument holding the new view breaks that, and the closure is no longer a value (`gdNotPushed`).
- So the unrestricted statements `MonoOwnGM`, `MonoGM` and `MonoVM` are refuted at `binder0`
  (`notMonoOwnGM0`). `gd` is not shown to arise, and two facts count against it: its closure is
  not a Core value, and its records fail an invariant the arising set is expected to keep
  (`RecsInsideOwn`, not proved for it). These are facts about our statements.
- The lemma's one consumer is the `∀I` row. **The row is proved at every context whose live
  variables reach no `U`**, at every index whose stack does not name the binder
  (`allIRowMNKUFree0`). On the way, the row turned out to need two more transports of its context
  beside the push, both about the reading of lifetime variables. Both hold where no `U` is reached
  (`vRLM_reading_uFree`).
- At `gd` itself the row's conclusion holds for a well-typed body that passes the closure a thunk
  holding the new view and runs what comes back (`gdAllIHoldsAtMt`). The run never asks the box
  that broke, so the lemma failing there is not the row failing there, at least for that body.
- Still open: the row at a context holding a `U` value, and at an index whose innermost lend is
  named by the binder.

**The three obligations.**
- Lends below `⊤`: proved everywhere, including the arising set (`outerBelowTopArises`). Across the
  arising set this comes from [TR] 6.64/6.65 H4's consequence (the new lend's lifetime is below
  `⊤`), which the unit added as a field of the draft definitions `LendMutI` and `LendImmI`.
- The payload condition (`RetainedPay`): proved at the lend's view, the transports and `∀E` at an
  instance with no join whose variable no stack entry names. At the `Mut` read-out through a bound view it stops where the design expected, at
  `EntryPayLeaves`: the condition for the lending entry's own payload type, which the index does not
  carry.
- **A fact about the guard, with one step unchecked: `withload` of a value holding two references
  side by side.** The guard forbids a shared cell at exactly the new lend's lifetime at a place no
  stack entry lends (`rebGuardFails`). So a resource with two such cells at distinct places meets
  the guard at no pushed stack (`loadGuardFails2`). `withload` hands its callback the payload
  re-borrowed at the new lend's lifetime. Whether that argument at `Ref 1 ⊗ Ref 1` really holds two
  such top-level cells at the callback's guard is [unchecked], and no such configuration is shown
  to arise. I have not verified that any obstruction is real, and no change to W's draft
  definitions follows until that step is proved.
- The tags at the share (`KeepsT`): proved from `LineageUnique` (a record lies in one frame's
  lineage), which is not derived.

**Statement 0 at `binder0`.** Every fact beside monotonicity is proved
(`statement0MBesideMono0`). The `∀I` row together with `MonoExtM` covers `MonoOwnGM`'s consumer and
the record-order rows; `MonoExtM` is proved, and the `∀I` row is proved except at `U` slots and at
the binder-named indices. That these are *all* the consumers of `MonoVM` and `MonoGM` is
[unchecked]. `statement0MAtConsumers0_iff` does not show it: it holds by the definition of our own
conjunction. And the handler's `MonoHide` at `vRLM`, which used to come from `MonoV`, is not stated.

**What it decides.** R1 is closed at `binder0`, by changing the draft relation at `μ`; the unroll row
now owes `vRLM`'s substitution lemma. Statement 0 there is not yet shown complete. Its known open
pieces are the `∀I` row's two open cases and `MonoHide` at `vRLM`, and whether anything else
consumes `MonoVM` or `MonoGM` is unchecked. `loadGuardFails2` is a proved fact about the guard;
whether `withload` at `Ref 1 ⊗ Ref 1` meets it is unchecked. OQ-8 is still undecided, because no
refutation passed the arising check, statement 0 is not complete at any placement, and `cbpv` and
`binder` were not redone at `vRLM`. No machine-checked failure of type (a), (b) or (d) occurred,
and the fallback is not triggered.

## The guard gap, the unroll row, the `∀I` row, `MonoHide`, and the floor (`NEXT.md`)

This unit took four things the R1 unit left at `binder0`:
- whether the `withload` gap is real;
- the unroll row at `vRLM`;
- the `∀I` row's two open cases;
- `MonoHide` at `vRLM`, with a check of statement 0's consumers.

The design is `NEXT.md`. Its §9 has the outcome in full, and §10 the user's corrections of
2026-10-08. Nothing outside ProbeD1 changed.

**The user's corrections of 2026-10-08.**
- Borrow-only programs (ordinary closures, higher-order functions, borrows without suspension) are
  already proved in Core, and the draft relation must reproduce that. A gap found on such a program
  is a defect of the draft, to be fixed. It is not a restriction, and not a cost of a placement.
- Persistent resource-free values must be carried across a lend by construction.
- Test programs are written the way the language writes them. `retry` is a handler around the
  borrow, and the callback performs operations.
- Real restrictions are expected only where a callback suspends while an inner lend is open, which
  is tier 2.

**The `withload` gap is real, and it is a defect of the draft.**
- A configuration that arises was built: allocations, a 6.64 lend, and the typed world's own
  reborrow step ([TR] 6.150). At it, `withload` of a pair of references, at its unwinding type,
  hands its callback a reborrowed pair that the guard rejects at every reading
  (`withloadUPairGapReal`).
- The cause is the stack entry. A lend's entry covers one place, and the reborrow makes two cells at
  two places.
- At `withload`'s own thunked type, the same configuration does not show the gap: the answer's
  instantiation moves the lend below the cells (`not_withloadPairGapInst`).
- After (E1), the gap also shows at the top level (`withloadUPairGapNilE1`).
- The fix is designed: a block entry lending several places at one lifetime (`NEXT.md` §1.6). It is
  not built.

**The unroll row is proved** (`vRLMUnroll`, `rollRowM`, `unrollRowM`).

**The `∀I` row.**
- It now holds at every context whose live variables reach no `U`, at every index, including an
  index whose innermost lend is named by the binder (`allIRowMUFree0`). That closes one of R1's two
  open cases at those contexts.
- At a context holding a `U` value it is not derived. The planned route to the row's reading
  transports breaks at the effect clause's re-lend (`not_readEquivRelend`, a fact about our own
  statement). The push at a `U` slot was not attempted.

**`MonoHide`.**
- Hiding is the identity where the hidden names cross no lend (`hideInvisible`).
- Statement 4's transport (`AllRMonoM0`) has its record-order half, its thaw half at the empty
  resource, and its hide half where the hidden names cross no lend. Its own-push half and the rest
  are open.
- The inventory of statement 0's consumers was not written. So nothing is claimed about what
  statement 0 at `binder0` reduces to.

**The floor for persistent values.**
- Before this unit, nothing in the draft's `!` clause carried a persistent value across a lend,
  with or without (E1). At the relation before (E1), a persistent closure is related at a stack and
  not after a lend's push (`gdBangJ`, at a configuration not shown to arise).
- So (E1) was kept, and the `!` clause was fixed: the persistence box.
  - A persistent thunk is now related at every world `binder0`'s order reaches: every
    instantiation, and every sequence of resource-free lends under reserved names.
  - It is carried across those lends by construction (`persistentPushN`), and the `!U` rows are
    re-proved (`statement0UFullM`).
- Still open:
  - the `∀I` row's own lend at a persistent context, which is named by the binder rather than a
    reserved name (`VRLMStackRename`, stated, not derived);
  - the reading transports there;
  - a persistent slot reaching `U` below its top;
  - linear closures across a lend;
  - the floor's own statement at the empty stack.

**`reconB′` is written as the language writes it** (`reconB'`).
- `retry` is a handler around the lend, and the callback performs `wait`. It runs to `(tt, ff)`.
- Its callback captures nothing, so its `∀I` row is read at the empty context, where it holds
  (`reconCb_allI`).
- What it still owes is the suspension inside the lend (tier 2). Its typing is not built.

**Not reached:** the block (item 1b), the slice gate, and the thunked callback rows
(`CallbackExt*MF`). Four review findings stay open (`NEXT.md`, *Unresolved*).

**What it decides.**
- The two defects found on borrow-only programs are the draft's: the two-cell entry, and the `!`
  clause, which is now fixed.
- OQ-8 is still undecided. No machine-checked failure of type (a), (b) or (d) occurred, and the
  fallback is not triggered.
- The box makes the `!` clause reach other stacks. If statement 0 comes to hold only with the box,
  DESIGN §12.2's reading of (d) applies to it (DESIGN §15.10).

## What remains for tier 2

Tier 2 needs `Statement0 p` at some placement, then statements 1–4 and both programs. Borrow-only
programs are a floor. A gap on one is a defect of the draft, and it is fixed before tier 2 is
judged. At `binder0`, the placement with the most proved, the remaining work is:
- **The two-cell defect: the block (item 1b).**
  - `withload` of a pair of references fails the guard at a configuration that arises
    (`withloadUPairGapReal`). It also fails at the top level after (E1) (`withloadUPairGapNilE1`).
  - The slices at two or more elements fail the same way (`SliceGuardFails`). Their gate
    (`SliceUGapReal`) is not built.
  - The designed fix is a block entry: one lend of several places at one lifetime (`NEXT.md`
    §1.6). It changes `StackOK`, so every row at `binder0` is re-proved at the revised relation.
  - If the block's gate fails, (E1) is revisited at the top level, as a defect of the draft.
- **The floor for persistent values, the rest of it.**
  - The `∀I` row's own lend at a persistent context: `VRLMStackRename` (stated, not derived), and
    the reading transports at a `!U` slot.
  - A persistent slot reaching `U` below its top: `PBox` at every `!B` that reaches a `U`.
  - The floor's own statement, that the draft relates at the empty stack every program Core's
    `fundamentalC` covers: not stated. OQ-58's statements are the nearest, and were not attempted.
- **The `∀I` row at a context holding a linear `U` value.**
  - The reading transports (`VRLMReadEquiv`): the planned route stops at the effect clause's
    re-lend (`not_readEquivRelend`).
  - The push: 3b-i (`MonoOwnGMAtPS`) and 3b-ii's steps (`PushArrStep`, `PopUStep`, `PushEffStep`,
    `PushAllStep`), stated and not attempted.
  - The unrestricted push is refuted at `gd`, a configuration not shown to arise.
- **The thunked callback rows** (`CallbackExtMutMF`, `CallbackExtImmMF`): stated, not proved. The
  proved callback rows are at the unwinding forms' `.arr` shape. The non-unwinding constants'
  callbacks are thunked, and have no proved own-push route.
- **`MonoHide` and statement 4's transport.**
  - `MonoHideGM` beyond the case where the hidden names cross no lend: `VRLMHideAvoid`,
    `HideStopStep`.
  - `AllRMonoM0`'s own-push half, its thaw half at a slot holding resource (`RelendJInter`), and
    its hide half's general case.
- **The consumers inventory** (`NEXT.md` §4.2). It is needed before anything is claimed about what
  statement 0 at `binder0` reduces to.
- **`reconB′`'s typing** at the probe's rule set, and its suspension inside the lend (statements
  1–3).
- **The obligations' leftovers.**
  - `RetainedPay`:
    - `EntryPayLeaves` at a bound `Mut` view (or the variant leaf, which changes W's views, the
      user's to decide);
    - the `Imm` read-out;
    - joins;
    - `RetainedPay` at `∀E` when a stack entry is named by the instantiated variable.
  - `KeepsT`: `LineageUnique`, and `FramesKept` from statement 2.
  - `ViewSlotInst` without `OuterBelowTop`.
- **OQ-8, where the future-world quantifier goes.**
  - Still undecided. `cbpv` and `binder` have not been redone at `vRLM`, and still owe their `U`
    rows with futures (`BINDER.md` §5.6), and the names the changed `FutStep` admits.
  - If statement 0 comes to hold at `binder0` only with the persistence box, DESIGN §12.2's reading
    of (d) applies to it.

## What to do next (options, not a decision)

1. **Finish the open review findings.**
   - The R1 unit's two major findings are now corrected in README, DESIGN §15.9 and `R1MONO.md`
     §8, with this unit's results.
   - The four major findings in `NEXT.md` *Unresolved* were answered in the text and not reviewed
     again.
   - The statement-0 unit's minor wording findings are still open (the note at the top).

   This is needed under every option.
2. **Continue D1.** The freeze-binder unit did the first two steps at `binder0`: PlaceViews is in
   the guard and the own lend, and the re-lend is an instantiation that lowers the stack's variables
   together. The gap unit removed the payload restriction. The R1 unit closed R1, proved statement
   0's other facts at `vRLM`, and proved the `∀I` row at contexts reaching no `U`. The guard-gap unit
   found the two-cell defect at an arising configuration, proved the unroll row and the `∀I` row at
   every index at those contexts, and gave persistent thunks the box. What is left, the floor
   first:
   - the block (item 1b), which is the designed fix for the two-cell defect at `withload` and the
     slices;
   - the floor's rest:
     - `VRLMStackRename`;
     - the reading transports at a `!U` slot;
     - `PBox` at every `!B` that reaches a `U`;
     - the floor's own statement at the empty stack;
   - the `∀I` row at a linear `U` slot: its reading transports and its push;
   - the thunked callback rows (`CallbackExt*MF`);
   - `MonoHide` beyond invisible hiding, `AllRMonoM0`'s open halves, and the consumers inventory;
   - whether a retained cell with `mut_not_natural`'s shape arises (`InternalPayloadArises`,
     `InternalLeafArises`), and `EntryPayLeaves` at the `Mut` read-out. A gap there on a
     borrow-only program is a defect of the draft, to fix;
   - `LineageUnique`, which the tags at the share rest on;
   - `cbpv`'s and `binder`'s `U` rows with futures (`BINDER.md` §5.6), redone at `vRLM`;
   - the names the changed `FutStep` gives, through a `StackJ` with a hygiene the rows can
     discharge, or through the renaming lemma.

   Then re-attempt statement 0, and statement 1 after it.
3. **Fall back to D3.** The closure keeps its lifetime across the stop, so there is no re-lend. The
   models-at-a-re-lend need does not come up. The cost is D3's stop change (D3.k1–k7) and scoped
   rows (D3.k12). The probe has not triggered the fallback: no machine-checked failure of type (a),
   (b) or (d) occurred. Choosing D3 now would be a judgement about cost, not something the probe
   forces.
4. **Fall back to D0.** This is the option if D3's stop change also fails. D1's A-side work carries
   over to it unchanged.
