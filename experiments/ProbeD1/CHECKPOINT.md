# ProbeD1: checkpoint

This is a plain-language summary of where the D1 tractability probe stands. The full outcome is in
`README.md` and `DESIGN.md` §15. The Lean is in `ProbeD1/`, and `lake build ProbeD1` builds it.

> [!NOTE]
> **All verifiers passed on the freeze-binder unit.** The hygiene review and the content review both
> passed. The content review raised three minor findings, and each is addressed:
> - The "what it decides" paragraphs now say the shared needs are met at `vRLJ` *conditional on*
>   `RetainedPay`, `KeepsT` and `OuterBelowTop`, which are owed, and that `RetainedPay` moves
>   `mut_not_natural`'s retained-part case into the `Mut`/`Imm` rows without settling it.
> - The added hypotheses now have Lean witnesses that they are satisfiable: `retainedPay_of_closed`,
>   `retainedPay_of_bound` and `keepsT_refl` (`BinderRows.lean`). `OuterBelowTop` already had
>   `ownPushBelowTop` and `outerBelowTop_inst`.
> - Item 3 now opens by saying that whether the witness arises is undetermined.
>
> The earlier statement-0 unit's open wording findings (the "only with" claim in DESIGN §2.2, the
> unmarked prose reasons in DESIGN §15.2 and the README, `MonoHide binder0`'s status, and the
> README's "no way to reach a stack" sentence) are still open. They are listed under option 1 below.

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

## What to do next (options, not a decision)

1. **Finish the open review findings** (the statement-0 unit's minor wording ones, listed in the
   note at the top). This is needed under every option.
2. **Continue D1.** The freeze-binder unit did the first two steps at `binder0`: PlaceViews is in
   the guard and the own lend, and the re-lend is an instantiation that lowers the stack's variables
   together. What is left:
   - whether a retained cell with `mut_not_natural`'s shape arises (`InternalPayloadArises`), which
     decides whether `RetainedPay` is a real restriction;
   - R1: the thaw at `μ` and `fam` slots;
   - the revised relation's obligations at the other rows (the payload condition, the tags at the
     share, lends below `⊤`), and statement 0's other facts redone at it;
   - `cbpv`'s and `binder`'s `U` rows with futures (`BINDER.md` §5.6);
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
