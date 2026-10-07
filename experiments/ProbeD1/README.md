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
| `ThunkFRow`, `ThunkVRow`, `BangThunkFRow`, `BangThunkVRow` (the `U` introductions) | not derived | not derived | not derived; proved given the context's thaw, where re-lends keep `Δ`'s models |

Nothing was refuted. `MonoHide` holds at `cbpv` and `binder` through `MonoHideFromMonoV`, which holds
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

**The `U` introductions are where statement 0 stops, at every placement and for one reason.** Each
owes the closure's body at every re-lend of the stack (and at `cbpv` and `binder` at every future of
the re-lend). GhostEnd proved the clause's half from two hypotheses, the context re-lendable and the
body at every re-lend. At W neither is derived:
- **the context's re-lendability** under the table (`CtxRelendable`, named in `Thunk.lean`). A `U`
  slot meets it (`thawRelend`); a leaf whose cell sits at a stack place without being that entry's
  view is not covered by anything `SemS` assumes;
- **the body at a re-lend**: the premise's `SemS` asks `Δ.Models` at the re-lent stack, and a
  re-lend need not keep it at a configuration `SemS` admits (`models_reLend_fails`): a variable of `Δ`
  off the stack, bounded by a stack variable, keeps its lifetime while the stack's is re-lent below
  it;
- at `cbpv` and `binder`, the context carried to a future that inserts between lenders, where the
  inner views sit below the inserted lifetimes and `MonoG`'s hypothesis at the context's whole
  resource fails, and the premise at a future whose inserted name `StackJ` does not admit.

At `binder0` the first two are all that is missing: given `CtxRelendable`, the four rows hold at
the configurations whose re-lends keep `Δ`'s models (`thunkFRow_binder0_of` and its three
siblings, with statement 1's `TabRelend` proved on the way).

The first two hold at every placement and do not depend on it. They are about `SemS`'s hypotheses
and the context's thaw, so by the stop rule's shared-reason clause they are a finding about our
definitions, not a comparison of placements. No obstruction is verified: no configuration here is
shown to arise in `TW`, and no row is refuted.

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
  derived anywhere, and what they still need is named. Two of those needs, the context's thaw and
  `Δ`'s models at a re-lend, are facts `SemS` does not give. For the second, Lean shows it failing at a
  configuration `SemS` admits (`models_reLend_fails`), so applying the premise at every re-lend the
  clause owes is not available as `SemS` stands: a proof needs another route at those re-lends, or a
  change to `SemS` or to what a re-lend re-lends. Which, is a design question the probe does not
  answer.
- **The fallback is not triggered.** D3, then D0, follow a machine-checked failure: (a) a refutation
  at a configuration that arises, (b) a guard beside `TW` or a second relation family, or (d) two
  quantifiers. None occurred. Nothing here is evidence that D3 or D0 is needed, and nothing is
  evidence that it is not.
- **The next step** is to settle the three needs of the `U` introductions: Δ's models at a re-lend
  (exclude, or re-lend with the stack, a variable off the stack bounded by a stack variable), the
  context's thaw under the table (by type, or from arising), and the names the changed `FutStep`
  gives (a `StackJ` that admits them with a hygiene the rows can discharge, or the renaming lemma).
  Then statement 0 can be re-attempted, and statement 1 after it.

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
| `ProbeD1/Thunk.lean` | `CtxRelendable`, `models_reLend_fails`, `tabRelend`, `SemSR`, the four `U` introductions at `binder0` given `CtxRelendable` |
