# LoopBorrow: borrow scopes over codata (O1)

**Question.** A borrow block's body is one computation (`F`). Loops, generators and tasks are
codata (`ν`), observed one run at a time, so no rule lends at `'x` to something that runs for
many observations. Can `withbor` be lifted through every computation type, `ν` included? Which
of the blocked programs need that, and which are already expressible?

Build: `lake build LoopBorrow`. The library imports `Core` and `Frontend.Check.CrossCheck`, and
nothing imports it. `Paper/`, `Support/`, `Examples/`, `Core/` and `Frontend/` are unchanged.

| file | contents |
|---|---|
| `Obstruction.lean` | `↭` brackets every borrow cell inside one run (`not_upd_of_new_mut`, `not_upd_of_ended_mut`, `not_upd_of_new_imm`); `Ext` sees a lend only through a borrow cell (`ext_of_cellIn`, `ext_unfolded_not_folded`); `RefoldKripke`, refuted (`refoldKripke_false`) |
| `Refold.lean` | a saved lend re-pushed for one observation at any depth (`wpTS_M_refold`, with 6.27 at `Res_{↓α}`, `six27_down`) |
| `Dormant.lean` | the dormant lend: with the freeze the refold step closes (`refoldKripkeD`); no run installs the freeze (`not_markerInstallable`); the consumer's frame that breaks the refold, as a tagged typed world (`refold_fails_at_consumer_frame`); no observation yields a borrowed element (`not_lendingYield_mut`, `not_lendingYield_imm`) |
| `Instances.lean` | six programs over the per-observation lend, each checked by the kernel checker, covered by `fundamentalC`, safe on every run (`theorem32D`) and interpreted with no cell left |
| `bc/` | the programs |

Every result's axioms are within `[propext, Classical.choice, Quot.sound]`.

## Verdict

- **The per-observation lend works today, with no new rule.** The lender lives in the codata's
  state, and each observation lends it for that observation only, by an ordinary `withbor`
  inside one run. Loops over a borrow, generators holding a lender, a configuration lent to
  every step, a lending yield in push form, and zips of lending sources are all library code
  over `unfold`. This result is worth landing on its own.
- **A lend that spans observations does not close in this model.** Refolding the lend at each
  observation is fine for the typed world (`wpTS_M_refold`). The Kripke order of the state held
  between observations cannot see the lend's lifetime, and no run can give it a borrow cell
  that would let it see it: `↭` requires every borrow cell a run hands back to have been in the
  flattening it started from. With the freeze such a cell would give, the refold step closes.
  So the spanning lend needs a model change: a borrow that `↭` lets outlive the run that opens
  it. That change is not verified sound, and nothing here shows the spanning lend unsound.
- **A lending yield in pull form (an element handed out and borrowed until the next
  observation) is excluded in every route here.** This includes the spanning lend. In push
  form (the consumer's body runs inside the observation) it works today.

## What works today: the per-observation lend

Each program's `main` is checked by `bcc`'s checker in the kernel (`decide +kernel`). The
checker returns a `CDerives` derivation at the empty context. `fundamentalC` covers it, every
run from the empty memory continues to a value at the empty memory (`…_every_run`), and the
interpreter's answer has no cell left (`…_eval`).

| program | combinator | what it shows | answer |
|---|---|---|---|
| `lend-loop-imm.bc` | `lend_loop_imm` | the core of `corpus/pending/borrow-across-loop.bc`: a table borrowed `imm` on every step of a loop | `100` |
| `lend-gen-mut.bc` | `lend_gen_mut` | a generator lending a cell `mut` on every `next`; pulled three times and closed; the cell comes back | `(18, 8)` |
| `lend-config-imm.bc` | `lend_loop_imm` | a loop-invariant configuration borrowed by every iteration | `(12, 4)` |
| `lend-each-imm.bc` | `lend_each` | a **lending yield in push form**: each observation lends one array entry to the body as a view `imm 'z i32`, a borrow that ends inside the observation | `100` |
| `zip-push-pull.bc` | `zip_lend` | that source zipped with an ordinary generator, pulled before the lend | `200` |
| `zip-push-push.bc` | `zip2` | two lending sources zipped: both owners in the state, the lends nested in one observation, both views borrowed at once | `300` |

The combinators are `unfold` steps whose state holds the lender (`Ref A`) and whose step is
`withbor` around the per-observation work. The step's result outlives `'x`, so nothing derived
from the borrow survives between observations. Setting up a borrow per step costs nothing at
run time, since `withbor` passes the location.

### Coverage of the blocked programs

| program | per-observation lend | needs |
|---|---|---|
| `for` inside a borrow block (`borrow-across-loop.bc`) | **covered** when the loop's state outlives `'x`: the owner moves into the loop's state (`lend-loop-imm.bc`). The surface form is elaborated so (SPEC §14, borrow scopes over loops; `Frontend/Elab/LoopLend.lean`), and the program runs as `corpus/axes/borrow-across-loop.bc` | — |
| generators holding a lender, driven in the scope | **covered** (`lend-gen-mut.bc`) | — |
| a borrow spanning a `yield` | **covered** when the borrow is taken again at the resume. Nothing else derived from it can survive the yield in this model: a view is made inside a run and ends there (`upd_borrow_top`) | — |
| lending yields | **push form covered** (`lend-each-imm.bc`). The body is the step's input, and a `for` body is fixed per loop, so no sink observation is needed. **Pull form excluded** (below) | — |
| async tasks borrowing config | **covered in step form**: the scheduler's state holds the owner and lends per poll (`lend-config-imm.bc`) | a task written as an opaque `U(Loop …)` capturing the borrow needs the spanning lend |
| scoped threads | as async: step form covered | the same |
| a div function with a borrow parameter, called in direct style inside a borrow block | **covered when its body is visible**: it is elaborated to take the owner and lend it at each step, and the call lends the place (`corpus/lend-server.bc`, `lend-div.bc`). Not covered for a borrow not lent from a place, or opaque codata capturing a borrow | the spanning lend, for those |

The spanning lend buys one thing: **opaque codata holding a borrow across observations**. A
library `gen fn iter<'a>(xs: &'a T)`, or a div function taking a borrow, driven from inside a
borrow block whose body loops. For "no function coloring" that is the case that matters: a
div callee with a borrow parameter.

### The lending yield

`Dormant.lean` machine-checks the crux. `upd_borrow_top`: a borrow cell at the top level of what
a run hands back puts a borrow cell of the same kind in the flattening the run started from
(`↭`'s `mut` clause, and its `imm` clause through `ResU.Flat.get`). `borrowFree_after_run`:
from the unfolded lender `ℓ ↦ own(w)`, at the tagged typed world it completes to, every run
hands back a borrow-free state. So no observation from the generator's state yields a `Mut` or
an `Imm` element (`not_lendingYield_mut`, `not_lendingYield_imm`). An observation can hand out
only a borrow whose cell was already there when it started: a borrow the consumer opened. An
element borrowed at a lifetime that ends at the next observation would be a cell made by one
run and ended by another. The spanning lend does not change this: it refolds the owner inside
each observation, and anything it hands out is still made in that run. This matches the
exclusion of same-lifetime views through a pointer (`SPEC.md` §5, Open; `experiments/FrameEnd`).
Rust's `LendingIterator` fits the same pattern: its caller opens the `&mut self` borrow at each
`next`.

### Zip

| zip | today (state + step) | with sink observations | with the spanning lend |
|---|---|---|---|
| pull × pull, owned sources | yes | yes | yes |
| pull × pull, sources holding a borrow, driven inside a scope that loops | only rewritten as state + step with the owners in the zip's state | same | **yes**: this is what the spanning lend buys |
| push × pull | **yes** (`zip-push-pull.bc`), pulling before the lend | yes with an opaque lending source, pulling outside its callback | — |
| push × push | **yes** when both are state + step (`zip-push-push.bc`) | one opaque source and one state + step: yes (the opaque one outside, the other lent inside its callback). Two opaque sources: no | no help |
| pull × pull of lending sources (elements handed out) | no | no | no (`not_lendingYield_*`) |

Push × push does not need the spanning lend. It needs the two lends to nest inside one
observation, and that works today when the sources' states are data. What stops two *opaque*
sources is typing, not the Kripke order. The inner source's rest is a thunk that would have to
leave the outer lend's `['x]` box, and `U C` has no outlives rule. The checker rejects exactly
this: pulling the generator inside the lend in `zip-push-pull.bc` gives "`g2`, of type
`U (gen i32 1 1)`, … cannot be shown to outlive `'x`". Lifting that needs `X` under `[@a]` in an
observation result (outside `NuOk`), not a spanning lend.

### Sink observations (issue #96)

The route: the observation takes the consumer's body as input, a lifetime-polymorphic callback,
and lends the element to it inside one run.

- **Soundness.** It is the per-observation lend with the body as an argument, so the existing
  machinery covers the lend. For a `for` loop the body is fixed per loop and fits in the step
  (`lend-each-imm.bc`), so no sink is needed. A sink buys a lending source as **opaque** codata,
  whose callback may differ per observation.
- **Cost.** An observation tree `A ⊸ D` with `X` not in `A`:
  - one `NuLeaf` clause and one `cB` clause (the `⊸` clause of `cC`, at `vCE η`);
  - `instT`, and a `nodeV`/`node_ok` case (`λa.` around the child);
  - `cB_mono` and `cB_unroll` cases, and the `CTyEq` lemma on `NuLeaf`.

  The greatest fixed point is taken over candidates, and an `X`-free input leaves `Φ_C`
  monotone, so no step index is needed. The estimate is a few hundred lines in `Core/Types`,
  `Relation`, `NuRel` and `Nu`, plus a §7 entry. It is not built here.
- **What it does not buy.** Two opaque lending sources zipped (above), and the pull form.

## The obstruction and its status

1. `↭` (5.27) is an equivalence on the borrow cells of the flattening, so a run cannot create
   or end a borrow cell (`not_upd_of_new_mut`, `not_upd_of_ended_mut`, `not_upd_of_new_imm`).
   Between observations the lend is held unfolded: `ρr ● ℓ ↦ own(w) ● χ`.
2. Refolding it for one observation, at any depth, is a theorem (`wpTS_M_refold`). Nothing in
   `TW`, `Tagged`, memory or `↭` depends on where the consumer's frames sit.
3. The inner thunk's Kripke order is `Ext` at the folded state, which freezes the records
   longer-lived than `α`. The unfolded state has no cell at `α` and freezes nothing
   (`ext_of_borrowFree`). `RefoldKripke` names the implication a refold proof needs, and it
   fails (`refoldKripke_false`, at tags `1` and `2`, both below `⊤`).
4. The failing list arises (`refold_fails_at_consumer_frame`). A consumer borrows a cell of its
   own at `γ = 1`, with the lend at `α = 2`, and observes the loop inside that borrow. Its list
   `[(r, γ)]` is the list of a tagged typed world holding the lender (`consumer_frame_world`,
   built by `TW.alloc` and `TW.immFrame`). The unfolded state admits it, and the folded state
   does not. `withbor`'s callback ranges over every `γ ⊏ ⊓Δ`, and nothing orders `γ` below a
   lend its type does not mention.

This shows that the refold route does not close. It does not show that a spanning lend is
unsound.

## The dormant lend

A dormant lend is a record, in the state held between observations, that a lend is suspended
at `α`, so that `Ext` freezes what the folded state would.

- **With the freeze the route's Kripke step closes.** `Frozen α ls ls′` is what `Ext` reads off
  a borrow cell at `α` (`frozen_of_cellIn`). With it, the unfolded state's order gives the
  folded state's (`ext_refold_of_frozen`), and `RefoldKripkeD`, `RefoldKripke` with the freeze
  added, holds (`refoldKripkeD`). The candidate assembly around it was not attempted: the
  obligation that remains is `nuP`'s Kripke order (plain `Ext`) at the rest of the outer loop,
  and it can be met only in a model that carries the freeze.
- **No run installs the freeze with the cells this model has.** `Ext` sees a lifetime only
  through a borrow cell (`CellIn`), and a run from the unfolded lender hands back no borrow
  cell (`borrowFree_after_run`). `MarkerInstallable` names the step, a run from `ℓ ↦ own(w)`
  whose every result holds a cell no longer-lived than `α`, and `not_markerInstallable`
  refutes it. `own` cells are invisible to `CellIn`, and `imm`/`mut` cells are bracketed by `↭`.
- **Relabelling instead.** Refolding at a fresh `α′` per observation would need the inner
  thunk's relation transported along a lifetime renaming. That is a parametricity property of
  the relation. `relabel_obs` gives it for reborrow images at data types only, not at `U`. Not
  pursued.

**What the marker must record.** Balzer and Pfenning, *Manifest Sharing with Session Types*
(ICFP 2017), have a client acquire a shared process, interact over many steps, and release it.
Meanwhile the configuration holds a placeholder `unavail(a_S)` (rule D-↑SL; configuration
typing T-Λ3). The release must be at the type of the acquire (equi-synchronizing, T-Θ2's
`⊢ (A_L, B̂) esync`). Read in this model:

- the placeholder is the lend held **folded** between observations, `ℓ ↦ mut(α, v, χ, P̂)`;
- equi-synchronizing is `↭`'s `mut` clause, which already fixes `α` and `P̂` across a run;
- the independence principle, that shared cannot depend on linear, is the stratification
  `Res_{↓α}`.

Holding the lend folded makes the freeze automatic: the cell is at `α`, and `withbor`'s frame
choice (`a₂ ⊓ m` below the callback's resource) forces every consumer frame below `α`. So a
marker needs no new cell kind. What it needs is a **register of open lends** in `wpTS`, a
coordinate like `ps`/`ls`, and `TW` constructors that open and close an entry. `↭`'s `mut`
clause would be read modulo the register: a run may open a lend, leaving a `mut` cell its start
did not have, or close one, returning the owner at the same `P̂`. This is a design reading of the
paper, not a Lean result.

## Promotion cost

- **The per-observation lend.** No kernel change. Landed (SPEC §14, borrow scopes over loops):
  the combinators are `lib/lend.bc` (`loop_lend_*`, `gen_lend_*`, `array_each_imm`), and the
  surface forms are elaborated by `Frontend/Elab/LoopLend.lean`.
- **Sink observations.** A `NuOk` clause and five cases (above). No new former, no `CDerives`
  index, one `unfold` compatibility case.
- **The spanning lend.** A new coordinate of the model, the register of open lends:
  - in `wpTS` and `TW`, with `↭`'s `mut` clause read modulo it;
  - one `CDerives` rule, `withborLoop : Ref A ⊸ (∀'x ⊏ ⊓Δ. Mut 'x A ⊸ F(U(Loop (['x] B) R))) ⊸
    F(U(Loop (Ref A ⊗ B) (Ref A ⊗ R)))`, with its compatibility lemma.

  Decision 19 allows this: the coordinate is in the model, not an index on `CDerives`. The
  cost is in `Core/World.lean` and `Wp.lean`, and in every frame rule that reads `↭`
  (6.64–6.66, 6.150's frames, `FrameRules.lean`). The register must be threaded through each
  of them, and their soundness re-proved with open lends present. That soundness is the open
  question, and nothing here settles it.
