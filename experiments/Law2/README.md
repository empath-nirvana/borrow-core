# Law2: a lend ended at a stop, re-lent at a fresh lifetime

Build with `lake build Law2`. It imports `Core`, `Restrat` and `GhostEnd`; the library does not
import it. There is no `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`,
and every result's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`. The only
`sorry` is the enumerated target (S1) of `Law2/Target.lean`; (S1′) is derived from it.

## The question

Law 2 (research/effects `synthesis.md` §10, `tier2-status.md`): a lend ended at a stop is re-lent
at a fresh lifetime beneath the resumer's list, and the suspended continuation `κ` is related at
that lifetime — at every borrow-nesting depth, as one result.

GhostEnd built the lender side: 6.65 and 6.64 at a resuming table (`ewpTS_M_frameR`,
`ewpTS_I_frameR`), D16.1's stacked piece `OpenS`, and one commutation step per kind of lend at
every stack (`StackStep.lean`). The κ side is what a borrower owes the piece: at every stop of
every run, the continuation runs again at every re-lend of the stack, handed the views made
afresh.

## Summary

| what | outcome | Lean |
|---|---|---|
| lenders, every mixed stack | **proved**, one induction on the stack | `fold_mixed` |
| bridge: stops at any context to the piece | **proved** | `openS_of_stops`, `stopAt_of_perform` |
| stacked bind: frame frozen at stops, thawed at re-lends | **proved**, induction on the piece | `bodyS_bind`, `openS_bind` |
| re-lendable values and contexts | **closed under re-lend, split, `Ext`** | `RSlot`, `RCtx`, `rslot_relendable` |
| piece judgment at the computation forms | **proved**, one lemma per form | `pj_let`, `pj_case`, `pj_call`, … |
| (S1) at a fragment of Core's typing | **proved**, induction on the derivation | `BComp.toPJ`, `piece_of_bcomp` |
| Law 2 at the fragment, every mixed stack | **proved** | `law2_frag` |
| (S1) for every derivation | **not derived beyond the fragment**; no obstruction verified | `piece_of_typed` |
| (S1′) at one lend | **from (S1)**; at the fragment with no open step | `relendOfTyped'`; `relend_frag` |
| hard cases, every hypothesis discharged | **proved** at depth 2 and a depth-3 reborrow chain | `branch_spans`, `loop_spans`, … |
| a handler installed inside the borrower | **not derived**; no obstruction verified | (S1)'s docstring |
| machine-step subject reduction | **not built**; the invariant is derivation-indexed | `PJ`, `BComp` |
| probe 4's verifier minors | **applied** | below |

## The bridge (`Law2/Bridge.lean`)

`openS_of_run` and `openS_yield_ds` built the piece for one stop context, `.seq .hole rest`, the
stop the run's first configuration. **`openS_of_stops`** is the general form: a run that, at every
re-lend below `αi` and handed the views, reaches an answer in `Q` or a stop of the table at
whatever context `K` the run reached (`StopAt`: the views it drops beside a part in `[top]` the
table admits, every continuation owed the piece again) is D16.1's piece. `stopAt_of_perform` builds
`StopAt` from a kernel `perform` stop; the ghost end is `stopS_of_full` with `ghostS_of_boxTop`.

**`openS_bind`** is the composition a borrower is built by: a pure context `K` around a piece, a
frame `Fr` beside it. At each unfolding the views split between the piece and the frame
(`vwS_split`) and the frame frozen at the last stop thaws at the re-lend (`hthaw`); one run is
`bodyS_bind`. At the inner piece's stops the frame freezes (`hfz`) into a part in `[top]` beside
the views it drops, the two drops join (`dropS_join`: one `mut` cell per entry, two `imm` cells
one), and the frozen frame joins every continuation inside the lenders' exits (`ghostS_frame`,
`opTable_frame`). By induction on the inner piece's `OpenS`, its continuations at the lifetimes
just ended; no step reads the stack's length.

**`relend_of_openS₁`**: at one `mut` entry, D16.1's piece is GhostEnd's single-lend `Relend`.

**`relend_not_emb`**: why the bridge is stated at the re-lent readings (`RunsAt`, `StopAt`) and not
through `KappaRelends`. `KappaRelends` quantifies over re-makings `θ : Restrat.Emb c`; on
`Life = ℕᵒᵈ` the re-lend `[7, 6]` of `[5, 3]` is one the piece is unfolded at (each lifetime below
the one it replaces, in nesting order), and no `Emb` realizes it: `4` would have to land strictly
between `7` and `6`.

## Re-lendable values, and the piece judgment (`Law2/Piece.lean`)

A frame held across a stop is frozen with the values it holds and thawed at the next re-lend. What
a value must satisfy is GhostEnd's `RelendableS`: its resource splits into the views it holds and a
part in `[top]` that, handed the views made afresh at any re-lend, is again in the relation.

**`RSlot σ A`** reads that along `A`'s shape: componentwise at `⊗` and `⊕` (each component
re-lends with its own share, so `let (x, y) =` can take a pair apart); at a closure that stops,
`U(A ⊸ F_Σ B)`, called at every re-lend on a re-lendable argument it is the piece; at `!A`, `A`'s
at `∅`; at every other type the kernel's relation at every re-lend. `RCtx` is `⊛` of `RSlot` over
a context. Proved: `rslot_relendable`/`rctx_relendable` (re-lendable as such: the frame of a
bind), `rctx_split` (along `SplitP`; a persistent slot holds nothing, `rslot_persistent_empty`),
`rslot_local`/`rctx_local`, `rslot_vC`/`rctx_gDenC` (the kernel's relation at the current
lifetimes, away from closures that stop), `rslot_of_frozen` (a value whose type reads none of the
stack's variables and whose resource is in `[top]` is re-lendable, frozen whole).

**`PJ`**, the piece judgment: at every lifetime vector of the stack whose re-lends model `Δ`, from
a re-lendable context, the term runs as D16.1's piece, its answer re-lendable. One lemma per form:

| form | lemma | how |
|---|---|---|
| a variable | `pj_var`, `pv_var` | the context's re-lendable value |
| pure code, answer frozen | `pj_pure`, `pv_frozen` | `fundamentalC` at the current lifetimes |
| `perform` at the row | `pj_perform` | argument by `fundamentalC`, in `[top]` by 6.60 |
| `M to x. N` | `pj_let` | `bodyS_bind` now, `openS_bind` at every continuation |
| `case`, `let (x, y) =`, `V; M` | `pj_case`, `pj_letpair`, `pj_seq` | the value taken apart |
| `()`, pairs, injections, `!E` | `pv_unit`, `pv_pair`, `pv_inj₁`, `pv_inj₂`, `pv_bangE` | componentwise |
| a closure that stops, built | `rslot_lamEff`, `pv_lamEff`, `pv_bangLamEff` | environment re-lendable; body's `PJ` |
| calling it | `pj_call` | its reading now, on the argument's |
| `bounded_fix` at the row | `rslot_fixSelf`, `rslot_boundedFix` | induction on the budget |

In `pj_let` the frame is `N`'s context, frozen by `rctx_relendable` and thawed by its own
re-lendability; in `rslot_lamEff` the closure's frozen share is its re-lendable environment.
`openS_of_pj`: the piece judgment, the context rebuilt re-lendably at every re-lend, gives
D16.1's piece (answers read at the stack's length, `openS_mono_Q_len`).

## (S1) at a fragment of Core's typing (`Law2/Fragment.lean`)

`BVal`/`BComp` is a sub-judgment of Core's typing (`BVal.toCDerives`, `BComp.toCDerives`, at a row
of linear operations): the derivations a borrower at a resuming row builds from the forms above.
`BComp.toPJ` is the piece judgment for every derivation of it, by one mutual induction. The hard
cases are its constructors: a frame holding a value computed before a stop (`letE`, over any
re-lendable frame), branches (`case`), loops (`boundedFix`, `call`), closures that stop (`lamEff`,
`bangLamEff`, `call`).

```lean
theorem piece_of_bcomp (hS : S ≠ []) (hx : AllCross σ (Row.tab S δ))
    (hLR : LinResume (Row.tab S δ)) (hd : BComp δ σ S Δ Γ M B) (hB : NoEffT B)
    (hQ : the answer in [top]) (hΔ : every re-lend below αi models Δ)
    (hctx : at every re-lend below αi the views rebuild the context re-lendably) :
    OpenS δ σ (Row.tab S δ) (cbQ δ σ Qa) σ.length ds αi [] ls (substAll γ M) PMap.empty
```

No case on the stack's depth or on its entries. `law2_frag` is Law 2 for the fragment at every
mixed stack (`fold_mixed` with `piece_of_bcomp`).

**Instances** (`Law2/FragInstances.lean`), every hypothesis discharged, no sorry. The program
derivations are stated at every stack; `law2_A` and `law2_C` discharge a stack's hypotheses once.

* `branch_spans`: `c = inj₂ (); yield 1; case c of inj₁ _ ⇒ use m | inj₂ _ ⇒ yield 2; use m` — a
  value computed before a stop held across it, and a stop inside a branch.
* `closure_stops_spans`: `f = λ_. yield 2; yield 1; f (); use m` — a closure that stops, built
  before a stop and called after it; the call stops inside the callee.
* `loop_spans`: `bounded_fix (step, (3, ())); use m`, the step yielding once per iteration — the
  view held in the frame across every iteration's stop.
* At depth 2, `[s@'x₂ reborrow, s@'x₁]`; at the depth-3 reborrow chain
  `[s@'x₃ reborrow, s@'x₂ reborrow, s@'x₁]`, `chain3_loop_spans` and `chain3_branch_spans`.

## Configuration typing: where the split and the measure come from

The plan was subject reduction for the effect machine: typed configurations preserved by every
`Step`, so that at every stop the captured `κ` is a typed segment over `HTV` values. What `OpenS`
needs from a stop is two things, and a machine-step typing supplies neither on its own:

* **the split.** The frame-by-frame re-lend needs to know which part of the stop's share each
  frame's values hold. The run's relation states the continuation's share as one wand
  (`contShare`); `HTV`/`HTG` at a resource is a statement about that split, which a syntactic
  typing of the configuration does not make.
* **the measure.** `OpenS` is a least fixed point over stops, its unfoldings at fresh lifetimes.
  The kernel's `ewpTS` at the lifetimes a run started at does not reach a re-lent run (§15's route
  1, `refoldKripke_false`), so an induction over runs at one reading does not close; a per-stop
  invariant gives the next stop's continuation, not a well-founded tree of them.

The derivation-indexed invariant supplies both, as GhostEnd's `Open` induction did for one lend:
a configuration is a stack of frames, each typed by a sub-derivation, its context re-lendable
(`RCtx`), and the measure is the derivation, with `openS_bind`'s induction on the inner piece for
the stops. So configuration typing is realised as `PJ` with `BComp`: "every step preserves
typedness" is `bodyS_bind`/`openS_bind` through the frames and the β-, `case`-, `letpair`- and
`boundedFix`-steps in the compatibility lemmas; "at every stop `κ` re-lends" is every stop's
continuation being `OpenS`. Machine-step subject reduction over `Step`, `catch_cell`,
`kappaC_resume`/`cancel` and `fwd_resume` is not built; the machine steps of a handler installed
inside the borrower are the open case below.

## Law 2's remaining sorry list

* **(S1) `piece_of_typed`** (`Law2/Target.lean`): a borrower Core's typing derives is D16.1's
  piece. Proved for the fragment (`piece_of_bcomp`); it reduces to `PJ` at every derivation
  (`openS_of_pj`). Not derived, no obstruction verified, for:
  * a pure computation whose answer is not frozen — a view, or a closure over one, returned by a
    pure call; `Mut`/`Imm` at a stack variable, an arrow or a `∀` held across a stop. Its answer
    has to be re-lendable, which the kernel's fundamental property does not record; at first-order
    types this is GhostEnd's `lok_thaws` at a stack (the table `TabAtS`, `↭` keeping each view's
    place and lifetime);
  * **a handler installed inside the borrower**: the stops of the operations it handles cross no
    lend (depth `0`), and `PJ` reads full-depth stops only (`AllCross`); the handler frame passing
    the lenders' stops and catching the inner ones at the stacked piece (GhostEnd #278) is not
    built;
  * `[then]`, `∀I`/`∀E` and `&` at a row, `[sub]` widening the row, a closure that stops handed to
    pure code (`CtxNoEffT`), and a context given as one `𝒢⟦Γ⟧` at each re-lend rather than slot by
    slot (`RCtx`).

(S1′) is not a separate sorry: `relendOfTyped'` derives `RelendOfTyped'` from (S1) at the
one-entry stack, and `law2_depth1` goes through it. `RelendOfTyped'` is GhostEnd's
`RelendOfTyped` with the lend's bound `@bδ` defined, the hypothesis GhostEnd's own
`relendOfTyped_of_rbodyOfTyped` adds: at an undefined bound no reading models `Δ, x ⊏ b`, and the
derivation constrains no run. `law2_depth1` carries it; at a program's `withbor` the bound is
`⊓Δ` (`meetOfDom`), defined at every reading that models `Δ` (`interp_defined_of_wf`). At the
fragment, `relend_frag` and `law2_depth1_frag` have no open step.

## The components from the previous round

* `fold_mixed` (`Mixed.lean`): D16.1's piece at a mixed stack (`mut` lends of distinct places,
  `imm` lends, `mut` reborrows of the next entry's place), every stop crossing every entry, beside
  the owners of the entries that are not reborrows, is its `ewpTS`. One induction on the stack.
  Scope: an entry's payload type may not mention the stack's own variables; a reborrow of an `imm`
  view is not a kind of entry.
* `law2_straight` (`Straight.lean`): Law 2 for `yield y₁; …; yield yₙ; E`, the continuation by
  `runsAt_of_typed`; `struct_reborrow_spans`, `struct_imm_spans` (a mixed 3-stack: an `imm` lend of
  another place inside a reborrow), `closure_reborrow_spans` (`Instances.lean`).
* `kappa_relend`, `htv_relend` (`Kappa.lean`, `Hereditary.lean`): a typed segment over an `HTG`
  context re-lends at every re-making `θ : Restrat.Emb c`. These are the re-make form; Law 2 as
  proved reads re-lends directly (`relend_not_emb`), and `HTV` is a hypothesis where used.
* `tw_remake` (`World.lean`): a re-make of a typed world is a typed world, for worlds whose
  re-made part holds no `imm` cell. Not used by Law 2 as proved: the piece re-lends inside the
  lenders' steps, which build typed worlds with `TW`'s constructors.
* `relend_all`, `relend_ret` (`AllF.lean`): `∀` and `F` for derived terms, by the fundamental
  property at the moved reading.

## Probe 4's verifier minors

* An honest depth-3 instance: the reborrow chain `[s@'x₃ reb, s@'x₂ reb, s@'x₁]`,
  `chain3_loop_spans` and `chain3_branch_spans` (`law2_C`), corollaries of `law2_frag`.
* "Any nesting depth" scoped: the lender side at every mixed stack; the κ side for the fragment
  and straight-line borrowers at every mixed stack; (S1) beyond them open. This README's title and
  `Target.lean`'s docstrings say so.
* `tw_remake` labelled: no `imm` cell in the re-made part, and not connected to the piece
  (`World.lean`).
* `Kappa.lean`'s dangling `KappaTypedAtStop` reference replaced by what is and is not derived.
* `closure_reborrow_spans`: the two-entry stack, the program started in the state after the
  closure is built (`Instances.lean`); `closure_stops_spans` builds the closure before the stop.
* `HTV` described as a predicate on values and a hypothesis where used (`Hereditary.lean`).

## What is open

* **(S1) beyond the fragment** — the list above. The two with the most reach: a handler installed
  inside the borrower (depth-`0` stops, #278), and pure code answering re-lendable non-frozen
  values (the first-order case is `lok_thaws` at a stack).
* **An inner lend whose payload reads the stack's own variables** (a borrow of a borrow opened
  inside the region): the lender step for such an entry is not built (GhostEnd's views read
  payloads at `δ`).
* 6.150 at a resuming table (a reborrow of an `imm` view spanning a stop); a typed continuation
  over an `Imm` view; a stop handled between two lenders (`AllCross` beyond constant `true`,
  #278); the borrow constants' frames as machine frames at a stack (#275).
* At the program level, nested lends spanning a stop are not typable in Core today (no borrow
  constant at a resuming row): `law2_depth1`/`law2_depth1_frag` are the program-level forms, and
  `law2`/`law2_frag` the any-depth forms at the level of the lenders' ghost state.

Kill criterion: not met. No step failed in a machine-checked configuration, and no step needed two
successive patches.

## Files

| file | content |
|---|---|
| `Law2/Remake.lean` | `RemakeR`; `relend_fov`, `relend_mut` at Core; `relend_derivable` |
| `Law2/Hereditary.lean` | `HTV`, `HTG`; `htv_sound`; `htv_relend`, `htv_relend_vC` |
| `Law2/Kappa.lean` | `TypedSeg`, `KappaRelends`; `kappa_relend`, `kappaRelends_of_typed` |
| `Law2/AllF.lean` | `relend_all`, `relend_ret`, `htv_relend_all`, `htv_relend_ret` |
| `Law2/World.lean` | `RemakeAt`, `tw_cell`, `tw_remakeAt`, `tw_remake`, `ti_remake` |
| `Law2/Mixed.lean` | `MixedStack`, `ownersM`, `withOwnersM`; `fold_mixed` |
| `Law2/Straight.lean` | `RunsAt`; `openS_of_run`, `openS_yield_ds`, `runsAt_of_typed`, `law2_straight` |
| `Law2/Bridge.lean` | `openS_of_stops`; `bodyS_bind`, `openS_bind`; `relend_of_openS₁`; `relend_not_emb` |
| `Law2/Piece.lean` | `RSlot`, `RCtx`; re-lendability, split, frozen values; `PJ`, `PV`; `openS_of_pj` |
| `Law2/Fragment.lean` | `BVal`, `BComp`; `toCDerives`, `toPJ`; `piece_of_bcomp`, `law2_frag` |
| `Law2/Instances.lean` | `struct_reborrow_spans`, `struct_imm_spans`, `closure_reborrow_spans` |
| `Law2/FragInstances.lean` | `branch_spans`, `closure_stops_spans`, `loop_spans`, `chain3_*` |
| `Law2/Target.lean` | (S1) `piece_of_typed`, `law2`; `relendOfTyped'`, `law2_depth1`; `relend_frag` |
