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
| stops inside the borrower beside the lenders' | **defined**; D16.1's piece where none occurs | `OpenH`, `openS_of_openH` |
| stacked bind: frame frozen at the lenders' stops, live at stops inside | **proved**, induction on the piece | `bodyH_bind`, `openH_bind` |
| re-lendable values and contexts | **closed under re-lend, split, `Ext`** | `RSlot`, `RCtx`, `rslot_relendable` |
| piece judgment at the computation forms | **proved**, one lemma per form | `pj_let`, `pj_case`, `pj_call`, … |
| a handler installed inside the borrower | **proved** at linear operations | `pj_handle`, `pj_resume` |
| (S1) at a fragment of Core's typing | **proved**, induction on the derivation | `BComp.toPJ`, `piece_of_bcomp` |
| Law 2 at the fragment, every mixed stack | **proved** | `law2_frag` |
| (S1) for every derivation | **not derived beyond the fragment**; no obstruction verified | `piece_of_typed` |
| (S1′) at one lend | **from (S1)**; at the fragment with no open step | `relendOfTyped'`; `relend_frag` |
| hard cases, every hypothesis discharged | **proved** at depth 2 and a depth-3 reborrow chain | `branch_spans`, `handler_spans`, … |
| machine-step subject reduction | **not built**; the invariant is derivation-indexed | `PJ`, `BComp` |
| probe 4's verifier minors | **applied** | below |

## The bridge (`Law2/Bridge.lean`)

`openS_of_run` and `openS_yield_ds` built the piece for one stop context, `.seq .hole rest`, the
stop the run's first configuration. **`openS_of_stops`** is the general form: a run that, at every
re-lend below `αi` and handed the views, reaches an answer in `Q` or a stop of the table at
whatever context `K` the run reached (`StopAt`: the views it drops beside a part in `[top]` the
table admits, every continuation owed the piece again) is D16.1's piece. `stopAt_of_perform` builds
`StopAt` from a kernel `perform` stop; the ghost end is `stopS_of_full` with `ghostS_of_boxTop`.

**`relend_of_openS₁`**: at one `mut` entry, D16.1's piece is GhostEnd's single-lend `Relend`.

**`relend_not_emb`**: why the bridge is stated at the re-lent readings (`RunsAt`, `StopAt`) and not
through `KappaRelends`. `KappaRelends` quantifies over re-makings `θ : Restrat.Emb c`; on
`Life = ℕᵒᵈ` the re-lend `[7, 6]` of `[5, 3]` is one the piece is unfolded at (each lifetime below
the one it replaces, in nesting order), and no `Emb` realizes it: `4` would have to land strictly
between `7` and `6`.

## Stops inside the borrower, and the stacked bind (`Law2/Inner.lean`)

A handler installed inside the region the lends span catches some operations: those stops cross
no lend and drop no view. The handler's clause is handed the continuation and may hold it across
later stops of the lenders' row, at which every view is dropped; so the continuation must be
re-lendable as a closure is, its share split up front into the views it holds and a part in
`[top]`. GhostEnd's `stopS` at depth `0` splits the share on each answer (`RelendableN` inside the
table's continuation), which a clause holding the continuation across a lenders' stop cannot
freeze; so these stops are read separately:

* **`InStop`**: `perform (n, (i, v))` at an operation caught inside (`RI n i = some P`): the
  argument in `P.1`, the continuation's share `RelendableS`, at every re-lend and on every answer
  in `P.2` the piece at depth `0`.
* **`bodyH`, `OpenH`**: D16.1's piece with `InStop` beside the lenders' full-depth stops
  (`StopAt`). Where nothing is caught inside it is D16.1's (`openS_of_openH`).
* **`bodyH_bind`, `openH_bind`**: a pure context `K` around a piece, a frame `Fr` beside it, its
  share split into views and a frozen part (`hfz`) that thaws at every re-lend (`hthaw`). At a
  full-depth stop the frame's views are dropped beside the piece's (`dropS_join`: one `mut` cell per
  entry, two `imm` cells one) and its frozen part joins every continuation inside the lenders'
  exits (`opTable_frame`); at a stop inside, the whole frame joins the continuation, re-lendable
  (`relendableS_sep`). `openH_bind` is one induction on the inner piece with a two-part motive:
  the frame frozen at the full-depth continuations, live at the depth-`0` ones.

## Re-lendable values, and the piece judgment (`Law2/Piece.lean`)

What a value held across a stop must satisfy is GhostEnd's `RelendableS`: its resource splits into
the views it holds and a part in `[top]` that, handed the views made afresh at any re-lend, is
again in the relation.

**`RSlot σ S₀ A`** reads that along `A`'s shape, `S₀` the lenders' row: componentwise at `⊗` and
`⊕` (each component re-lends with its own share, so `let (x, y) =` can take a pair apart); at a
closure that stops, `U(A ⊸ F_Σ B)`, called at every re-lend on a re-lendable argument it is the
piece; at a continuation a clause is handed, `U((B ⊸ F_Σ R) & ⊤)`, resumed at every re-lend on a
re-lendable answer it is the piece; at `!A`, `A`'s at `∅`; at every other type the kernel's
relation at every re-lend. The piece at a row `Σ` is `OpenH` with the lenders' table and `RIn`:
the operations of `Σ` whose names are not `S₀`'s are caught inside, their argument and answer types
read by `RSlot`. `RCtx` is `⊛` of `RSlot` over a context. Proved: `rslot_relendable`/
`rctx_relendable` (re-lendable as such: the frame of a bind), `rctx_split` (along `SplitP`; a
persistent slot holds nothing, `rslot_persistent_empty`), `rslot_local`/`rctx_local`,
`rslot_vC`/`rctx_gDenC` (the kernel's relation at the current lifetimes, away from closures that
stop and continuations), `rslot_of_frozen` (a value whose type reads none of the stack's variables
and whose resource is in `[top]` is re-lendable, frozen whole).

**`PJ`**, the piece judgment: at every lifetime vector of the stack whose re-lends model `Δ`, from
a re-lendable context, the term runs as the piece, its answer re-lendable. One lemma per form:

| form | lemma | how |
|---|---|---|
| a variable | `pj_var`, `pv_var` | the context's re-lendable value |
| pure code, answer frozen | `pj_pure`, `pv_frozen` | `fundamentalC` at the current lifetimes |
| `perform` at the lenders' row | `pj_perform` | argument by `fundamentalC`, in `[top]` by 6.60 |
| `perform` caught inside | `pj_performIn` | argument re-lendable, continuation holding nothing |
| `M to x. N` | `pj_let` | `bodyH_bind` now, `openH_bind` at every continuation |
| `case`, `let (x, y) =`, `V; M` | `pj_case`, `pj_letpair`, `pj_seq` | the value taken apart |
| `()`, pairs, injections, `!E` | `pv_unit`, `pv_pair`, `pv_inj₁`, `pv_inj₂`, `pv_bangE` | componentwise |
| a closure that stops, built | `rslot_lamEff`, `pv_lamEff`, `pv_bangLamEff` | environment re-lendable; body's `PJ` |
| calling it | `pj_call` | its reading now, on the argument's |
| resuming a continuation | `pj_resume` | its reading now, on the answer's |
| `bounded_fix` at the row | `rslot_fixSelf`, `rslot_boundedFix` | induction on the budget |

In `pj_let` the frame is `N`'s context, split by `rctx_relendable` and thawed by its own
re-lendability; in `rslot_lamEff` the closure's frozen share is its re-lendable environment.
`openS_of_pj`: the piece judgment at a row nothing of which is caught inside, the context rebuilt
re-lendably at every re-lend, gives D16.1's piece (answers read at the stack's length,
`openH_mono_Q`).

## A handler installed inside the borrower (`Law2/Handle.lean`)

`handle_n e with (h_ret, hs)`, `n` a name of neither the lenders' row nor the row outside, its
operations linear, `e` at the handler's row ahead of the row outside:

* **`bodyH_handle`**: one run of `hnd H e`. An answer of `e` runs `h_ret` on it, re-lendable. A
  stop of the lenders' row, and a stop caught by a handler further out, pass `hnd H` outward,
  reinstalled in their continuations and dead in their cancel runs (`opTable_handle`). A stop at
  `n` steps to the clause (`[op]`), handed the argument and `κ` at a fresh cell
  (`wpG_kappaCell`).
* **`rslot_kappaC`**: that `κ` is re-lendable at `kTy`. Its share is the continuation's, which the
  stop already split into views and a frozen part, beside its cell, owned and in every stratum.
  Resumed at a re-lend on a re-lendable answer it frees the cell and runs `hnd H K[w]`
  (`wpG_kappaC_resume`), the piece there.
* **`openH_handle`**: the same at every continuation, by induction on `e`'s piece, below the
  vector the handler was installed at.
* **`pj_handle`**: the piece judgment for `handle_n e with H`, `H` a value form over a context whose
  live slots are persistent. `H`'s value is read off the world the run starts in
  (`wpTS_val_post`), as the kernel's `handleV_compatC` does; its clauses hold nothing and are
  re-lendable at every re-lend (`relendableS_empty`).

The clause may hold `κ` across stops of the lenders' row: `κ` is a value of its context like any
other, its views dropped at each stop and handed afresh at the next re-lend.

## (S1) at a fragment of Core's typing (`Law2/Fragment.lean`)

`BVal`/`BComp` is a sub-judgment of Core's typing (`BVal.toCDerives`, `BComp.toCDerives`, at rows
of linear operations), the lenders' row `S₀` a parameter and the row a derivation is at an index:
the derivations a borrower builds from the forms above, with `performIn`, `resume` and `handle`
(Core's `effHandleV`) for a handler inside. `BComp.toPJ` is the piece judgment for every
derivation of it, by one mutual induction. The hard cases are its constructors: a frame holding a
value computed before a stop (`letE`, over any re-lendable frame), branches (`case`), loops
(`boundedFix`, `call`), closures that stop (`lamEff`, `bangLamEff`, `call`), a handler inside the
borrower whose clause holds the continuation across the lenders' stops (`handle`, `resume`).

```lean
theorem piece_of_bcomp (hS : S₀ ≠ []) (hx : AllCross σ (Row.tab S₀ δ))
    (hLR : LinResume (Row.tab S₀ δ)) (hd : BComp δ σ S₀ S₀ Δ Γ M B) (hB : NoEffT B)
    (hQ : the answer in [top]) (hΔ : every re-lend below αi models Δ)
    (hctx : at every re-lend below αi the views rebuild the context re-lendably) :
    OpenS δ σ (Row.tab S₀ δ) (cbQ δ σ Qa) σ.length ds αi [] ls (substAll γ M) PMap.empty
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
* `handler_spans`: `handle (tick (); yield 1; use m) with {x ↦ x; tick (u, κ) ↦ yield 2; κ u}` — a
  handler inside the region: `tick` is caught inside, crossing no lend; its clause yields to the
  lenders holding `κ`, which holds the view `m`; `κ` is resumed at the re-lend, yields again
  through the handler, and uses `m`.
* At depth 2, `[s@'x₂ reborrow, s@'x₁]`; at the depth-3 reborrow chain
  `[s@'x₃ reborrow, s@'x₂ reborrow, s@'x₁]`, `chain3_loop_spans`, `chain3_branch_spans` and
  `chain3_handler_spans`.

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
(`RCtx`), and the measure is the derivation, with `openH_bind`'s and `openH_handle`'s inductions on
the inner piece for the stops. So configuration typing is realised as `PJ` with `BComp`: "every
step preserves typedness" is `bodyH_bind`/`openH_bind` through the pure frames, `bodyH_handle`/
`openH_handle` through a handler frame, and the β-, `case`-, `letpair`- and `boundedFix`-steps in
the compatibility lemmas; "at every stop `κ` re-lends" is every stop's continuation being the
piece, and a continuation a clause is handed being re-lendable (`rslot_kappaC`). Machine-step
subject reduction over `Step` itself is not built.

## Law 2's remaining sorry list

* **(S1) `piece_of_typed`** (`Law2/Target.lean`): a borrower Core's typing derives is D16.1's
  piece. Proved for the fragment (`piece_of_bcomp`), a handler inside the borrower among it; it
  reduces to `PJ` at every derivation (`openS_of_pj`). Not derived, no obstruction verified, for:
  * a pure computation whose answer is not frozen — a view, or a closure over one, returned by a
    pure call; `Mut`/`Imm` at a stack variable, an arrow or a `∀` held across a stop. Its answer
    has to be re-lendable, which the kernel's fundamental property does not record; at first-order
    types this is GhostEnd's `lok_thaws` at a stack (the table `TabAtS`, `↭` keeping each view's
    place and lifetime);
  * a handler inside the borrower at an affine, unrestricted or abortive operation: `κ` may be
    dropped or copied, and an abortive operation's stop is a `raise` the handler unwinds to;
  * `[then]`, `∀I`/`∀E` at a row, `&` at a row other than a continuation's resume, `[sub]`
    widening the row, a closure that stops handed to pure code (`CtxNoEffT`), and a context given
    as one `𝒢⟦Γ⟧` at each re-lend rather than slot by slot (`RCtx`).

(S1′) is not a separate sorry: `relendOfTyped'` derives `RelendOfTyped'` from (S1) at the
one-entry stack, and `law2_depth1` goes through it. `RelendOfTyped'` is GhostEnd's
`RelendOfTyped` with the lend's bound `@bδ` defined, the hypothesis GhostEnd's own
`relendOfTyped_of_rbodyOfTyped` adds: at an undefined bound no reading models `Δ, x ⊏ b`, and the
derivation constrains no run. `law2_depth1` carries it; at a program's `withbor` the bound is
`⊓Δ` (`meetOfDom`), defined at every reading that models `Δ` (`interp_defined_of_wf`). At the
fragment, `relend_frag` and `law2_depth1_frag` have no open step.

## The components from the previous rounds

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
  `chain3_loop_spans`, `chain3_branch_spans` and `chain3_handler_spans` (`law2_C`), corollaries of
  `law2_frag`.
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

* **(S1) beyond the fragment** — the list above. The one with the most reach: pure code answering
  re-lendable non-frozen values (the first-order case is `lok_thaws` at a stack).
* **An inner lend whose payload reads the stack's own variables** (a borrow of a borrow opened
  inside the region): the lender step for such an entry is not built (GhostEnd's views read
  payloads at `δ`).
* 6.150 at a resuming table (a reborrow of an `imm` view spanning a stop); a typed continuation
  over an `Imm` view; a stop handled between two lenders (`AllCross` beyond constant `true`,
  #278 — a handler inside every lender is the case built here); the borrow constants' frames as
  machine frames at a stack (#275).
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
| `Law2/Bridge.lean` | `StopAt`, `openS_of_stops`; `dropS_join`; `relend_of_openS₁`; `relend_not_emb` |
| `Law2/Inner.lean` | `InStop`, `bodyH`, `OpenH`; `openS_of_openH`; `bodyH_bind`, `openH_bind` |
| `Law2/Piece.lean` | `RSlot`, `RIn`, `RCtx`; re-lendability, split, frozen values; `PJ`, `PV`; `openS_of_pj` |
| `Law2/Handle.lean` | `rslot_kappaC`, `opTable_handle`; `bodyH_handle`, `openH_handle`, `pj_handle` |
| `Law2/Fragment.lean` | `BVal`, `BComp`; `toCDerives`, `toPJ`; `piece_of_bcomp`, `law2_frag` |
| `Law2/Instances.lean` | `struct_reborrow_spans`, `struct_imm_spans`, `closure_reborrow_spans` |
| `Law2/FragInstances.lean` | `branch_spans`, `closure_stops_spans`, `loop_spans`, `handler_spans`, `chain3_*` |
| `Law2/Target.lean` | (S1) `piece_of_typed`, `law2`; `relendOfTyped'`, `law2_depth1`; `relend_frag` |
