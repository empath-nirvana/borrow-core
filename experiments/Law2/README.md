# Law2: a lend ended at a stop, re-lent at a fresh lifetime, at any nesting

Build with `lake build Law2`. It imports `Core`, `Restrat` and `GhostEnd`; the library does not
import it. There is no `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`,
and every result's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`. The only
`sorry`s are the two enumerated target statements of `Law2/Target.lean`, (S1) and (S1′) below.

## The question

Law 2 (research/effects `synthesis.md` §10, `tier2-status.md`): a lend ended at a stop is re-lent
at a fresh lifetime beneath the resumer's list, and the suspended continuation `κ` is related at
that lifetime — at every borrow-nesting depth, as one result.

What was established before (`experiments/DenseCarrier/README.md`, *Re-lending*, *Law 2*): moving a
region's cells (stored predicates carried to their image, `θ.relRU`) breaks the relation; re-making
them works at every first-order type at any depth; at `U` re-lending fails pointwise from room, and
every term the fundamental property relates re-lends at every type. So the invariant at `U` is how
the configuration was built: the typed-world pattern. `GhostEnd` built the lender side: 6.65 and
6.64 at a resuming table (`ewpTS_M_frameR`, `ewpTS_I_frameR`), the stacked piece `OpenS` and one
commutation step per kind of lend at every stack (`StackStep.lean`). Open there: the κ side (OQ-8),
GFP's induction.

## Results

| deliverable | outcome | Lean |
|---|---|---|
| 1. typed-world step | **proved**, no new step | `tw_remake`, `ti_remake` |
| 2. κ re-lends | **proved for typed continuations**; at an arbitrary stop of a typed borrower **not derived** | `kappa_relend`, `htv_relend`, `runsAt_of_typed`; (S1) |
| 3. mixed stacks | **proved**, one induction on the stack | `fold_mixed` |
| 4. `∀` and `F` | **proved** for derived terms and typed continuations; pointwise not derived | `relend_all`, `relend_ret`, `htv_relend_all`, `htv_relend_ret` |
| 5. assembly | Law 2 stated, one open step; proved for straight-line borrowers at every mixed stack | `law2`, `law2_depth1`; `law2_straight`; instances |
| 6. probe 3's minors | applied; the `mmm` closure instance added | `DenseCarrier/README.md`; `closure_captures_mmm` |

### 1. The typed world is closed under the ghost end and the re-make

The resume re-makes the region: each `mut` cell at its moved lifetime, its witness re-made cell by
cell, storing the predicate the moved reading asks for (`RemakeR`, `Remake.lean`). `tw_remake`: **a
re-make of a typed world is a typed world**, by the typed world's own steps. The re-make of one cell
is Law 2's pair — the lend ended at the stop as 6.65's exit ends it (`TW.mutUnfold`), the witness
re-made, the lend made afresh at the moved lifetime as 6.65's entry makes it (`TW.mutFold`, any
stored predicate). No constructor is added to `TW`, so `TI` holds of the re-made world by `TW.inv`
(`ti_remake`): the "one preservation lemma" is the existing steps'.

Depth is the cells' nesting. A witness lies strictly above its cell, so its cells are at lower
levels (distance below `⊤`); `tw_remakeAt` is one induction on a level bound and inside it one on
the locations re-made, each cell's witness re-made by the hypothesis between its unfold and its
fold (`tw_cell`). The validity each step asks for is `[TR]` 6.24 (`ResU.six24`): valid with a `mut`
cell exactly when valid with it unfolded, whatever its lifetime and predicate. No case on depth.

Scope: `RemakeR` has no `imm` case, so `tw_remake` is for worlds holding no `imm` cell. Re-making an
`imm` lend (6.64's records, re-slotted) is not derived.

### 2. κ re-lends

**The property a resume needs** (`KappaRelends`, `Kappa.lean`): at every re-making `θ` of the
region (every lend the stop ended, moved by one order embedding, at any depth), the share of `κ` has
a re-make at which `κ`, plugged with any answer related at the moved reading, is related at the
moved reading. It is, for a continuation, the `∀'x` a borrow constant reads its callback at
(`withbor2_compatX` instantiates the callback's own clause at 6.65's fresh `α`).

**Proved for typed continuations, frame by frame:**

* `relend_fov`, `relend_derivable` (`Remake.lean`): Core's relation re-lends at every first-order
  type at any depth, and every term Core's typing derives over a first-order context re-lends at
  every computation type — DenseCarrier's `relend_fov` and `core_relend_derivable` proved at Core's
  `vC` directly.
* `htv_relend`, `htv_relend_vC` (`Hereditary.lean`): **closures a typed program builds re-lend,
  hereditarily**. `HTV` records how a value was built (a first-order value, a pair, or a thunk whose
  body Core's typing derives, closed by such values); at every re-making it has a re-make that is
  again `HTV` at the moved reading, the closure case by the derivation's own `⟦Δ⟧` at the moved
  reading. This is the hereditary `semD_relend` DenseCarrier left unbuilt.
* `kappa_relend`, `kappaRelends_of_typed` (`Kappa.lean`): **a typed segment re-lends** —
  `K[w] = E[w/z, γ]` for `E` Core's typing derives, `γ` hereditarily typed — at every re-making:
  the context re-lends and the fundamental property relates `E` at the moved reading.
  `relend_derivable` extended from closed terms to plugged contexts, and from first-order contexts to
  closures.
* `runsAt_of_typed` (`Straight.lean`): the same at the stacked readings: a continuation Core's
  typing derives runs at every re-lend of a lend stack, its context rebuilt from the views the
  lenders make afresh.

**Not derived: that the continuation captured at an arbitrary stop of a typed borrower is such a
segment, with its share split as the segment's context** — (S1) below. The run's relation gives the
continuation only through `contShare`, whose share is existential: it does not record which part of
the share each frame's values hold, and the frame-by-frame argument needs exactly that split. In
the fundamental property's proof the split is there (each frame's context is framed off during the
run before it), so the step is an induction over typing at a relation that keeps it: GFP at the
stacked relation (GhostEnd's `GFP`), or `RBodyOfTyped` at one lend. At nesting depth two or more
the continuation holds lenders' frames, and re-lending such a frame is 6.65 at a resuming table for
the inner callback, which needs the inner continuation re-lendable at every later stop
(`stack_step_other`'s hypothesis is the inner piece `OpenS`): the one-resume statement at depth `n`
is the full statement at depth `n − 1`, so (S1) is one fixed point, not a sequence of resumes. No
obstruction verified: no configuration arising from a typed program is known where `κ` is related
at the old lifetime and not re-lendable.

### 3. Mixed stacks

`fold_mixed` (`Mixed.lean`): D16.1's piece at a **mixed stack** (`MixedStack`: `mut` lends of
distinct places, `imm` lends, and `mut` reborrows of the next entry's place, in any order), every
stop crossing every entry, beside the owners of the entries that are not reborrows (`ownersM`), is
its `ewpTS`, the owners handed back (`withOwnersM`). One induction on the stack, each entry folded
by its own GhostEnd step (`stack_step_other`, `stack_step_imm`, `stack_step_reborrow`); the
induction carries the piece at every `Ext`-extension of the list, which the `imm` step asks for and
the other two keep. No case on depth. It generalises `fold_other` (`mut` lends of distinct places
only).

Scope: GhostEnd's views read each entry's payload at the outer reading `δ`, so an entry's payload
type may not mention the stack's own variables; a reborrow of an `imm` view (6.150 at a resuming
table) is not a kind of entry.

### 4. `∀` and `F`

Probe 3 left `RelendC` open at `∀` (one re-make has to serve every instance, gap ones included)
and at `F` (the `wpTS` frames of the moved world have to be sent back). For terms Core's typing
derives and typed continuations, neither is asked: the fundamental property is applied at the
moved reading, whose `∀` ranges over every instance of the moved reading and whose `wpTS` over every
frame of the moved world, after the one re-make is chosen. `relend_all`, `relend_ret`
(`AllF.lean`); for closures a typed program builds, `htv_relend_all`, `htv_relend_ret`. Pointwise,
at every configuration the relation relates: not derived, no obstruction verified.

### 5. Law 2

```lean
theorem law2 {S : Row} (hLR : LinResume (Row.tab S δ)) (hL : (Row.tab S δ).Local) {β : Life}
    {σ : LStack} (hσ : MixedStack σ) (hS : ∀ e ∈ σ, Row.Resume S e.x)
    (hx : AllCross σ (Row.tab S δ)) (hP …) (hadm …) (hQa …)
    (hds …) (hbs …) (hβ …) {Δ Γ M B} (hd : CDerives Δ Γ M (.comp (CTy.effOf S B))) {γ}
    (hctx : at every re-lend of σ, the context rebuilt from the views)
    (hQ : the answer in [top]) (ls : List SRec) :
    Entails (ownersM δ σ ls)
      (ewpTS ls (substAll γ M) (opTable (Row.tab S δ)) (withOwnersM δ σ Qa))
```

A borrower Core's typing derives at a resuming row, holding a mixed stack of lends open across its
stops: beside the owners of the stack's lenders it is its `ewpTS`, the owners handed back with its
answer. The row is `Row.Resume` at every lend's variable: linear operations answered at `1` whose
arguments are closed data outliving every lifetime, so no lend escapes in a payload (lending
iterators are outside). Proof: `fold_mixed` (deliverable 3) applied to the borrower's piece.

**Enumerated sorries** (`Law2/Target.lean`, the only ones in the library):

* **(S1) `piece_of_typed`**: a borrower Core's typing derives is D16.1's piece at its stack — the κ
  side at every stop of every run. Not derived; no obstruction verified.
* **(S1′) `relendOfTyped`**: GhostEnd's `RelendOfTyped`, the same at one lend in GhostEnd's
  single-lend form, the open step of `law2_depth1` (the program-level resume rule's compatibility,
  `withbor ℓ (Λ. λm. M)` at `F_S (Ref T ⊗ B)`, GhostEnd's `withbor_of_relendOfTyped`).

**Which deliverable discharged which step.** The lenders' ghost end at every stop and re-lend at
every resume, at every mixed stack: deliverable 3 (`fold_mixed`). The κ side (S1): discharged for
straight-line borrowers by deliverable 2 — `law2_straight` proves Law 2 for
`yield y₁; …; yield yₙ; E` at every mixed stack with no sorry, the continuation by
`runsAt_of_typed`. The re-made worlds are typed worlds: inside the lenders' steps by construction
(6.65 and 6.64 re-applied build them with `TW`'s constructors); for the region re-made at once
(`RemakeR`, the form deliverable 2's `kappa_relend` re-makes in), deliverable 1. The `∀` and `F`
rows of a continuation re-derived at the moved reading: deliverable 4's mechanism, the fundamental
property taken at the moved reading.

**Acceptance instances** (`Instances.lean`), corollaries of `law2_straight`, every hypothesis
discharged, no sorry:

* `struct_reborrow_spans` (depth 2): a struct holding a borrow `Mut 'b 1` of an outer place is lent
  and reborrowed; the generator yields with both lends open and uses the reborrow after the resume.
  Stack `[s@'x₂ reborrow, s@'x₁]`.
* `struct_imm_spans` (depth 3): the same with an `imm` lend of another place inside. Stack
  `[p@'x₃ imm, s@'x₂ reborrow, s@'x₁]`.
* `closure_reborrow_spans`: a closure capturing the nested borrow, built before the yield and
  forced after it; its context is rebuilt at each re-lend by the closure's hereditary typing
  (`HTV.thunkF`, `htv_sound`).
* The async-borrow shape (tasks over a borrowed list, awaited before the lend ends): **not in the
  proved class**. The tasks read the list through an `Imm` view, and the view a re-lend hands
  carries no record for the `Imm` clause's coherence `CohE`; a typed continuation over an `Imm` view
  is not given.

### 6. Probe 3's minors

`experiments/DenseCarrier/README.md`: §6's closing paragraph narrowed to moves carrying stored
predicates to their image (`θ.relRU`), with re-making named as the move that frees the same slots
and keeps the relation; "from nothing else" replaced by the resource quantifiers reading room at
every `L` (`not_reflect_boxMM`); `RemakeR` stated to re-make every cell of a resource. The instance
`closure_captures_mmm`: the thunk `λ_. return x` closed by a borrow of a borrow of a borrow re-lends
at `U (F mmm)` at every re-making, from `relend_derivable` (Core's `core_relend_derivable`).

On this branch DenseCarrier builds only up to `Faithful`, `Equivariance`, `Rat`, `Nominal` and
`Positioned` (two `CTy.eff` patterns of `Faithful` and `Equivariance` updated to the cancel row's
arity): `FL` and `Borrow` read the computation types from before the tier-1 cancel row, and `Gap`,
`Reslot` and every file after them import `ProbeD1`, which imports `Targets`, written against the
cancel payload that carried handler names. `GhostEnd.Arising` does not build either. Law2 imports
none of them; the re-lending it needs is proved again at Core's relation (`Remake.lean`).

## What is open

* **(S1)**: the κ side at every stop of a typed borrower, beyond straight-line ones — branching and
  loops around stops, closures that stop, frames holding values computed before a stop (the bind
  row: the frame's share has to be located, with the run's `↭` keeping each view's place and
  lifetime, GhostEnd's `wpG_tabAt`), handlers installed inside the borrower. GFP's induction.
* **An inner lend whose payload reads the stack's own variables** (a borrow of a borrow opened
  inside the region): the relation re-lends it (`relend_fov`, re-made witnesses) and the world does
  (`tw_remake`); the lender step for such an entry is not built (GhostEnd's views read payloads at
  `δ`).
* 6.150 at a resuming table (a reborrow of an `imm` view spanning a stop); a typed continuation over
  an `Imm` view (the re-lent record); a stop handled between two lenders (`AllCross` beyond constant
  `true`, GhostEnd #278); the borrow constants' frames as machine frames at a stack (#275), which
  connects `law2` to programs nesting borrow constants; re-making an `imm` cell in `tw_remake`.
* At the program level, nested lends spanning a stop are not typable in Core today (no borrow
  constant at a resuming row), so `law2_depth1` is the program-level form and `law2` the
  any-depth form at the level of the lenders' ghost state.

Kill criterion: not met. No step failed in a machine-checked configuration, and no step needed two
successive patches.

## Files

| file | content |
|---|---|
| `Law2/Remake.lean` | `RemakeR`; `relend_fov`, `strat_relend`, `relend_mut` at Core; `relend_gSepC`, `relend_derivable` |
| `Law2/Hereditary.lean` | `HTV`, `HTG`; `htv_sound`; `htv_relend`, `htv_relend_vC` |
| `Law2/Kappa.lean` | `TypedSeg`, `RelendsAt`, `KappaRelends`; `kappa_relend`, `kappaRelends_of_typed` |
| `Law2/AllF.lean` | `relend_all`, `relend_ret`, `htv_relend_all`, `htv_relend_ret` |
| `Law2/World.lean` | `RemakeAt`, `tw_cell`, `tw_remakeAt`, `tw_remake`, `ti_remake` |
| `Law2/Mixed.lean` | `MixedStack`, `ownersM`, `withOwnersM`; `fold_mixed` |
| `Law2/Straight.lean` | `RunsAt`; `openS_of_run`, `openS_yield_ds`, `openS_chain`, `runsAt_of_typed`, `law2_straight` |
| `Law2/Instances.lean` | `struct_reborrow_spans`, `struct_imm_spans`, `closure_reborrow_spans`, `closure_captures_mmm` |
| `Law2/Target.lean` | (S1) `piece_of_typed`, `law2`; (S1′) `relendOfTyped`, `law2_depth1` |
